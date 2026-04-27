#!/usr/bin/env python3
"""Quality eval runner for VLSI skills.

For each {prompt, expected_output} pair in a skill's evals.json:
  1. Ask the model the prompt with the skill's SKILL.md content as system context.
  2. Ask a judge model to score the response 0-10 against expected_output.
  3. Aggregate scores, write benchmark.json + benchmark.md.

Unlike skill-creator's run_loop (which measures discoverability via
should_trigger), this measures answer quality against a rubric. Uses our
existing evals.json shape as-is — no reformatting required.

Usage:
  python run-quality-eval.py <skill-name> [--model claude-sonnet-4-6]

Env:
  ANTHROPIC_API_KEY  required
  VLSI_EVAL_MODEL    overrides --model default
"""
from __future__ import annotations

import argparse
import json
import os
import sys
import time
from datetime import datetime, timezone
from pathlib import Path

import anthropic

REPO_ROOT = Path(__file__).resolve().parents[3]
SKILLS_ROOT = REPO_ROOT / ".agent" / "skills"
EVALS_ROOT = SKILLS_ROOT / "_evals"

JUDGE_SYSTEM = """You are a strict technical judge for VLSI/RTL design skills.

Score the candidate answer 0-10 against the expected_output rubric:
  0-3  : Wrong, misleading, or missing core requirements.
  4-6  : Partially correct, but with gaps or errors that would cost an engineer time.
  7-8  : Correct and useful, with minor omissions.
  9-10 : Correct, complete, and includes the nuance the rubric describes.

Output STRICT JSON only:
{"score": <int 0-10>, "rationale": "<one sentence>"}

Do not include markdown fences. Do not include any other text."""


def load_skill(skill_name: str) -> tuple[str, str]:
    """Return (description, full_skill_md_content)."""
    skill_md = SKILLS_ROOT / skill_name / "SKILL.md"
    if not skill_md.is_file():
        sys.exit(f"ERROR: skill not found: {skill_md}")
    text = skill_md.read_text(encoding="utf-8")
    # Pull description from frontmatter if present (best-effort).
    desc = ""
    if text.startswith("---"):
        end = text.find("---", 3)
        if end > 0:
            for line in text[3:end].splitlines():
                if line.strip().startswith("description:"):
                    desc = line.split(":", 1)[1].strip().strip('"').strip("'")
                    break
    return desc, text


def load_evals(skill_name: str) -> list[dict]:
    path = EVALS_ROOT / skill_name / "evals.json"
    if not path.is_file():
        sys.exit(f"ERROR: evals not found: {path}")
    data = json.loads(path.read_text(encoding="utf-8"))
    evals = data.get("evals", [])
    if not evals:
        sys.exit(f"ERROR: evals.json has no 'evals' array: {path}")
    return evals


def call_candidate(client: anthropic.Anthropic, model: str, skill_md: str, prompt: str) -> str:
    """Ask the candidate model to answer the prompt with skill loaded as context."""
    system = (
        "You are an expert VLSI/RTL design assistant. The following skill content "
        "is loaded for your reference; apply its guidance directly when answering.\n\n"
        "===== SKILL CONTENT =====\n" + skill_md + "\n===== END SKILL ====="
    )
    resp = client.messages.create(
        model=model,
        max_tokens=2048,
        system=system,
        messages=[{"role": "user", "content": prompt}],
    )
    return "".join(block.text for block in resp.content if block.type == "text").strip()


def call_judge(
    client: anthropic.Anthropic,
    model: str,
    prompt: str,
    expected: str,
    actual: str,
) -> dict:
    user = (
        f"PROMPT:\n{prompt}\n\n"
        f"EXPECTED_OUTPUT (rubric):\n{expected}\n\n"
        f"CANDIDATE_ANSWER:\n{actual}\n\n"
        "Return JSON only."
    )
    resp = client.messages.create(
        model=model,
        max_tokens=512,
        system=JUDGE_SYSTEM,
        messages=[{"role": "user", "content": user}],
    )
    text = "".join(b.text for b in resp.content if b.type == "text").strip()
    # Strip markdown fences if the judge added them despite instructions.
    if text.startswith("```"):
        text = text.split("\n", 1)[1] if "\n" in text else text
        if text.endswith("```"):
            text = text.rsplit("```", 1)[0]
        text = text.strip()
    try:
        return json.loads(text)
    except json.JSONDecodeError:
        return {"score": 0, "rationale": f"judge returned non-JSON: {text[:200]}"}


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("skill", help="Skill name (subdir of .agent/skills/)")
    ap.add_argument(
        "--model",
        default=os.environ.get("VLSI_EVAL_MODEL", "claude-sonnet-4-6"),
        help="Model for both candidate and judge (default: claude-sonnet-4-6)",
    )
    ap.add_argument("--candidate-model", help="Override candidate model only")
    ap.add_argument("--judge-model", help="Override judge model only")
    args = ap.parse_args()

    if not os.environ.get("ANTHROPIC_API_KEY"):
        sys.exit("ERROR: ANTHROPIC_API_KEY not set")

    candidate_model = args.candidate_model or args.model
    judge_model = args.judge_model or args.model

    desc, skill_md = load_skill(args.skill)
    evals = load_evals(args.skill)
    client = anthropic.Anthropic()

    workspace = SKILLS_ROOT / f"{args.skill}-workspace"
    iter_dir = workspace / "iteration-1"
    iter_dir.mkdir(parents=True, exist_ok=True)
    transcripts_dir = workspace / "transcripts"
    transcripts_dir.mkdir(exist_ok=True)

    started = datetime.now(timezone.utc).isoformat()
    print(f"=== Quality eval: {args.skill} ===")
    print(f"Skill description: {desc}")
    print(f"Candidate model:   {candidate_model}")
    print(f"Judge model:       {judge_model}")
    print(f"Eval count:        {len(evals)}")
    print()

    results = []
    for ev in evals:
        eid = ev.get("id", "?")
        prompt = ev["prompt"]
        expected = ev["expected_output"]
        print(f"[{eid}] {prompt[:80]}...")
        t0 = time.time()
        try:
            actual = call_candidate(client, candidate_model, skill_md, prompt)
        except Exception as exc:
            print(f"  candidate error: {exc}")
            results.append({"id": eid, "score": 0, "error": f"candidate: {exc}"})
            continue
        try:
            verdict = call_judge(client, judge_model, prompt, expected, actual)
        except Exception as exc:
            print(f"  judge error: {exc}")
            results.append({"id": eid, "score": 0, "error": f"judge: {exc}"})
            continue
        elapsed = time.time() - t0
        score = int(verdict.get("score", 0))
        rationale = verdict.get("rationale", "")
        print(f"  score: {score}/10 ({elapsed:.1f}s) — {rationale}")
        results.append(
            {"id": eid, "prompt": prompt, "score": score, "rationale": rationale}
        )
        # Save full transcript for post-hoc inspection.
        (transcripts_dir / f"eval-{eid}.json").write_text(
            json.dumps(
                {
                    "id": eid,
                    "prompt": prompt,
                    "expected_output": expected,
                    "actual": actual,
                    "score": score,
                    "rationale": rationale,
                },
                indent=2,
            ),
            encoding="utf-8",
        )

    finished = datetime.now(timezone.utc).isoformat()
    scores = [r["score"] for r in results if "score" in r]
    avg = sum(scores) / len(scores) if scores else 0.0
    benchmark = {
        "skill": args.skill,
        "candidate_model": candidate_model,
        "judge_model": judge_model,
        "started": started,
        "finished": finished,
        "n_evals": len(evals),
        "average_score": round(avg, 2),
        "min_score": min(scores) if scores else 0,
        "max_score": max(scores) if scores else 0,
        "results": results,
    }
    (iter_dir / "benchmark.json").write_text(
        json.dumps(benchmark, indent=2), encoding="utf-8"
    )

    md = [
        f"# Baseline: {args.skill}",
        "",
        f"- **Candidate model:** {candidate_model}",
        f"- **Judge model:** {judge_model}",
        f"- **Started:** {started}",
        f"- **Finished:** {finished}",
        f"- **Average score:** **{avg:.2f}/10** (n={len(scores)})",
        f"- **Range:** {min(scores) if scores else 0}–{max(scores) if scores else 0}",
        "",
        "| ID | Score | Rationale |",
        "|----|-------|-----------|",
    ]
    for r in results:
        rid = r.get("id", "?")
        sc = r.get("score", 0)
        rat = r.get("rationale", r.get("error", "")).replace("|", "\\|")
        md.append(f"| {rid} | {sc}/10 | {rat} |")
    (iter_dir / "benchmark.md").write_text("\n".join(md) + "\n", encoding="utf-8")

    print()
    print(f"=== Average: {avg:.2f}/10 (n={len(scores)}) ===")
    print(f"Wrote {iter_dir / 'benchmark.md'}")


if __name__ == "__main__":
    main()
