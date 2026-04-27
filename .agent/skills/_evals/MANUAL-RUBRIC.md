# Manual rubric review (no-API-spend baseline)

## Why this exists

The original Wave 0 plan (Task 12) called for running automated baseline evals via
the Anthropic API — either skill-creator's `run_loop.py` or our own
`run-quality-eval.py`. Both require API credits separate from Claude.ai chat
plans. For contributors without API budget, this document defines a free
alternative.

## Caveat

This process uses **same-model self-judging**: the assistant in your Claude
Code session reads the skill, drafts an answer, then grades itself. This is
weaker than independent automated evaluation. Treat scores as **directional**,
not absolute. If you ever do get API credits, re-run `run-quality-eval.py`
and record the delta.

## Process

For each Wave 1 skill, after the skill is written:

1. Open `.agent/skills/<skill-name>/SKILL.md` and any `references/` content.
2. Open `.agent/skills/_evals/<skill-name>/evals.json`.
3. For each `{prompt, expected_output}` pair:
   - **Without looking at `expected_output`**, draft what the skill would lead
     a competent VLSI engineer to answer. Use only the skill's content.
   - Reveal `expected_output`. Compare against the draft.
   - Score 0–10 using the rubric below.
   - Write a one-sentence rationale.
4. Append all results to `.agent/skills/_evals/<skill-name>/manual-baseline.md`
   (template below).

## Rubric

| Score | Meaning |
|-------|---------|
| 0–3   | Skill does not contain enough material to produce the rubric answer; engineer would still need to consult external docs. |
| 4–6   | Skill covers the topic but with gaps or imprecision; engineer would get partial credit and waste time on missing parts. |
| 7–8   | Skill produces a correct, useful answer with minor omissions. |
| 9–10  | Skill produces a complete answer with the nuance the rubric describes. |

## Template

`manual-baseline.md`:

```markdown
# Manual baseline: <skill-name>

- **Reviewer:** <session id or human name>
- **Date:** <YYYY-MM-DD>
- **Skill version:** <git SHA of SKILL.md>
- **Method:** Manual rubric (no API spend); same-model self-judging.

| ID | Score | Rationale |
|----|-------|-----------|
| 1  | 7/10  | Skill covered the FSM encoding tradeoffs but missed the safe-state default. |
| 2  | …     | … |

**Average:** X.X/10 (n=N)

## Notes

<Any patterns observed across prompts: gaps in skill coverage, places where
the skill went deeper than the rubric, etc.>
```

## When to upgrade to API runner

If you later add Anthropic API credits, switch to:

```bash
export ANTHROPIC_API_KEY=sk-ant-...
python .agent/skills/_evals/run-quality-eval.py <skill-name>
```

It writes results to `<skill>-workspace/iteration-1/benchmark.{json,md}`.
Compare those against the manual baseline to validate the manual scores
weren't biased.
