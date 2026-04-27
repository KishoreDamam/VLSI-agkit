#!/usr/bin/env bash
# Wrapper for skill-creator's scripts.run_loop.
# Usage: run-skill-creator.sh <skill-name>
set -euo pipefail

if [ $# -ne 1 ]; then
  echo "Usage: $0 <skill-name>" >&2
  exit 2
fi

SKILL_NAME="$1"
REPO_ROOT="$(git rev-parse --show-toplevel)"
SKILL_PATH="$REPO_ROOT/.agent/skills/$SKILL_NAME"
EVAL_SET="$REPO_ROOT/.agent/skills/_evals/$SKILL_NAME/evals.json"
WORKSPACE="$REPO_ROOT/.agent/skills/${SKILL_NAME}-workspace"

# Locate skill-creator. Try common Claude plugin cache locations.
SKILL_CREATOR=""
for cand in \
    ${SKILL_CREATOR_PATH:-} \
    "$HOME/.claude/plugins/cache/claude-plugins-official/skill-creator/"*"/skills/skill-creator" \
    "$HOME/.claude/plugins/marketplaces/claude-plugins-official/plugins/skill-creator/skills/skill-creator" \
    "$HOME/.claude/plugins/cache/claude-plugins-official/superpowers/"*"/skills/skill-creator" \
    "$HOME/.claude/plugins/cache/claude-plugins-official/anthropic-skills/"*"/skills/skill-creator" \
    "$APPDATA/Claude/local-agent-mode-sessions/skills-plugin/"*"/"*"/skills/skill-creator" \
    "$LOCALAPPDATA/Claude/local-agent-mode-sessions/skills-plugin/"*"/"*"/skills/skill-creator" \
    ; do
  if [ -d "$cand" ]; then
    SKILL_CREATOR="$cand"
    break
  fi
done

if [ -z "$SKILL_CREATOR" ]; then
  echo "ERROR: skill-creator framework not found. Set SKILL_CREATOR_PATH env." >&2
  echo "  Looked in:" >&2
  echo "  - ~/.claude/plugins/cache/claude-plugins-official/superpowers/*/skills/skill-creator" >&2
  echo "  - APPDATA path on Windows" >&2
  exit 3
fi

if [ ! -f "$EVAL_SET" ]; then
  echo "ERROR: no evals.json for skill '$SKILL_NAME'." >&2
  echo "Expected: $EVAL_SET" >&2
  exit 4
fi

if [ ! -d "$SKILL_PATH" ]; then
  echo "ERROR: skill not found: $SKILL_PATH" >&2
  exit 5
fi

mkdir -p "$WORKSPACE"

# Default to Sonnet — good rubric signal at ~5x cheaper than Opus.
# Override with VLSI_EVAL_MODEL=claude-haiku-4-5 (cheaper, noisier) or
# VLSI_EVAL_MODEL=claude-opus-4-7 (most rigorous).
MODEL="${VLSI_EVAL_MODEL:-claude-sonnet-4-6}"

cd "$SKILL_CREATOR"
# Note: skill-creator's run_loop expects --results-dir (not --workspace).
# Drop $1 (the skill name we already consumed) before forwarding extras.
shift
python -m scripts.run_loop \
    --skill-path "$SKILL_PATH" \
    --eval-set "$EVAL_SET" \
    --model "$MODEL" \
    --results-dir "$WORKSPACE" \
    "$@"
