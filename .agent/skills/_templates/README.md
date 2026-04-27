# Skill templates

Use these as starting points when writing a new VLSI skill.

## Naming convention: `_`-prefix dirs are metadata

Any directory under `.agent/skills/` whose name starts with `_` (this one,
`_evals/`, fixture dirs) is **NOT a skill**. The root `Makefile` walker
and the skills index in `.agent/skills/README.md` skip them.

## Picking a template

| Skill type | Template | Examples |
|---|---|---|
| **Coding skill** — code constructs, idioms, anti-patterns | `coding-skill-template.md` | `fsm-design`, `fifo-design`, `axi-protocols` |
| **Flow skill** — numbered procedure, decision flowchart, validation gates | `flow-skill-template.md` | `clock-domain-crossing`, `synthesis-guidelines`, `simulation-flows` |

## Using a template

```bash
# Copy template into a new skill directory
cp -r .agent/skills/_templates/coding-skill-template.md \
      .agent/skills/<new-skill>/SKILL.md
mkdir -p .agent/skills/<new-skill>/{references,examples}
cp .agent/skills/_templates/example-Makefile.in \
   .agent/skills/<new-skill>/examples/Makefile
```

Then fill in the frontmatter, body, and at least one worked example.
