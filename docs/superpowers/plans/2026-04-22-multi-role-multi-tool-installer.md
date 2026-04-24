# Multi-Role, Multi-Tool VLSI-KIT Installer — Implementation Plan

> **For agentic workers:** REQUIRED: Use superpowers:subagent-driven-development (if subagents available) or superpowers:executing-plans to implement this plan. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Extend `vlsi-agkit init` so users pick one of six role profiles and one-or-more target tools (Claude Code, Gemini, VS Code, Antigravity, Cursor, Windsurf), emitting per-tool layouts from a single canonical `.agent/` source via adapter modules.

**Architecture:** Thin CLI orchestrator (`bin/cli.js`) delegates to three subsystems: `profiles.js` (role registry + skill expansion from agent frontmatter), `prompts.js` (interactive UX via `@inquirer/prompts`, bypassed by flags), and `adapters/<tool>.js` modules (one per supported tool, each declaring `targetPaths` + `emit()`). Canonical `.agent/` stays untouched; adapters read it and transform per target. Tests use built-in `node:test` with fixture trees in `test/fixtures/`.

**Tech Stack:** Node.js ≥18, CommonJS modules, `@inquirer/prompts` for prompts, `node:test` for tests, `node:fs` / `node:path` for I/O. No bundler, no TypeScript.

**Spec reference:** `docs/superpowers/specs/2026-04-22-multi-role-multi-tool-installer-design.md`

---

## Chunk 1: Foundations (fs-util, profiles, package setup)

### Task 1: Bump Node engine and add dependency

**Files:**
- Modify: `package.json`

- [ ] **Step 1: Update package.json engines + deps**

Edit `package.json` — change the `engines.node` field and add `dependencies`:

```json
{
  "name": "@kishore-damam/vlsi-agkit",
  "version": "1.1.0",
  "description": "AI Agent Kit for VLSI (FPGA & ASIC) Development",
  "main": "index.js",
  "bin": {
    "vlsi-agkit": "./bin/cli.js"
  },
  "files": [
    "bin",
    ".agent",
    "CLAUDE.md",
    "README.md",
    "LICENSE"
  ],
  "scripts": {
    "test": "node --test test/"
  },
  "keywords": [
    "vlsi", "fpga", "asic", "rtl", "systemverilog",
    "ai", "agent", "gemini", "cursor", "claude", "windsurf"
  ],
  "author": "Kishore Damam",
  "license": "MIT",
  "repository": {
    "type": "git",
    "url": "https://github.com/kishore-damam/vlsi-kit"
  },
  "engines": {
    "node": ">=18.0.0"
  },
  "dependencies": {
    "@inquirer/prompts": "^7.0.0"
  }
}
```

Key changes vs current:
- `version` bumped to `1.1.0`
- `files` array now includes `CLAUDE.md` (the claude/vscode adapters read it)
- `scripts.test` now runs `node --test test/`
- `engines.node` ≥18
- new `dependencies.@inquirer/prompts`

- [ ] **Step 2: Install deps**

Run: `cd /d/Projects/agkit/vlsi-kit && npm install`
Expected: `@inquirer/prompts` and its deps installed; `package-lock.json` created.

- [ ] **Step 3: Commit**

```bash
cd /d/Projects/agkit/vlsi-kit
git init   # only if not already a repo
git add package.json package-lock.json
git commit -m "chore: bump to Node 18, add @inquirer/prompts"
```

---

### Task 2: `bin/fs-util.js` — shared helpers

**Files:**
- Create: `bin/fs-util.js`
- Create: `test/fs-util.test.js`

- [ ] **Step 1: Write the failing tests**

Create `test/fs-util.test.js`:

```js
const test = require('node:test');
const assert = require('node:assert');
const fs = require('node:fs');
const os = require('node:os');
const path = require('node:path');
const { readFrontmatter, pathExists, writeFile, copyDir } = require('../bin/fs-util');

function tmpFile(contents) {
  const p = path.join(fs.mkdtempSync(path.join(os.tmpdir(), 'fsu-')), 'f.md');
  fs.writeFileSync(p, contents);
  return p;
}

test('readFrontmatter parses flat scalars', () => {
  const p = tmpFile('---\nname: foo\ndescription: a thing\n---\n# Body\nhello');
  const { data, body } = readFrontmatter(p);
  assert.strictEqual(data.name, 'foo');
  assert.strictEqual(data.description, 'a thing');
  assert.strictEqual(body.trim(), '# Body\nhello');
});

test('readFrontmatter keeps scalars literal (commas not auto-split)', () => {
  // Real agent descriptions contain commas; the parser MUST NOT auto-split.
  // Callers decide whether a specific key is a list and split themselves.
  const p = tmpFile('---\nskills: a, b , c\ndescription: Expert in A, B, and C.\n---\nbody');
  const { data } = readFrontmatter(p);
  assert.strictEqual(data.skills, 'a, b , c');
  assert.strictEqual(data.description, 'Expert in A, B, and C.');
});

test('readFrontmatter returns empty data when no frontmatter', () => {
  const p = tmpFile('# Just a heading\nno fm');
  const { data, body } = readFrontmatter(p);
  assert.deepStrictEqual(data, {});
  assert.ok(body.includes('Just a heading'));
});

test('readFrontmatter throws on nested mapping', () => {
  const p = tmpFile('---\nnested:\n  key: v\n---\n');
  assert.throws(() => readFrontmatter(p), /not supported/i);
});

test('readFrontmatter throws on unclosed fence', () => {
  const p = tmpFile('---\nname: x\n# no closing fence');
  assert.throws(() => readFrontmatter(p), /unclosed/i);
});

test('pathExists returns true/false', () => {
  const d = fs.mkdtempSync(path.join(os.tmpdir(), 'pe-'));
  assert.strictEqual(pathExists(d), true);
  assert.strictEqual(pathExists(path.join(d, 'nope')), false);
});

test('writeFile creates parent dirs', () => {
  const d = fs.mkdtempSync(path.join(os.tmpdir(), 'wf-'));
  const target = path.join(d, 'a/b/c.txt');
  writeFile(target, 'hi');
  assert.strictEqual(fs.readFileSync(target, 'utf8'), 'hi');
});

test('copyDir recursively copies', () => {
  const src = fs.mkdtempSync(path.join(os.tmpdir(), 'cs-'));
  const dst = fs.mkdtempSync(path.join(os.tmpdir(), 'cd-'));
  fs.mkdirSync(path.join(src, 'sub'));
  fs.writeFileSync(path.join(src, 'a.txt'), 'A');
  fs.writeFileSync(path.join(src, 'sub/b.txt'), 'B');
  copyDir(src, path.join(dst, 'out'));
  assert.strictEqual(fs.readFileSync(path.join(dst, 'out/a.txt'), 'utf8'), 'A');
  assert.strictEqual(fs.readFileSync(path.join(dst, 'out/sub/b.txt'), 'utf8'), 'B');
});
```

- [ ] **Step 2: Run tests — expect failure**

Run: `npm test`
Expected: FAIL — `Cannot find module '../bin/fs-util'`

- [ ] **Step 3: Implement `bin/fs-util.js`**

Create `bin/fs-util.js`:

```js
const fs = require('node:fs');
const path = require('node:path');

function pathExists(p) {
  try { fs.accessSync(p); return true; } catch { return false; }
}

function writeFile(target, contents) {
  fs.mkdirSync(path.dirname(target), { recursive: true });
  fs.writeFileSync(target, contents);
}

function copyFile(src, dst) {
  fs.mkdirSync(path.dirname(dst), { recursive: true });
  fs.copyFileSync(src, dst);
}

function copyDir(src, dst) {
  fs.mkdirSync(dst, { recursive: true });
  for (const entry of fs.readdirSync(src, { withFileTypes: true })) {
    const s = path.join(src, entry.name);
    const d = path.join(dst, entry.name);
    if (entry.isDirectory()) copyDir(s, d);
    else fs.copyFileSync(s, d);
  }
}

// Minimal frontmatter parser. Supports:
//   flat scalars: `key: value` — value kept as literal string (NOT split on commas)
// Callers that want a list-valued key (e.g., `skills`) must split the string
// themselves. This is intentional: agent `description:` fields contain commas
// as ordinary prose.
// Throws on nested mappings, block scalars, unclosed fences.
function readFrontmatter(filePath) {
  const raw = fs.readFileSync(filePath, 'utf8');
  const lines = raw.split(/\r?\n/);
  if (lines[0] !== '---') return { data: {}, body: raw };

  let end = -1;
  for (let i = 1; i < lines.length; i++) {
    if (lines[i] === '---') { end = i; break; }
  }
  if (end === -1) {
    throw new Error(`readFrontmatter: unclosed --- fence in ${filePath}`);
  }

  const data = {};
  for (let i = 1; i < end; i++) {
    const line = lines[i];
    if (line.trim() === '') continue;
    const m = line.match(/^([A-Za-z0-9_-]+):\s*(.*)$/);
    if (!m) {
      throw new Error(`readFrontmatter: not supported (unparseable line "${line}") in ${filePath}`);
    }
    const key = m[1];
    const rhs = m[2].trim();
    if (rhs === '') {
      // "key:" with value on subsequent indented lines = nested mapping / block scalar
      const next = lines[i + 1] || '';
      if (/^\s+\S/.test(next)) {
        throw new Error(`readFrontmatter: nested structures not supported (key "${key}") in ${filePath}`);
      }
      data[key] = '';
      continue;
    }
    data[key] = rhs;
  }

  const body = lines.slice(end + 1).join('\n');
  return { data, body };
}

module.exports = { pathExists, writeFile, copyFile, copyDir, readFrontmatter };
```

- [ ] **Step 4: Run tests — expect pass**

Run: `npm test`
Expected: PASS — all 8 tests green.

- [ ] **Step 5: Commit**

```bash
git add bin/fs-util.js test/fs-util.test.js
git commit -m "feat(fs-util): add shared fs helpers with minimal frontmatter parser"
```

---

### Task 3: `bin/profiles.js` — role registry + resolver

**Files:**
- Create: `bin/profiles.js`
- Create: `test/profiles.test.js`
- Create: `test/fixtures/agents-sample/rtl-designer.md`
- Create: `test/fixtures/agents-sample/timing-analyst.md`
- Create: `test/fixtures/agents-sample/debugger.md`
- Create: `test/fixtures/agents-sample/no-skills-agent.md`

- [ ] **Step 1: Create fixture agent files**

Create `test/fixtures/agents-sample/rtl-designer.md`:
```markdown
---
name: rtl-designer
description: RTL design expert.
skills: clean-rtl, systemverilog-patterns, fsm-design
---
# Body
```

Create `test/fixtures/agents-sample/timing-analyst.md`:
```markdown
---
name: timing-analyst
description: STA expert.
skills: timing-constraints, clock-domain-crossing, clean-rtl
---
# Body
```

Create `test/fixtures/agents-sample/debugger.md`:
```markdown
---
name: debugger
description: Waveform debugging.
skills: waveform-debugging
---
# Body
```

Create `test/fixtures/agents-sample/no-skills-agent.md`:
```markdown
---
name: no-skills-agent
description: No skills declared.
---
# Body
```

- [ ] **Step 2: Write the failing tests**

Create `test/profiles.test.js`:

```js
const test = require('node:test');
const assert = require('node:assert');
const path = require('node:path');
const { list, resolve, VALID_IDS } = require('../bin/profiles');

const FIXTURE = path.join(__dirname, 'fixtures/agents-sample');

test('list returns all six profile ids', () => {
  const ids = list().map(p => p.id);
  assert.deepStrictEqual(ids.sort(), [
    'asic-engineer', 'fpga-engineer', 'full-stack',
    'physical-design', 'rtl-designer', 'verification-engineer'
  ]);
});

test('VALID_IDS mirrors list', () => {
  assert.deepStrictEqual([...VALID_IDS].sort(), list().map(p => p.id).sort());
});

test('resolve unknown id throws with valid list', () => {
  assert.throws(() => resolve('nope', FIXTURE), /nope.*full-stack/s);
});

test('resolve full-stack returns sentinel (no filtering)', () => {
  const p = resolve('full-stack', FIXTURE);
  assert.strictEqual(p.id, 'full-stack');
  assert.strictEqual(p.isFullStack, true);
});

test('resolve expands and deduplicates skills from agent frontmatter', () => {
  // Use a test-only profile helper: pass explicit agents via _testOverride
  const p = resolve('rtl-designer', FIXTURE);
  // rtl-designer profile includes: rtl-designer + alwaysInclude (orchestrator, project-planner)
  // Only rtl-designer exists in fixture, so skills come from it:
  assert.ok(p.skills.includes('clean-rtl'));
  assert.ok(p.skills.includes('fsm-design'));
  // Deduped — no duplicates
  assert.strictEqual(p.skills.length, new Set(p.skills).size);
});

test('resolve includes alwaysInclude agents', () => {
  const p = resolve('rtl-designer', FIXTURE);
  assert.ok(p.agents.includes('orchestrator'));
  assert.ok(p.agents.includes('project-planner'));
  assert.ok(p.agents.includes('rtl-designer'));
});

test('resolve warns when an agent file is missing, does not crash', () => {
  // asic-engineer references asic-specialist which is NOT in fixture
  // should still resolve, emit a warning, just not expand that agent's skills
  const warnings = [];
  const orig = console.warn;
  console.warn = (m) => warnings.push(m);
  try {
    const p = resolve('asic-engineer', FIXTURE);
    assert.ok(Array.isArray(p.agents));
    assert.ok(warnings.some(w => /asic-specialist/.test(w)));
  } finally { console.warn = orig; }
});

test('agent with empty skills frontmatter is tolerated', () => {
  // Direct skill expansion via internal helper — test through a fresh resolver call
  // Simulate: a profile referencing no-skills-agent would resolve without error.
  // We test this indirectly by asserting resolve doesn't throw on that file:
  const { _expandSkills } = require('../bin/profiles');
  const result = _expandSkills(['no-skills-agent'], FIXTURE);
  assert.deepStrictEqual(result, []);
});
```

- [ ] **Step 3: Run tests — expect failure**

Run: `npm test`
Expected: FAIL — `Cannot find module '../bin/profiles'`

- [ ] **Step 4: Implement `bin/profiles.js`**

Create `bin/profiles.js`:

```js
const fs = require('node:fs');
const path = require('node:path');
const { readFrontmatter } = require('./fs-util');

const ALWAYS_INCLUDE = ['orchestrator', 'project-planner'];

const PROFILES = [
  {
    id: 'full-stack',
    name: 'Full Stack',
    description: 'All 14 VLSI specialist agents — the original behavior',
    agents: [
      'orchestrator', 'rtl-designer', 'verification-engineer',
      'synthesis-engineer', 'timing-analyst', 'fpga-specialist',
      'asic-specialist', 'physical-design-engineer', 'debugger',
      'lint-reviewer', 'documentation-writer', 'project-planner',
      'ip-integrator', 'power-analyst'
    ],
    workflows: [
      'brainstorm', 'plan', 'design', 'verify', 'synthesize',
      'debug', 'lint', 'timing', 'review', 'integrate'
    ],
    alwaysInclude: [],   // full-stack already has everything
    extraSkills: [],
    isFullStack: true
  },
  {
    id: 'fpga-engineer',
    name: 'FPGA Engineer',
    description: 'FPGA design, Vivado/Quartus flows, timing closure',
    agents: ['fpga-specialist', 'rtl-designer', 'timing-analyst',
             'ip-integrator', 'debugger', 'lint-reviewer'],
    workflows: ['design', 'debug', 'lint', 'timing', 'integrate'],
    alwaysInclude: ALWAYS_INCLUDE,
    extraSkills: []
  },
  {
    id: 'asic-engineer',
    name: 'ASIC Engineer',
    description: 'ASIC flows, DFT, tapeout',
    agents: ['asic-specialist', 'rtl-designer', 'physical-design-engineer',
             'timing-analyst', 'power-analyst', 'debugger', 'lint-reviewer'],
    workflows: ['design', 'synthesize', 'timing', 'lint', 'review'],
    alwaysInclude: ALWAYS_INCLUDE,
    extraSkills: []
  },
  {
    id: 'verification-engineer',
    name: 'Verification Engineer',
    description: 'UVM, formal, coverage',
    agents: ['verification-engineer', 'debugger', 'lint-reviewer',
             'documentation-writer'],
    workflows: ['verify', 'debug', 'review'],
    alwaysInclude: ALWAYS_INCLUDE,
    extraSkills: []
  },
  {
    id: 'rtl-designer',
    name: 'RTL Designer',
    description: 'Core RTL design focus',
    agents: ['rtl-designer', 'lint-reviewer', 'documentation-writer'],
    workflows: ['design', 'lint', 'review'],
    alwaysInclude: ALWAYS_INCLUDE,
    extraSkills: []
  },
  {
    id: 'physical-design',
    name: 'Physical Design',
    description: 'P&R, floorplanning, power',
    agents: ['physical-design-engineer', 'timing-analyst',
             'power-analyst', 'asic-specialist'],
    workflows: ['synthesize', 'timing', 'review'],
    alwaysInclude: ALWAYS_INCLUDE,
    extraSkills: []
  }
];

const BY_ID = Object.fromEntries(PROFILES.map(p => [p.id, p]));
const VALID_IDS = new Set(PROFILES.map(p => p.id));

function list() { return PROFILES.slice(); }

function _expandSkills(agentIds, agentsDir) {
  const skills = new Set();
  for (const id of agentIds) {
    const file = path.join(agentsDir, `${id}.md`);
    if (!fs.existsSync(file)) {
      console.warn(`[profiles] warning: agent file missing: ${file}`);
      continue;
    }
    const { data } = readFrontmatter(file);
    const decl = data.skills;
    if (!decl) continue;
    // `skills` is a comma-separated string in agent frontmatter;
    // split here (parser intentionally keeps it literal — see fs-util.js).
    const items = decl.split(',').map(s => s.trim()).filter(Boolean);
    for (const s of items) skills.add(s);
  }
  return [...skills];
}

function resolve(id, agentsDir) {
  const profile = BY_ID[id];
  if (!profile) {
    const valid = [...VALID_IDS].join(', ');
    throw new Error(`Unknown role profile "${id}". Valid ids: ${valid}`);
  }
  const agents = [...new Set([...profile.agents, ...profile.alwaysInclude])];
  const skills = [...new Set([
    ..._expandSkills(agents, agentsDir),
    ...profile.extraSkills
  ])];
  return {
    id: profile.id,
    name: profile.name,
    description: profile.description,
    agents,
    skills,
    workflows: profile.workflows.slice(),
    isFullStack: !!profile.isFullStack
  };
}

module.exports = { list, resolve, VALID_IDS, _expandSkills };
```

- [ ] **Step 5: Run tests — expect pass**

Run: `npm test`
Expected: PASS — all profile tests + fs-util tests green.

- [ ] **Step 6: Commit**

```bash
git add bin/profiles.js test/profiles.test.js test/fixtures/agents-sample/
git commit -m "feat(profiles): add role profile registry + skill expansion"
```

---

## Chunk 2: Adapters (shared globs map + six tool adapters)

### Task 4: `bin/adapters/globs.js` — shared agent-to-globs map

**Files:**
- Create: `bin/adapters/globs.js`
- Create: `test/adapters-globs.test.js`

- [ ] **Step 1: Write failing tests**

Create `test/adapters-globs.test.js`:

```js
const test = require('node:test');
const assert = require('node:assert');
const { globsFor, isAlwaysApply } = require('../bin/adapters/globs');

test('rtl-designer maps to HDL globs', () => {
  assert.deepStrictEqual(globsFor('rtl-designer'), ['**/*.{sv,svh,v,vh,vhd,vhdl}']);
});

test('timing-analyst maps to constraint globs', () => {
  assert.deepStrictEqual(globsFor('timing-analyst'), ['**/*.{sdc,xdc,tcl}']);
});

test('debugger is alwaysApply', () => {
  assert.strictEqual(isAlwaysApply('debugger'), true);
  assert.strictEqual(globsFor('debugger'), null);
});

test('unknown agent is alwaysApply by default (safe fallback)', () => {
  assert.strictEqual(isAlwaysApply('made-up-agent'), true);
});
```

- [ ] **Step 2: Run tests — expect FAIL**

Run: `npm test`
Expected: FAIL — `Cannot find module '../bin/adapters/globs'`

- [ ] **Step 3: Implement `bin/adapters/globs.js`**

Create `bin/adapters/globs.js`:

```js
// Agent -> Cursor/Windsurf glob map. Agents not in the map default to alwaysApply.
const GLOBS = {
  'rtl-designer':       ['**/*.{sv,svh,v,vh,vhd,vhdl}'],
  'ip-integrator':      ['**/*.{sv,svh,v,vh,vhd,vhdl}'],
  'verification-engineer': ['**/{tb,test,tests,sim}/**/*.{sv,svh,v}', '**/*_tb.{sv,v}'],
  'synthesis-engineer': ['**/*.{tcl,sdc}', '**/synth/**'],
  'timing-analyst':     ['**/*.{sdc,xdc,tcl}'],
  'fpga-specialist':    ['**/*.{xdc,qsf,xpr}', '**/fpga/**'],
  'asic-specialist':    ['**/*.{lef,def,lib,sdc}', '**/pnr/**', '**/synth/**'],
  'physical-design-engineer': ['**/*.{lef,def,lib,sdc}', '**/pnr/**', '**/synth/**'],
  'power-analyst':      ['**/*.upf', '**/power/**']
};

function globsFor(agentId) { return GLOBS[agentId] ?? null; }
function isAlwaysApply(agentId) { return !(agentId in GLOBS); }

module.exports = { globsFor, isAlwaysApply };
```

- [ ] **Step 4: Run tests — expect PASS**

Run: `npm test`
Expected: PASS

- [ ] **Step 5: Commit**

```bash
git add bin/adapters/globs.js test/adapters-globs.test.js
git commit -m "feat(adapters): add shared agent-to-globs map"
```

---

### Task 5: Adapter fixture tree + `bin/adapters/index.js` registry

**Files:**
- Create: `test/fixtures/canonical/.agent/agents/rtl-designer.md`
- Create: `test/fixtures/canonical/.agent/agents/debugger.md`
- Create: `test/fixtures/canonical/.agent/skills/clean-rtl/SKILL.md`
- Create: `test/fixtures/canonical/.agent/skills/waveform-debugging/SKILL.md`
- Create: `test/fixtures/canonical/.agent/workflows/design.md`
- Create: `test/fixtures/canonical/.agent/workflows/debug.md`
- Create: `test/fixtures/canonical/.agent/rules/GEMINI.md`
- Create: `test/fixtures/canonical/.agent/ARCHITECTURE.md`
- Create: `test/fixtures/canonical/CLAUDE.md`
- Create: `bin/adapters/index.js`
- Create: `test/adapters-index.test.js`

- [ ] **Step 1: Build the canonical fixture tree**

Create `test/fixtures/canonical/.agent/agents/rtl-designer.md`:
```markdown
---
name: rtl-designer
description: RTL design expert.
skills: clean-rtl
---
# RTL Designer body
```

Create `test/fixtures/canonical/.agent/agents/debugger.md`:
```markdown
---
name: debugger
description: Waveform debugging.
skills: waveform-debugging
---
# Debugger body
```

Create `test/fixtures/canonical/.agent/skills/clean-rtl/SKILL.md`:
```markdown
# Clean RTL
Rules here.
```

Create `test/fixtures/canonical/.agent/skills/waveform-debugging/SKILL.md`:
```markdown
# Waveform Debugging
Rules here.
```

Create `test/fixtures/canonical/.agent/workflows/design.md`:
```markdown
# /design
Design workflow.
```

Create `test/fixtures/canonical/.agent/workflows/debug.md`:
```markdown
# /debug
Debug workflow.
```

Create `test/fixtures/canonical/.agent/rules/GEMINI.md`:
```markdown
# Gemini Rules
Base rules.
```

Create `test/fixtures/canonical/.agent/ARCHITECTURE.md`:
```markdown
# Architecture
Overview.
```

Create `test/fixtures/canonical/CLAUDE.md`:
```markdown
# VLSI Agent Kit - Claude Code Configuration

Some intro text.

## Agent Routing

| Domain | Agent File | Trigger Keywords |
|---|---|---|
| RTL Design | `rtl-designer.md` | module, design |
| Debug | `debugger.md` | debug, waveform |
| Physical Design | `physical-design-engineer.md` | pnr |

Other content.

## Available Slash Commands

| Command | Description |
|---|---|
| `/design` | RTL design |
| `/debug` | Debug |

End of file.
```

- [ ] **Step 2: Write failing test for adapter registry**

Create `test/adapters-index.test.js`:

```js
const test = require('node:test');
const assert = require('node:assert');
const adapters = require('../bin/adapters');

test('registry exposes all six adapter ids', () => {
  const ids = adapters.list().map(a => a.id).sort();
  assert.deepStrictEqual(ids, [
    'antigravity', 'claude', 'cursor', 'gemini', 'vscode', 'windsurf'
  ]);
});

test('get(id) returns adapter', () => {
  assert.strictEqual(adapters.get('cursor').id, 'cursor');
});

test('get(unknown) throws with valid list', () => {
  assert.throws(() => adapters.get('nope'), /nope.*claude/s);
});

test('every adapter declares id, name, targetPaths, emit', () => {
  for (const a of adapters.list()) {
    assert.ok(a.id, `${a.id} has no id`);
    assert.ok(a.name, `${a.id} has no name`);
    assert.ok(Array.isArray(a.targetPaths), `${a.id} targetPaths not array`);
    assert.strictEqual(typeof a.emit, 'function', `${a.id} emit not function`);
  }
});
```

- [ ] **Step 3: Run — expect FAIL**

Run: `npm test`
Expected: FAIL — `Cannot find module '../bin/adapters'`

- [ ] **Step 4: Create stub adapters + registry**

Create `bin/adapters/index.js`:

```js
const claude = require('./claude');
const gemini = require('./gemini');
const vscode = require('./vscode');
const antigravity = require('./antigravity');
const cursor = require('./cursor');
const windsurf = require('./windsurf');

const ALL = [claude, gemini, vscode, antigravity, cursor, windsurf];
const BY_ID = Object.fromEntries(ALL.map(a => [a.id, a]));
const VALID_IDS = new Set(ALL.map(a => a.id));

function list() { return ALL.slice(); }
function get(id) {
  if (!BY_ID[id]) {
    throw new Error(`Unknown tool "${id}". Valid: ${[...VALID_IDS].join(', ')}`);
  }
  return BY_ID[id];
}
module.exports = { list, get, VALID_IDS };
```

Create stubs for all six adapters with only the shape; real `emit` comes in later tasks. Example — `bin/adapters/cursor.js`:

```js
module.exports = {
  id: 'cursor',
  name: 'Cursor',
  targetPaths: ['.cursor/'],
  emit() { throw new Error('not implemented'); }
};
```

Do the same for:
- `bin/adapters/claude.js` → `targetPaths: ['.claude/', 'CLAUDE.md']`
- `bin/adapters/gemini.js` → `targetPaths: ['GEMINI.md']`
- `bin/adapters/vscode.js` → `targetPaths: ['.github/copilot-instructions.md']`
- `bin/adapters/antigravity.js` → `targetPaths: ['.agent/']`
- `bin/adapters/windsurf.js` → `targetPaths: ['.windsurf/']`

Each stub file should be ~5 lines, identical shape with different `id`/`name`/`targetPaths`.

- [ ] **Step 5: Run — expect PASS**

Run: `npm test`
Expected: PASS — registry tests green. (The stubs' `emit` throws, but no test calls it yet.)

- [ ] **Step 6: Commit**

```bash
git add bin/adapters/ test/adapters-index.test.js test/fixtures/canonical/
git commit -m "feat(adapters): scaffold adapter registry + stubs"
```

---

### Task 6: Antigravity adapter (simplest — migrates current behavior)

**Files:**
- Modify: `bin/adapters/antigravity.js`
- Create: `test/adapters-antigravity.test.js`

- [ ] **Step 1: Write failing test**

Create `test/adapters-antigravity.test.js`:

```js
const test = require('node:test');
const assert = require('node:assert');
const fs = require('node:fs');
const os = require('node:os');
const path = require('node:path');
const adapter = require('../bin/adapters/antigravity');
const { resolve } = require('../bin/profiles');

const SRC = path.join(__dirname, 'fixtures/canonical');

function mkTmp() {
  return fs.mkdtempSync(path.join(os.tmpdir(), 'ag-'));
}

test('antigravity full-stack copies entire .agent/ tree', () => {
  const out = mkTmp();
  const profile = resolve('full-stack', path.join(SRC, '.agent/agents'));
  adapter.emit({ profile, sourceDir: SRC, targetDir: out, log: () => {}, force: false });
  assert.ok(fs.existsSync(path.join(out, '.agent/agents/rtl-designer.md')));
  assert.ok(fs.existsSync(path.join(out, '.agent/agents/debugger.md')));
  assert.ok(fs.existsSync(path.join(out, '.agent/skills/clean-rtl/SKILL.md')));
  assert.ok(fs.existsSync(path.join(out, '.agent/workflows/design.md')));
  assert.ok(fs.existsSync(path.join(out, '.agent/ARCHITECTURE.md')));
});

test('antigravity rtl-designer profile filters agents, skills, workflows', () => {
  const out = mkTmp();
  const profile = resolve('rtl-designer', path.join(SRC, '.agent/agents'));
  // profile has: rtl-designer + alwaysInclude(orchestrator, project-planner)
  // fixture only has rtl-designer + debugger
  adapter.emit({ profile, sourceDir: SRC, targetDir: out, log: () => {}, force: false });
  assert.ok(fs.existsSync(path.join(out, '.agent/agents/rtl-designer.md')));
  assert.ok(!fs.existsSync(path.join(out, '.agent/agents/debugger.md')),
    'debugger not in rtl-designer profile');
  assert.ok(fs.existsSync(path.join(out, '.agent/skills/clean-rtl/SKILL.md')));
  assert.ok(!fs.existsSync(path.join(out, '.agent/skills/waveform-debugging/SKILL.md')),
    'waveform-debugging skill should not ship with rtl-designer profile');
  // ARCHITECTURE.md always copied
  assert.ok(fs.existsSync(path.join(out, '.agent/ARCHITECTURE.md')));
});
```

- [ ] **Step 2: Run — expect FAIL**

Run: `npm test`
Expected: FAIL — `not implemented`.

- [ ] **Step 3: Implement `bin/adapters/antigravity.js`**

Replace contents:

```js
const fs = require('node:fs');
const path = require('node:path');
const { copyFile, writeFile, pathExists, copyDir } = require('../fs-util');

function emit({ profile, sourceDir, targetDir, log = () => {} }) {
  const srcAgent = path.join(sourceDir, '.agent');
  const dstAgent = path.join(targetDir, '.agent');

  if (profile.isFullStack) {
    copyDir(srcAgent, dstAgent);
    log(`  .agent/ (full tree)`);
    return;
  }

  // Always-copy top-level files
  fs.mkdirSync(dstAgent, { recursive: true });
  for (const name of fs.readdirSync(srcAgent, { withFileTypes: true })) {
    if (name.isFile()) {
      copyFile(path.join(srcAgent, name.name), path.join(dstAgent, name.name));
    }
  }

  // Filtered agents
  const agentsSrc = path.join(srcAgent, 'agents');
  if (pathExists(agentsSrc)) {
    for (const id of profile.agents) {
      const f = path.join(agentsSrc, `${id}.md`);
      if (pathExists(f)) copyFile(f, path.join(dstAgent, 'agents', `${id}.md`));
    }
    log(`  .agent/agents/ (${profile.agents.length} filtered)`);
  }

  // Filtered skills (each skill is a directory)
  const skillsSrc = path.join(srcAgent, 'skills');
  if (pathExists(skillsSrc)) {
    for (const id of profile.skills) {
      const d = path.join(skillsSrc, id);
      if (pathExists(d)) copyDir(d, path.join(dstAgent, 'skills', id));
    }
    log(`  .agent/skills/ (${profile.skills.length} filtered)`);
  }

  // Filtered workflows
  const wfSrc = path.join(srcAgent, 'workflows');
  if (pathExists(wfSrc)) {
    for (const id of profile.workflows) {
      const f = path.join(wfSrc, `${id}.md`);
      if (pathExists(f)) copyFile(f, path.join(dstAgent, 'workflows', `${id}.md`));
    }
    log(`  .agent/workflows/ (${profile.workflows.length} filtered)`);
  }

  // Rules: copy whole dir (rules are universal)
  const rulesSrc = path.join(srcAgent, 'rules');
  if (pathExists(rulesSrc)) copyDir(rulesSrc, path.join(dstAgent, 'rules'));
}

module.exports = {
  id: 'antigravity',
  name: 'Antigravity',
  targetPaths: ['.agent/'],
  emit
};
```

- [ ] **Step 4: Run — expect PASS**

Run: `npm test`
Expected: PASS

- [ ] **Step 5: Commit**

```bash
git add bin/adapters/antigravity.js test/adapters-antigravity.test.js
git commit -m "feat(adapters): implement antigravity emitter (migrates current behavior)"
```

---

### Task 7: Gemini adapter

**Files:**
- Modify: `bin/adapters/gemini.js`
- Create: `test/adapters-gemini.test.js`

- [ ] **Step 1: Write failing test**

Create `test/adapters-gemini.test.js`:

```js
const test = require('node:test');
const assert = require('node:assert');
const fs = require('node:fs');
const os = require('node:os');
const path = require('node:path');
const adapter = require('../bin/adapters/gemini');
const { resolve } = require('../bin/profiles');

const SRC = path.join(__dirname, 'fixtures/canonical');

test('gemini copies GEMINI.md to target root', () => {
  const out = fs.mkdtempSync(path.join(os.tmpdir(), 'gem-'));
  const profile = resolve('full-stack', path.join(SRC, '.agent/agents'));
  adapter.emit({ profile, sourceDir: SRC, targetDir: out, log: () => {}, force: false });
  const contents = fs.readFileSync(path.join(out, 'GEMINI.md'), 'utf8');
  assert.ok(contents.includes('# Gemini Rules'));
});

test('gemini appends profile summary when not full-stack', () => {
  const out = fs.mkdtempSync(path.join(os.tmpdir(), 'gem-'));
  const profile = resolve('rtl-designer', path.join(SRC, '.agent/agents'));
  adapter.emit({ profile, sourceDir: SRC, targetDir: out, log: () => {}, force: false });
  const contents = fs.readFileSync(path.join(out, 'GEMINI.md'), 'utf8');
  assert.ok(contents.includes('RTL Designer'), 'profile name appended');
  assert.ok(contents.includes('rtl-designer'), 'agent id in summary');
});
```

- [ ] **Step 2: Run — expect FAIL**

Run: `npm test`
Expected: FAIL

- [ ] **Step 3: Implement `bin/adapters/gemini.js`**

```js
const fs = require('node:fs');
const path = require('node:path');
const { writeFile, pathExists } = require('../fs-util');

function emit({ profile, sourceDir, targetDir, log = () => {} }) {
  const src = path.join(sourceDir, '.agent/rules/GEMINI.md');
  if (!pathExists(src)) {
    throw new Error(`gemini adapter: canonical rules missing at ${src}`);
  }
  let contents = fs.readFileSync(src, 'utf8');

  if (!profile.isFullStack) {
    const summary = [
      '',
      '---',
      '',
      `## Active Profile: ${profile.name}`,
      '',
      profile.description,
      '',
      `**Agents (${profile.agents.length}):** ${profile.agents.join(', ')}`,
      '',
      `**Workflows (${profile.workflows.length}):** ${profile.workflows.map(w => '/' + w).join(', ')}`,
      ''
    ].join('\n');
    contents = contents + summary;
  }

  const dst = path.join(targetDir, 'GEMINI.md');
  writeFile(dst, contents);
  log(`  GEMINI.md`);
}

module.exports = {
  id: 'gemini',
  name: 'Gemini CLI',
  targetPaths: ['GEMINI.md'],
  emit
};
```

- [ ] **Step 4: Run — expect PASS**

Run: `npm test`
Expected: PASS

- [ ] **Step 5: Commit**

```bash
git add bin/adapters/gemini.js test/adapters-gemini.test.js
git commit -m "feat(adapters): implement gemini emitter"
```

---

### Task 8: Claude adapter (agents + commands + filtered CLAUDE.md)

**Files:**
- Modify: `bin/adapters/claude.js`
- Create: `bin/adapters/claude-md-filter.js`
- Create: `test/adapters-claude.test.js`
- Create: `test/claude-md-filter.test.js`

- [ ] **Step 1: Test the CLAUDE.md table filter in isolation**

Create `test/claude-md-filter.test.js`:

```js
const test = require('node:test');
const assert = require('node:assert');
const { filterAgentRoutingTable, stripSlashCommandsSection } = require('../bin/adapters/claude-md-filter');

const SAMPLE = `# Title

## Agent Routing

| Domain | Agent File | Trigger Keywords |
|---|---|---|
| RTL Design | \`rtl-designer.md\` | module |
| Debug | \`debugger.md\` | debug |
| Physical Design | \`physical-design-engineer.md\` | pnr |

## Other

stuff

## Available Slash Commands

| Command | Description |
|---|---|
| \`/design\` | RTL |

## Footer

End.
`;

test('filterAgentRoutingTable keeps only matching rows', () => {
  const out = filterAgentRoutingTable(SAMPLE, new Set(['rtl-designer', 'debugger']));
  assert.ok(out.includes('rtl-designer.md'));
  assert.ok(out.includes('debugger.md'));
  assert.ok(!out.includes('physical-design-engineer.md'),
    'non-matching row removed');
  // Header rows preserved
  assert.ok(out.includes('| Domain | Agent File | Trigger Keywords |'));
});

test('filterAgentRoutingTable with full set keeps all rows', () => {
  const all = new Set(['rtl-designer', 'debugger', 'physical-design-engineer']);
  const out = filterAgentRoutingTable(SAMPLE, all);
  assert.ok(out.includes('rtl-designer.md'));
  assert.ok(out.includes('physical-design-engineer.md'));
});

test('stripSlashCommandsSection removes the whole section', () => {
  const out = stripSlashCommandsSection(SAMPLE);
  assert.ok(!out.includes('Available Slash Commands'));
  assert.ok(!out.includes('/design'));
  // Preceding section retained
  assert.ok(out.includes('## Other'));
  // Trailing content after the stripped section also retained
  assert.ok(out.includes('End.'));
});
```

- [ ] **Step 2: Run — expect FAIL**

Run: `npm test`
Expected: FAIL

- [ ] **Step 3: Implement `bin/adapters/claude-md-filter.js`**

```js
function filterAgentRoutingTable(md, keepSet) {
  // Find the "## Agent Routing" section and filter its table rows.
  const lines = md.split(/\r?\n/);
  const out = [];
  let inRouting = false;
  let sawTableHeader = false;
  let pastTable = false;

  for (let i = 0; i < lines.length; i++) {
    const line = lines[i];
    if (/^##\s+Agent Routing\s*$/.test(line)) {
      inRouting = true; sawTableHeader = false; pastTable = false;
      out.push(line);
      continue;
    }
    if (inRouting && /^##\s+/.test(line)) {
      inRouting = false; pastTable = true;
      out.push(line);
      continue;
    }
    if (inRouting && /^\|/.test(line)) {
      if (!sawTableHeader) {
        out.push(line);
        // Next line is expected separator ("|---|---|..."); keep it too.
        sawTableHeader = line.includes('---') ? sawTableHeader : true;
        continue;
      }
      if (/^\|\s*-+/.test(line)) { out.push(line); continue; } // separator
      // Data row — keep only if references a kept agent
      const m = line.match(/`([a-z-]+)\.md`/);
      if (m && keepSet.has(m[1])) out.push(line);
      continue;
    }
    out.push(line);
  }
  return out.join('\n');
}

function stripSlashCommandsSection(md) {
  const lines = md.split(/\r?\n/);
  const out = [];
  let inSection = false;
  for (let i = 0; i < lines.length; i++) {
    const line = lines[i];
    if (/^##\s+Available Slash Commands\s*$/.test(line)) { inSection = true; continue; }
    if (inSection && /^##\s+/.test(line)) { inSection = false; /* fall through to push */ }
    if (!inSection) out.push(line);
  }
  return out.join('\n');
}

module.exports = { filterAgentRoutingTable, stripSlashCommandsSection };
```

- [ ] **Step 4: Run filter tests — expect PASS**

Run: `npm test`
Expected: PASS (filter tests).

- [ ] **Step 5: Write failing claude adapter tests**

Create `test/adapters-claude.test.js`:

```js
const test = require('node:test');
const assert = require('node:assert');
const fs = require('node:fs');
const os = require('node:os');
const path = require('node:path');
const adapter = require('../bin/adapters/claude');
const { resolve } = require('../bin/profiles');

const SRC = path.join(__dirname, 'fixtures/canonical');

test('claude emits filtered agents, commands, CLAUDE.md', () => {
  const out = fs.mkdtempSync(path.join(os.tmpdir(), 'cl-'));
  const profile = resolve('rtl-designer', path.join(SRC, '.agent/agents'));
  adapter.emit({ profile, sourceDir: SRC, targetDir: out, log: () => {}, force: false });

  // Agents: only rtl-designer (+ alwaysInclude, but fixture doesn't have them)
  assert.ok(fs.existsSync(path.join(out, '.claude/agents/rtl-designer.md')));
  assert.ok(!fs.existsSync(path.join(out, '.claude/agents/debugger.md')));

  // Workflows → commands
  assert.ok(fs.existsSync(path.join(out, '.claude/commands/design.md')));
  assert.ok(!fs.existsSync(path.join(out, '.claude/commands/debug.md')),
    'debug workflow not in rtl-designer profile');

  // CLAUDE.md at root, filtered
  const claudeMd = fs.readFileSync(path.join(out, 'CLAUDE.md'), 'utf8');
  assert.ok(claudeMd.includes('rtl-designer.md'));
  assert.ok(!claudeMd.includes('physical-design-engineer.md'),
    'Agent Routing table filtered');
});

test('claude full-stack keeps entire Agent Routing table', () => {
  const out = fs.mkdtempSync(path.join(os.tmpdir(), 'cl-'));
  const profile = resolve('full-stack', path.join(SRC, '.agent/agents'));
  adapter.emit({ profile, sourceDir: SRC, targetDir: out, log: () => {}, force: false });
  const claudeMd = fs.readFileSync(path.join(out, 'CLAUDE.md'), 'utf8');
  assert.ok(claudeMd.includes('rtl-designer.md'));
  assert.ok(claudeMd.includes('physical-design-engineer.md'));
});
```

- [ ] **Step 6: Run — expect FAIL**

Run: `npm test`
Expected: FAIL

- [ ] **Step 7: Implement `bin/adapters/claude.js`**

```js
const fs = require('node:fs');
const path = require('node:path');
const { copyFile, writeFile, pathExists } = require('../fs-util');
const { filterAgentRoutingTable } = require('./claude-md-filter');

function emit({ profile, sourceDir, targetDir, log = () => {} }) {
  const agentsSrc = path.join(sourceDir, '.agent/agents');
  const wfSrc = path.join(sourceDir, '.agent/workflows');
  const claudeMdSrc = path.join(sourceDir, 'CLAUDE.md');

  // Agents -> .claude/agents/
  if (pathExists(agentsSrc)) {
    for (const id of profile.agents) {
      const f = path.join(agentsSrc, `${id}.md`);
      if (pathExists(f)) copyFile(f, path.join(targetDir, '.claude/agents', `${id}.md`));
    }
    log(`  .claude/agents/ (${profile.agents.length})`);
  }

  // Workflows -> .claude/commands/
  if (pathExists(wfSrc)) {
    for (const id of profile.workflows) {
      const f = path.join(wfSrc, `${id}.md`);
      if (pathExists(f)) copyFile(f, path.join(targetDir, '.claude/commands', `${id}.md`));
    }
    log(`  .claude/commands/ (${profile.workflows.length})`);
  }

  // CLAUDE.md — filter Agent Routing table
  if (pathExists(claudeMdSrc)) {
    let md = fs.readFileSync(claudeMdSrc, 'utf8');
    if (!profile.isFullStack) {
      md = filterAgentRoutingTable(md, new Set(profile.agents));
    }
    writeFile(path.join(targetDir, 'CLAUDE.md'), md);
    log(`  CLAUDE.md`);
  }
}

module.exports = {
  id: 'claude',
  name: 'Claude Code',
  targetPaths: ['.claude/', 'CLAUDE.md'],
  emit
};
```

- [ ] **Step 8: Run — expect PASS**

Run: `npm test`
Expected: PASS

- [ ] **Step 9: Commit**

```bash
git add bin/adapters/claude.js bin/adapters/claude-md-filter.js \
        test/adapters-claude.test.js test/claude-md-filter.test.js
git commit -m "feat(adapters): implement claude emitter with filtered CLAUDE.md"
```

---

### Task 9: VS Code adapter

**Files:**
- Modify: `bin/adapters/vscode.js`
- Create: `test/adapters-vscode.test.js`

- [ ] **Step 1: Write failing test**

Create `test/adapters-vscode.test.js`:

```js
const test = require('node:test');
const assert = require('node:assert');
const fs = require('node:fs');
const os = require('node:os');
const path = require('node:path');
const adapter = require('../bin/adapters/vscode');
const { resolve } = require('../bin/profiles');

const SRC = path.join(__dirname, 'fixtures/canonical');

test('vscode emits copilot-instructions.md with filtered routing, no slash commands', () => {
  const out = fs.mkdtempSync(path.join(os.tmpdir(), 'vs-'));
  const profile = resolve('rtl-designer', path.join(SRC, '.agent/agents'));
  adapter.emit({ profile, sourceDir: SRC, targetDir: out, log: () => {}, force: false });

  const file = path.join(out, '.github/copilot-instructions.md');
  assert.ok(fs.existsSync(file));
  const md = fs.readFileSync(file, 'utf8');
  assert.ok(md.includes('rtl-designer.md'));
  assert.ok(!md.includes('physical-design-engineer.md'),
    'routing table filtered to profile');
  assert.ok(!md.includes('Available Slash Commands'),
    'slash commands section stripped');
  assert.ok(!md.includes('/design'), 'slash command rows stripped');
  // Exactly one top-level H1 in the emitted file
  const h1s = md.split(/\r?\n/).filter(l => /^#\s/.test(l));
  assert.strictEqual(h1s.length, 1, `expected 1 H1, got ${h1s.length}: ${h1s.join(' | ')}`);
});

test('vscode + real .agent/ content does not produce malformed frontmatter', () => {
  // Regression guard: descriptions in real agent files contain commas.
  // This test only fails if the parser regresses to auto-splitting on commas.
  const out = fs.mkdtempSync(path.join(os.tmpdir(), 'vs-real-'));
  const realSrc = path.join(__dirname, '..');  // package root
  const profile = resolve('full-stack', path.join(realSrc, '.agent/agents'));
  adapter.emit({ profile, sourceDir: realSrc, targetDir: out, log: () => {}, force: false });
  const md = fs.readFileSync(path.join(out, '.github/copilot-instructions.md'), 'utf8');
  assert.ok(md.length > 100);
});
```

(A matching cursor regression test is added in Task 10, Step 1 below.)

- [ ] **Step 2: Run — expect FAIL**

Run: `npm test`
Expected: FAIL

- [ ] **Step 3: Implement `bin/adapters/vscode.js`**

```js
const fs = require('node:fs');
const path = require('node:path');
const { writeFile, pathExists } = require('../fs-util');
const { filterAgentRoutingTable, stripSlashCommandsSection } = require('./claude-md-filter');

function emit({ profile, sourceDir, targetDir, log = () => {} }) {
  const claudeMdSrc = path.join(sourceDir, 'CLAUDE.md');
  if (!pathExists(claudeMdSrc)) {
    throw new Error(`vscode adapter: canonical CLAUDE.md missing at ${claudeMdSrc}`);
  }
  let md = fs.readFileSync(claudeMdSrc, 'utf8');
  if (!profile.isFullStack) {
    md = filterAgentRoutingTable(md, new Set(profile.agents));
  }
  md = stripSlashCommandsSection(md);
  // Strip the canonical CLAUDE.md's leading H1 so we don't end up with two H1s.
  md = md.replace(/^#\s[^\n]*\n+/, '');

  const header = [
    '# GitHub Copilot Instructions — VLSI Agent Kit',
    '',
    `**Active profile:** ${profile.name}`,
    '',
    '---',
    ''
  ].join('\n');

  writeFile(path.join(targetDir, '.github/copilot-instructions.md'), header + md);
  log(`  .github/copilot-instructions.md`);
}

module.exports = {
  id: 'vscode',
  name: 'VS Code / Copilot',
  targetPaths: ['.github/copilot-instructions.md'],
  emit
};
```

- [ ] **Step 4: Run — expect PASS**

Run: `npm test`
Expected: PASS

- [ ] **Step 5: Commit**

```bash
git add bin/adapters/vscode.js test/adapters-vscode.test.js
git commit -m "feat(adapters): implement vscode/copilot emitter"
```

---

### Task 10: Cursor adapter (MDC with frontmatter)

**Files:**
- Modify: `bin/adapters/cursor.js`
- Create: `test/adapters-cursor.test.js`

- [ ] **Step 1: Write failing test**

Create `test/adapters-cursor.test.js`:

```js
const test = require('node:test');
const assert = require('node:assert');
const fs = require('node:fs');
const os = require('node:os');
const path = require('node:path');
const adapter = require('../bin/adapters/cursor');
const { resolve } = require('../bin/profiles');

const SRC = path.join(__dirname, 'fixtures/canonical');

test('cursor emits .mdc files with glob frontmatter for HDL agents', () => {
  const out = fs.mkdtempSync(path.join(os.tmpdir(), 'cur-'));
  const profile = resolve('full-stack', path.join(SRC, '.agent/agents'));
  adapter.emit({ profile, sourceDir: SRC, targetDir: out, log: () => {}, force: false });

  const rtl = fs.readFileSync(path.join(out, '.cursor/rules/rtl-designer.mdc'), 'utf8');
  assert.ok(rtl.startsWith('---\n'));
  assert.ok(rtl.includes('description: RTL design expert.'));
  assert.ok(rtl.includes('globs: "**/*.{sv,svh,v,vh,vhd,vhdl}"'));
  assert.ok(rtl.includes('alwaysApply: false'));
  assert.ok(rtl.includes('# RTL Designer body'), 'body preserved');
});

test('cursor emits alwaysApply: true for agents not in globs map', () => {
  const out = fs.mkdtempSync(path.join(os.tmpdir(), 'cur-'));
  const profile = resolve('full-stack', path.join(SRC, '.agent/agents'));
  adapter.emit({ profile, sourceDir: SRC, targetDir: out, log: () => {}, force: false });

  const dbg = fs.readFileSync(path.join(out, '.cursor/rules/debugger.mdc'), 'utf8');
  assert.ok(dbg.includes('alwaysApply: true'));
  assert.ok(!dbg.includes('globs:'),
    'no globs field when alwaysApply');
});

test('cursor + real .agent/ content emits valid MDC frontmatter (regression guard)', () => {
  // This test only fails if the parser regresses to auto-splitting on commas,
  // because real agent description: fields all contain commas.
  const out = fs.mkdtempSync(path.join(os.tmpdir(), 'cur-real-'));
  const realSrc = path.join(__dirname, '..');  // package root
  const profile = resolve('full-stack', path.join(realSrc, '.agent/agents'));
  adapter.emit({ profile, sourceDir: realSrc, targetDir: out, log: () => {}, force: false });

  const files = fs.readdirSync(path.join(out, '.cursor/rules'));
  assert.ok(files.length >= 10, 'expect multiple agents emitted');
  for (const f of files) {
    const content = fs.readFileSync(path.join(out, '.cursor/rules', f), 'utf8');
    assert.ok(content.startsWith('---\n'), `${f} missing fence`);
    const descLine = content.split('\n').find(l => l.startsWith('description:'));
    assert.ok(descLine, `${f} missing description line`);
    // description is free-form prose — must not have been mangled by array-join
    // (e.g., no ",and" artifacts from split+join collapsing spaces)
    assert.ok(!/,[A-Za-z]/.test(descLine.replace('description:', '')),
      `${f} description appears mangled: ${descLine}`);
  }
});
```

- [ ] **Step 2: Run — expect FAIL**

Run: `npm test`
Expected: FAIL

- [ ] **Step 3: Implement `bin/adapters/cursor.js`**

```js
const fs = require('node:fs');
const path = require('node:path');
const { writeFile, pathExists, readFrontmatter } = require('../fs-util');
const { globsFor, isAlwaysApply } = require('./globs');

function buildFrontmatter(agentId, description) {
  const lines = ['---', `description: ${description}`];
  if (isAlwaysApply(agentId)) {
    lines.push('alwaysApply: true');
  } else {
    const g = globsFor(agentId);
    const v = g.length === 1 ? JSON.stringify(g[0]) : JSON.stringify(g.join(','));
    lines.push(`globs: ${v}`);
    lines.push('alwaysApply: false');
  }
  lines.push('---', '');
  return lines.join('\n');
}

function emit({ profile, sourceDir, targetDir, log = () => {} }) {
  const agentsSrc = path.join(sourceDir, '.agent/agents');
  if (!pathExists(agentsSrc)) return;
  let count = 0;
  for (const id of profile.agents) {
    const f = path.join(agentsSrc, `${id}.md`);
    if (!pathExists(f)) continue;
    const { data, body } = readFrontmatter(f);
    const fm = buildFrontmatter(id, data.description || '');
    const out = fm + body.trimStart();
    writeFile(path.join(targetDir, '.cursor/rules', `${id}.mdc`), out);
    count++;
  }
  log(`  .cursor/rules/ (${count})`);
}

module.exports = {
  id: 'cursor',
  name: 'Cursor',
  targetPaths: ['.cursor/'],
  emit
};
```

- [ ] **Step 4: Run — expect PASS**

Run: `npm test`
Expected: PASS

- [ ] **Step 5: Commit**

```bash
git add bin/adapters/cursor.js test/adapters-cursor.test.js
git commit -m "feat(adapters): implement cursor emitter with glob frontmatter"
```

---

### Task 11: Windsurf adapter (reuses globs logic)

**Files:**
- Modify: `bin/adapters/windsurf.js`
- Create: `test/adapters-windsurf.test.js`

- [ ] **Step 1: Write failing test**

Create `test/adapters-windsurf.test.js`:

```js
const test = require('node:test');
const assert = require('node:assert');
const fs = require('node:fs');
const os = require('node:os');
const path = require('node:path');
const adapter = require('../bin/adapters/windsurf');
const { resolve } = require('../bin/profiles');

const SRC = path.join(__dirname, 'fixtures/canonical');

test('windsurf emits .md rules with frontmatter', () => {
  const out = fs.mkdtempSync(path.join(os.tmpdir(), 'ws-'));
  const profile = resolve('full-stack', path.join(SRC, '.agent/agents'));
  adapter.emit({ profile, sourceDir: SRC, targetDir: out, log: () => {}, force: false });

  const rtl = fs.readFileSync(path.join(out, '.windsurf/rules/rtl-designer.md'), 'utf8');
  assert.ok(rtl.includes('globs: "**/*.{sv,svh,v,vh,vhd,vhdl}"'));
  assert.ok(rtl.includes('# RTL Designer body'));
  const dbg = fs.readFileSync(path.join(out, '.windsurf/rules/debugger.md'), 'utf8');
  assert.ok(dbg.includes('alwaysApply: true'));
});
```

- [ ] **Step 2: Run — expect FAIL**

Run: `npm test`
Expected: FAIL

- [ ] **Step 3: Implement `bin/adapters/windsurf.js`**

```js
const path = require('node:path');
const { writeFile, pathExists, readFrontmatter } = require('../fs-util');
const { globsFor, isAlwaysApply } = require('./globs');

function buildFrontmatter(agentId, description) {
  const lines = ['---', `description: ${description}`];
  if (isAlwaysApply(agentId)) {
    lines.push('alwaysApply: true');
  } else {
    const g = globsFor(agentId);
    const v = g.length === 1 ? JSON.stringify(g[0]) : JSON.stringify(g.join(','));
    lines.push(`globs: ${v}`);
    lines.push('alwaysApply: false');
  }
  lines.push('---', '');
  return lines.join('\n');
}

function emit({ profile, sourceDir, targetDir, log = () => {} }) {
  const agentsSrc = path.join(sourceDir, '.agent/agents');
  if (!pathExists(agentsSrc)) return;
  let count = 0;
  for (const id of profile.agents) {
    const f = path.join(agentsSrc, `${id}.md`);
    if (!pathExists(f)) continue;
    const { data, body } = readFrontmatter(f);
    const fm = buildFrontmatter(id, data.description || '');
    writeFile(path.join(targetDir, '.windsurf/rules', `${id}.md`), fm + body.trimStart());
    count++;
  }
  log(`  .windsurf/rules/ (${count})`);
}

module.exports = {
  id: 'windsurf',
  name: 'Windsurf',
  targetPaths: ['.windsurf/'],
  emit
};
```

- [ ] **Step 4: Run — expect PASS**

Run: `npm test`
Expected: PASS

- [ ] **Step 5: Refactor — extract shared MDC frontmatter builder**

Both cursor and windsurf have identical `buildFrontmatter`. Move it to `bin/adapters/globs.js` to DRY:

Add to `bin/adapters/globs.js`:
```js
function buildRuleFrontmatter(agentId, description) {
  const lines = ['---', `description: ${description}`];
  if (isAlwaysApply(agentId)) {
    lines.push('alwaysApply: true');
  } else {
    const g = globsFor(agentId);
    const v = g.length === 1 ? JSON.stringify(g[0]) : JSON.stringify(g.join(','));
    lines.push(`globs: ${v}`);
    lines.push('alwaysApply: false');
  }
  lines.push('---', '');
  return lines.join('\n');
}

module.exports = { globsFor, isAlwaysApply, buildRuleFrontmatter };
```

Update `bin/adapters/cursor.js` and `bin/adapters/windsurf.js` to import and use `buildRuleFrontmatter` instead of their local copies. Delete the local copies.

- [ ] **Step 6: Run — expect PASS**

Run: `npm test`
Expected: PASS (all tests still green after refactor).

- [ ] **Step 7: Commit**

```bash
git add bin/adapters/windsurf.js bin/adapters/cursor.js bin/adapters/globs.js \
        test/adapters-windsurf.test.js
git commit -m "feat(adapters): implement windsurf emitter; DRY frontmatter builder"
```

---

## Chunk 3: CLI wiring (prompts, conflict handling, entry point)

### Task 12: `bin/prompts.js` — interactive prompts

**Files:**
- Create: `bin/prompts.js`
- Create: `test/prompts.test.js`

- [ ] **Step 1: Write failing test**

Create `test/prompts.test.js`:

```js
const test = require('node:test');
const assert = require('node:assert');
const { validateNonInteractiveFlags, parseToolsCsv } = require('../bin/prompts');

test('parseToolsCsv splits and trims', () => {
  assert.deepStrictEqual(parseToolsCsv('claude, cursor,windsurf'),
    ['claude', 'cursor', 'windsurf']);
});

test('parseToolsCsv throws on unknown id', () => {
  assert.throws(() => parseToolsCsv('claude,nope'), /nope/);
});

test('parseToolsCsv throws on empty', () => {
  assert.throws(() => parseToolsCsv(''), /at least one/i);
});

test('validateNonInteractiveFlags passes when both set', () => {
  assert.doesNotThrow(() =>
    validateNonInteractiveFlags({ role: 'full-stack', tools: 'claude' }));
});

test('validateNonInteractiveFlags throws when role missing', () => {
  assert.throws(() => validateNonInteractiveFlags({ tools: 'claude' }), /--role/);
});

test('validateNonInteractiveFlags throws on unknown role', () => {
  assert.throws(() => validateNonInteractiveFlags({ role: 'nope', tools: 'claude' }),
    /nope/);
});
```

- [ ] **Step 2: Run — expect FAIL**

Run: `npm test`
Expected: FAIL

- [ ] **Step 3: Implement `bin/prompts.js`**

```js
const profiles = require('./profiles');
const adapters = require('./adapters');

function parseToolsCsv(csv) {
  if (!csv || !csv.trim()) throw new Error('--tools requires at least one tool');
  const ids = csv.split(',').map(s => s.trim()).filter(Boolean);
  for (const id of ids) {
    if (!adapters.VALID_IDS.has(id)) {
      throw new Error(`Unknown tool "${id}". Valid: ${[...adapters.VALID_IDS].join(', ')}`);
    }
  }
  return ids;
}

function validateNonInteractiveFlags({ role, tools }) {
  if (!role) throw new Error('--role is required in non-interactive mode');
  if (!tools) throw new Error('--tools is required in non-interactive mode');
  if (!profiles.VALID_IDS.has(role)) {
    throw new Error(
      `Unknown role "${role}". Valid: ${[...profiles.VALID_IDS].join(', ')}`
    );
  }
  parseToolsCsv(tools);
}

async function promptInteractive({ defaultDir = '.' } = {}) {
  const { select, checkbox, input } = require('@inquirer/prompts');

  const role = await select({
    message: 'Select your role profile:',
    choices: profiles.list().map(p => ({
      name: `${p.name} — ${p.description}`,
      value: p.id
    })),
    default: 'full-stack'
  });

  const tools = await checkbox({
    message: 'Select tools to install for:',
    choices: adapters.list().map(a => ({ name: a.name, value: a.id })),
    required: true,
    validate: (v) => v.length > 0 || 'Pick at least one tool'
  });

  const dir = await input({
    message: 'Target directory:',
    default: defaultDir
  });

  return { role, tools, dir };
}

async function promptOverwrite(pathLabel) {
  const { confirm } = require('@inquirer/prompts');
  return confirm({
    message: `${pathLabel} already exists — overwrite?`,
    default: false
  });
}

module.exports = {
  parseToolsCsv,
  validateNonInteractiveFlags,
  promptInteractive,
  promptOverwrite
};
```

- [ ] **Step 4: Run — expect PASS (unit-level)**

Run: `npm test`
Expected: PASS — pure helpers tested; `promptInteractive` / `promptOverwrite` are not unit-tested (they wrap inquirer and are covered by manual smoke).

- [ ] **Step 5: Commit**

```bash
git add bin/prompts.js test/prompts.test.js
git commit -m "feat(prompts): add interactive prompts + flag validation"
```

---

### Task 13: Rewrite `bin/cli.js` — orchestrator

**Files:**
- Modify: `bin/cli.js`
- Create: `test/cli-flags.test.js`

- [ ] **Step 1: Write failing test for flag parsing**

Create `test/cli-flags.test.js`:

```js
const test = require('node:test');
const assert = require('node:assert');
const { parseArgs } = require('../bin/cli');

test('parseArgs extracts role, tools, dir, force', () => {
  const a = parseArgs(['init', '--role', 'fpga-engineer',
    '--tools', 'claude,cursor', '--dir', './out', '--force']);
  assert.strictEqual(a.command, 'init');
  assert.strictEqual(a.role, 'fpga-engineer');
  assert.strictEqual(a.tools, 'claude,cursor');
  assert.strictEqual(a.dir, './out');
  assert.strictEqual(a.force, true);
});

test('parseArgs defaults dir to .', () => {
  const a = parseArgs(['init']);
  assert.strictEqual(a.dir, '.');
  assert.strictEqual(a.force, false);
});

test('parseArgs recognizes --list-profiles / --list-tools', () => {
  assert.strictEqual(parseArgs(['init', '--list-profiles']).listProfiles, true);
  assert.strictEqual(parseArgs(['init', '--list-tools']).listTools, true);
});

test('parseArgs recognizes help / version', () => {
  assert.strictEqual(parseArgs(['help']).command, 'help');
  assert.strictEqual(parseArgs(['--version']).command, 'version');
});
```

- [ ] **Step 2: Run — expect FAIL**

Run: `npm test`
Expected: FAIL — current cli.js exports nothing.

- [ ] **Step 3: Rewrite `bin/cli.js`**

Replace the entire file:

```js
#!/usr/bin/env node

const fs = require('node:fs');
const path = require('node:path');
const profiles = require('./profiles');
const adaptersReg = require('./adapters');
const { pathExists } = require('./fs-util');
const {
  parseToolsCsv, validateNonInteractiveFlags,
  promptInteractive, promptOverwrite
} = require('./prompts');

const COLORS = { reset: '\x1b[0m', green: '\x1b[32m', cyan: '\x1b[36m',
  yellow: '\x1b[33m', red: '\x1b[31m', bold: '\x1b[1m' };
const log = (msg, color = '') => console.log(`${color}${msg}${COLORS.reset}`);

function parseArgs(argv) {
  const out = { command: null, role: null, tools: null, dir: '.',
    force: false, listProfiles: false, listTools: false };
  if (argv.length === 0) { out.command = 'help'; return out; }

  // First positional is command, unless it starts with "-"
  let i = 0;
  if (!argv[0].startsWith('-')) { out.command = argv[i++]; }

  for (; i < argv.length; i++) {
    const a = argv[i];
    switch (a) {
      case '--role':           out.role = argv[++i]; break;
      case '--tools':          out.tools = argv[++i]; break;
      case '--dir':            out.dir = argv[++i]; break;
      case '--force':          out.force = true; break;
      case '--list-profiles':  out.listProfiles = true; break;
      case '--list-tools':     out.listTools = true; break;
      case '-v':
      case '--version':        out.command = 'version'; break;
      case '-h':
      case '--help':           out.command = 'help'; break;
      default:
        if (a.startsWith('-')) throw new Error(`Unknown flag: ${a}`);
    }
  }
  return out;
}

function showHelp() {
  log('\nVLSI Agent Kit CLI\n', COLORS.cyan + COLORS.bold);
  log('Usage: vlsi-agkit <command> [options]\n');
  log('Commands:');
  log('  init [options]     Initialize VLSI Agent Kit');
  log('  help               Show this help');
  log('  version            Show version\n');
  log('Options (init):');
  log('  --role <id>        Profile id (skips prompt)');
  log('  --tools <csv>      Comma-separated tool ids (skips prompt)');
  log('  --dir <path>       Target directory (default: .)');
  log('  --force            Overwrite existing target paths');
  log('  --list-profiles    Print profiles and exit');
  log('  --list-tools       Print tools and exit\n');
}

function showVersion() {
  const pkg = require('../package.json');
  log(`VLSI Agent Kit v${pkg.version}`);
}

function listProfilesCmd() {
  log('\nAvailable role profiles:\n', COLORS.cyan + COLORS.bold);
  for (const p of profiles.list()) {
    log(`  ${p.id}`, COLORS.green);
    log(`    ${p.name} — ${p.description}`);
  }
  log('');
}

function listToolsCmd() {
  log('\nAvailable tools:\n', COLORS.cyan + COLORS.bold);
  for (const a of adaptersReg.list()) {
    log(`  ${a.id}`, COLORS.green);
    log(`    ${a.name} (writes: ${a.targetPaths.join(', ')})`);
  }
  log('');
}

async function init(opts) {
  log('\nVLSI Kit — AI Agent Kit for VLSI Development\n', COLORS.cyan + COLORS.bold);

  const interactive = process.stdin.isTTY && !opts.role && !opts.tools;

  let role, toolsIds, targetDir;
  if (interactive) {
    const ans = await promptInteractive({ defaultDir: opts.dir });
    role = ans.role; toolsIds = ans.tools; targetDir = ans.dir;
  } else {
    validateNonInteractiveFlags({ role: opts.role, tools: opts.tools });
    role = opts.role;
    toolsIds = parseToolsCsv(opts.tools);
    targetDir = opts.dir;
  }

  const packageDir = path.dirname(__dirname);
  const agentsDir = path.join(packageDir, '.agent/agents');
  const profile = profiles.resolve(role, agentsDir);
  const selected = toolsIds.map(id => adaptersReg.get(id));

  // Conflict pre-check
  const conflicts = [];
  for (const a of selected) {
    for (const rel of a.targetPaths) {
      const abs = path.join(targetDir, rel);
      if (pathExists(abs)) conflicts.push({ adapter: a.id, path: abs });
    }
  }

  if (conflicts.length > 0 && !opts.force) {
    if (interactive) {
      for (const c of conflicts) {
        const ok = await promptOverwrite(c.path);
        if (!ok) { log(`Aborted: ${c.path} not overwritten.`, COLORS.yellow); return 1; }
      }
      // Remove conflicted paths so adapters write cleanly
      for (const c of conflicts) fs.rmSync(c.path, { recursive: true, force: true });
    } else {
      log('Refusing to overwrite existing paths:', COLORS.red);
      for (const c of conflicts) log(`  ${c.path}`);
      log('Re-run with --force to overwrite.');
      return 1;
    }
  } else if (conflicts.length > 0 && opts.force) {
    for (const c of conflicts) fs.rmSync(c.path, { recursive: true, force: true });
  }

  // Emit
  log(`Profile: ${profile.name} (${profile.agents.length} agents, ${profile.skills.length} skills, ${profile.workflows.length} workflows)`, COLORS.cyan);
  for (const a of selected) {
    log(`Emitting for ${a.name}`, COLORS.cyan);
    a.emit({ profile, sourceDir: packageDir, targetDir, log: msg => log(msg), force: opts.force });
  }

  log('\nDone.\n', COLORS.green + COLORS.bold);
  return 0;
}

async function main(argv) {
  let opts;
  try { opts = parseArgs(argv); }
  catch (e) { log(`Error: ${e.message}`, COLORS.red); process.exit(1); }

  try {
    switch (opts.command) {
      case 'init':
        if (opts.listProfiles) { listProfilesCmd(); return; }
        if (opts.listTools)    { listToolsCmd(); return; }
        process.exit(await init(opts));
        break;
      case 'version': showVersion(); break;
      case 'help':
      default:        showHelp(); break;
    }
  } catch (e) {
    log(`Error: ${e.message}`, COLORS.red);
    process.exit(1);
  }
}

module.exports = { parseArgs, main };

if (require.main === module) {
  main(process.argv.slice(2));
}
```

- [ ] **Step 4: Run — expect PASS**

Run: `npm test`
Expected: PASS — flag tests green plus all prior tests.

- [ ] **Step 5: Commit**

```bash
git add bin/cli.js test/cli-flags.test.js
git commit -m "feat(cli): orchestrator with flag parsing, conflict handling, interactive prompts"
```

---

### Task 14: End-to-end integration test

**Files:**
- Create: `test/integration.test.js`

- [ ] **Step 1: Write failing test**

Create `test/integration.test.js`:

```js
const test = require('node:test');
const assert = require('node:assert');
const { execFileSync } = require('node:child_process');
const fs = require('node:fs');
const os = require('node:os');
const path = require('node:path');

const CLI = path.join(__dirname, '../bin/cli.js');

function runCli(args, cwd) {
  return execFileSync(process.execPath, [CLI, ...args], {
    cwd, encoding: 'utf8', stdio: ['ignore', 'pipe', 'pipe']
  });
}

test('init --role full-stack --tools antigravity writes .agent/', () => {
  const dir = fs.mkdtempSync(path.join(os.tmpdir(), 'it-'));
  runCli(['init', '--role', 'full-stack', '--tools', 'antigravity', '--dir', dir], process.cwd());
  assert.ok(fs.existsSync(path.join(dir, '.agent/agents/rtl-designer.md')));
});

test('init with all tools and fpga-engineer profile', () => {
  const dir = fs.mkdtempSync(path.join(os.tmpdir(), 'it-'));
  runCli(['init',
    '--role', 'fpga-engineer',
    '--tools', 'claude,gemini,vscode,antigravity,cursor,windsurf',
    '--dir', dir
  ], process.cwd());

  assert.ok(fs.existsSync(path.join(dir, '.claude/agents/fpga-specialist.md')));
  assert.ok(fs.existsSync(path.join(dir, 'GEMINI.md')));
  assert.ok(fs.existsSync(path.join(dir, '.github/copilot-instructions.md')));
  assert.ok(fs.existsSync(path.join(dir, '.agent/agents/fpga-specialist.md')));
  assert.ok(fs.existsSync(path.join(dir, '.cursor/rules/fpga-specialist.mdc')));
  assert.ok(fs.existsSync(path.join(dir, '.windsurf/rules/fpga-specialist.md')));

  // Filtered out: verification-engineer not in fpga-engineer profile
  assert.ok(!fs.existsSync(path.join(dir, '.claude/agents/verification-engineer.md')));
});

test('init refuses to overwrite without --force', () => {
  const dir = fs.mkdtempSync(path.join(os.tmpdir(), 'it-'));
  fs.mkdirSync(path.join(dir, '.agent'));
  assert.throws(() => runCli([
    'init', '--role', 'full-stack', '--tools', 'antigravity', '--dir', dir
  ], process.cwd()), /Refusing to overwrite|non-zero/);
});

test('init --force overwrites', () => {
  const dir = fs.mkdtempSync(path.join(os.tmpdir(), 'it-'));
  fs.mkdirSync(path.join(dir, '.agent'));
  fs.writeFileSync(path.join(dir, '.agent/stale.txt'), 'old');
  runCli(['init', '--role', 'full-stack', '--tools', 'antigravity',
          '--dir', dir, '--force'], process.cwd());
  assert.ok(!fs.existsSync(path.join(dir, '.agent/stale.txt')),
    'stale file removed');
  assert.ok(fs.existsSync(path.join(dir, '.agent/agents/rtl-designer.md')));
});

test('init --list-profiles exits 0 and prints ids', () => {
  const out = runCli(['init', '--list-profiles'], process.cwd());
  assert.ok(out.includes('full-stack'));
  assert.ok(out.includes('fpga-engineer'));
});

test('init without role/tools in non-TTY fails with guidance', () => {
  const dir = fs.mkdtempSync(path.join(os.tmpdir(), 'it-'));
  assert.throws(() => runCli(['init', '--dir', dir], process.cwd()),
    /non-zero|--role/);
});
```

- [ ] **Step 2: Run — expect PASS (or reveal bugs)**

Run: `npm test`
Expected: PASS. If any adapter fails on real `.agent/` content (vs fixture), fix the offending adapter and re-run.

- [ ] **Step 3: Commit**

```bash
git add test/integration.test.js
git commit -m "test: add end-to-end integration tests"
```

---

## Chunk 4: Docs + manual smoke

### Task 15: Update README

**Files:**
- Modify: `README.md`

- [ ] **Step 1: Update README**

Rewrite the "Quick Install" and "What's Included" sections, and add a "Migration" note. Replace the existing `## Quick Install` block (through `### Manual Installation`) with:

```markdown
## Quick Install

```bash
npx @kishore-damam/vlsi-agkit init
```

You'll be prompted to:
1. Pick a **role profile** (Full Stack, FPGA Engineer, ASIC Engineer, Verification Engineer, RTL Designer, or Physical Design).
2. Pick one or more **target tools**:

| Tool | Output |
|---|---|
| Claude Code | `.claude/agents/`, `.claude/commands/`, `CLAUDE.md` |
| Gemini CLI | `GEMINI.md` |
| VS Code / Copilot | `.github/copilot-instructions.md` |
| Antigravity | `.agent/` (legacy layout) |
| Cursor | `.cursor/rules/*.mdc` |
| Windsurf | `.windsurf/rules/*.md` |

### Non-interactive / scripted install

```bash
npx @kishore-damam/vlsi-agkit init \
  --role fpga-engineer \
  --tools claude,cursor \
  --dir ./my-project
```

See `vlsi-agkit init --list-profiles` and `vlsi-agkit init --list-tools` for available ids.

### Migration from 1.0.x

1.0.x always installed `.agent/` + `GEMINI.md`. For equivalent behavior:
```bash
vlsi-agkit init --role full-stack --tools antigravity,gemini
```
```

- [ ] **Step 2: Commit**

```bash
git add README.md
git commit -m "docs: document role profiles and multi-tool install"
```

---

### Task 16: Manual smoke test

- [ ] **Step 1: Link and test in an empty scratch dir**

```bash
cd /d/Projects/agkit/vlsi-kit
npm link
mkdir -p /tmp/vlsi-smoke && cd /tmp/vlsi-smoke
vlsi-agkit init --role fpga-engineer --tools claude,cursor,windsurf
```

Expected:
- `.claude/agents/` has 6–8 filtered agent files (fpga-specialist, rtl-designer, timing-analyst, ip-integrator, debugger, lint-reviewer + implicit orchestrator, project-planner)
- `.claude/commands/` has 5 workflows (design, debug, lint, timing, integrate)
- `CLAUDE.md` written at root; its Agent Routing table only references the included agents
- `.cursor/rules/*.mdc` — each with frontmatter; rtl-designer has `globs:"**/*.{sv,svh,v,vh,vhd,vhdl}"`
- `.windsurf/rules/*.md` — matching set

- [ ] **Step 2: Spot-check file contents**

```bash
head -15 /tmp/vlsi-smoke/.cursor/rules/rtl-designer.mdc
head -15 /tmp/vlsi-smoke/.cursor/rules/debugger.mdc    # should be alwaysApply: true
grep -c '.md' /tmp/vlsi-smoke/CLAUDE.md                # filtered routing table
```

- [ ] **Step 3: Run the interactive path**

```bash
cd /tmp && mkdir vlsi-interactive && cd vlsi-interactive
vlsi-agkit init
# Walk through: select a profile, check 2 tools, accept default dir
```

- [ ] **Step 4: Unlink**

```bash
cd /d/Projects/agkit/vlsi-kit && npm unlink
```

- [ ] **Step 5: Tag the release**

Tag the final commit (already on HEAD from the README or prior commit):

```bash
git tag v1.1.0
```

Do not push the tag unless the user asks.

---

## Done criteria

- [ ] `npm test` passes all unit + integration tests.
- [ ] `vlsi-agkit init --list-profiles` lists six profiles.
- [ ] `vlsi-agkit init --list-tools` lists six tools.
- [ ] Interactive `init` prompts for role, tools, and directory.
- [ ] `--role X --tools Y` flag combo works non-interactively.
- [ ] Each tool's output is in the correct location with correct format.
- [ ] Conflicts are detected; `--force` overrides; interactive prompts per-conflict.
- [ ] README documents migration path from 1.0.x.
