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
