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
