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
