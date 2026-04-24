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
