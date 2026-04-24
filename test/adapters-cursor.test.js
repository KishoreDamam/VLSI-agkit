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
  const out = fs.mkdtempSync(path.join(os.tmpdir(), 'cur-real-'));
  const realSrc = path.join(__dirname, '..');
  const profile = resolve('full-stack', path.join(realSrc, '.agent/agents'));
  adapter.emit({ profile, sourceDir: realSrc, targetDir: out, log: () => {}, force: false });

  const files = fs.readdirSync(path.join(out, '.cursor/rules'));
  assert.ok(files.length >= 10, 'expect multiple agents emitted');
  for (const f of files) {
    const content = fs.readFileSync(path.join(out, '.cursor/rules', f), 'utf8');
    assert.ok(content.startsWith('---\n'), `${f} missing fence`);
    const descLine = content.split('\n').find(l => l.startsWith('description:'));
    assert.ok(descLine, `${f} missing description line`);
    assert.ok(!/,[A-Za-z]/.test(descLine.replace('description:', '')),
      `${f} description appears mangled: ${descLine}`);
  }
});
