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
