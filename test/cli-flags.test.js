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
