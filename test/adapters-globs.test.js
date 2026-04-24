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
