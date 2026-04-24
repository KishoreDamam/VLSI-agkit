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

test('validateNonInteractiveFlags throws when tools missing', () => {
  assert.throws(() => validateNonInteractiveFlags({ role: 'full-stack' }), /--tools/);
});
