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
  const { _expandSkills } = require('../bin/profiles');
  const result = _expandSkills(['no-skills-agent'], FIXTURE);
  assert.deepStrictEqual(result, []);
});
