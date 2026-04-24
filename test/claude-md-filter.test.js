const test = require('node:test');
const assert = require('node:assert');
const { filterAgentRoutingTable, stripSlashCommandsSection } = require('../bin/adapters/claude-md-filter');

const SAMPLE = `# Title

## Agent Routing

| Domain | Agent File | Trigger Keywords |
|---|---|---|
| RTL Design | \`rtl-designer.md\` | module |
| Debug | \`debugger.md\` | debug |
| Physical Design | \`physical-design-engineer.md\` | pnr |

## Other

stuff

## Available Slash Commands

| Command | Description |
|---|---|
| \`/design\` | RTL |

## Footer

End.
`;

test('filterAgentRoutingTable keeps only matching rows', () => {
  const out = filterAgentRoutingTable(SAMPLE, new Set(['rtl-designer', 'debugger']));
  assert.ok(out.includes('rtl-designer.md'));
  assert.ok(out.includes('debugger.md'));
  assert.ok(!out.includes('physical-design-engineer.md'),
    'non-matching row removed');
  // Header rows preserved
  assert.ok(out.includes('| Domain | Agent File | Trigger Keywords |'));
});

test('filterAgentRoutingTable with full set keeps all rows', () => {
  const all = new Set(['rtl-designer', 'debugger', 'physical-design-engineer']);
  const out = filterAgentRoutingTable(SAMPLE, all);
  assert.ok(out.includes('rtl-designer.md'));
  assert.ok(out.includes('physical-design-engineer.md'));
});

test('stripSlashCommandsSection removes the whole section', () => {
  const out = stripSlashCommandsSection(SAMPLE);
  assert.ok(!out.includes('Available Slash Commands'));
  assert.ok(!out.includes('/design'));
  // Preceding section retained
  assert.ok(out.includes('## Other'));
  // Trailing content after the stripped section also retained
  assert.ok(out.includes('End.'));
});
