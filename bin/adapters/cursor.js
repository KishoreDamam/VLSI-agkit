const fs = require('node:fs');
const path = require('node:path');
const { writeFile, pathExists, readFrontmatter } = require('../fs-util');
const { buildRuleFrontmatter } = require('./globs');

function emit({ profile, sourceDir, targetDir, log = () => {} }) {
  const agentsSrc = path.join(sourceDir, '.agent/agents');
  if (!pathExists(agentsSrc)) return;
  let count = 0;
  for (const id of profile.agents) {
    const f = path.join(agentsSrc, `${id}.md`);
    if (!pathExists(f)) continue;
    const { data, body } = readFrontmatter(f);
    const fm = buildRuleFrontmatter(id, data.description || '');
    const out = fm + body.trimStart();
    writeFile(path.join(targetDir, '.cursor/rules', `${id}.mdc`), out);
    count++;
  }
  log(`  .cursor/rules/ (${count})`);
}

module.exports = {
  id: 'cursor',
  name: 'Cursor',
  targetPaths: ['.cursor/'],
  emit
};
