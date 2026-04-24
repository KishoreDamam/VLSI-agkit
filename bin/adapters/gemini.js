const fs = require('node:fs');
const path = require('node:path');
const { writeFile, pathExists } = require('../fs-util');

function emit({ profile, sourceDir, targetDir, log = () => {} }) {
  const src = path.join(sourceDir, '.agent/rules/GEMINI.md');
  if (!pathExists(src)) {
    throw new Error(`gemini adapter: canonical rules missing at ${src}`);
  }
  let contents = fs.readFileSync(src, 'utf8');

  if (!profile.isFullStack) {
    const summary = [
      '',
      '---',
      '',
      `## Active Profile: ${profile.name}`,
      '',
      profile.description,
      '',
      `**Agents (${profile.agents.length}):** ${profile.agents.join(', ')}`,
      '',
      `**Workflows (${profile.workflows.length}):** ${profile.workflows.map(w => '/' + w).join(', ')}`,
      ''
    ].join('\n');
    contents = contents + summary;
  }

  const dst = path.join(targetDir, 'GEMINI.md');
  writeFile(dst, contents);
  log(`  GEMINI.md`);
}

module.exports = {
  id: 'gemini',
  name: 'Gemini CLI',
  targetPaths: ['GEMINI.md'],
  emit
};
