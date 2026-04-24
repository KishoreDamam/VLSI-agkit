const fs = require('node:fs');
const path = require('node:path');
const { writeFile, pathExists } = require('../fs-util');
const { filterAgentRoutingTable, stripSlashCommandsSection } = require('./claude-md-filter');

function emit({ profile, sourceDir, targetDir, log = () => {} }) {
  const claudeMdSrc = path.join(sourceDir, 'CLAUDE.md');
  if (!pathExists(claudeMdSrc)) {
    throw new Error(`vscode adapter: canonical CLAUDE.md missing at ${claudeMdSrc}`);
  }
  let md = fs.readFileSync(claudeMdSrc, 'utf8');
  if (!profile.isFullStack) {
    md = filterAgentRoutingTable(md, new Set(profile.agents));
  }
  md = stripSlashCommandsSection(md);
  // Strip the canonical CLAUDE.md's leading H1 so we don't end up with two H1s.
  md = md.replace(/^#\s[^\n]*\n+/, '');

  const header = [
    '# GitHub Copilot Instructions — VLSI Agent Kit',
    '',
    `**Active profile:** ${profile.name}`,
    '',
    '---',
    ''
  ].join('\n');

  writeFile(path.join(targetDir, '.github/copilot-instructions.md'), header + md);
  log(`  .github/copilot-instructions.md`);
}

module.exports = {
  id: 'vscode',
  name: 'VS Code / Copilot',
  targetPaths: ['.github/copilot-instructions.md'],
  emit
};
