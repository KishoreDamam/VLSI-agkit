const fs = require('node:fs');
const path = require('node:path');
const { copyFile, writeFile, pathExists } = require('../fs-util');
const { filterAgentRoutingTable } = require('./claude-md-filter');

function emit({ profile, sourceDir, targetDir, log = () => {} }) {
  const agentsSrc = path.join(sourceDir, '.agent/agents');
  const wfSrc = path.join(sourceDir, '.agent/workflows');
  const claudeMdSrc = path.join(sourceDir, 'CLAUDE.md');

  // Agents -> .claude/agents/
  if (pathExists(agentsSrc)) {
    for (const id of profile.agents) {
      const f = path.join(agentsSrc, `${id}.md`);
      if (pathExists(f)) copyFile(f, path.join(targetDir, '.claude/agents', `${id}.md`));
    }
    log(`  .claude/agents/ (${profile.agents.length})`);
  }

  // Workflows -> .claude/commands/
  if (pathExists(wfSrc)) {
    for (const id of profile.workflows) {
      const f = path.join(wfSrc, `${id}.md`);
      if (pathExists(f)) copyFile(f, path.join(targetDir, '.claude/commands', `${id}.md`));
    }
    log(`  .claude/commands/ (${profile.workflows.length})`);
  }

  // CLAUDE.md — filter Agent Routing table
  if (pathExists(claudeMdSrc)) {
    let md = fs.readFileSync(claudeMdSrc, 'utf8');
    if (!profile.isFullStack) {
      md = filterAgentRoutingTable(md, new Set(profile.agents));
    }
    writeFile(path.join(targetDir, 'CLAUDE.md'), md);
    log(`  CLAUDE.md`);
  }
}

module.exports = {
  id: 'claude',
  name: 'Claude Code',
  targetPaths: ['.claude/', 'CLAUDE.md'],
  emit
};
