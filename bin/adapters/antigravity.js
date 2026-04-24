const fs = require('node:fs');
const path = require('node:path');
const { copyFile, writeFile, pathExists, copyDir } = require('../fs-util');

function emit({ profile, sourceDir, targetDir, log = () => {} }) {
  const srcAgent = path.join(sourceDir, '.agent');
  const dstAgent = path.join(targetDir, '.agent');

  if (profile.isFullStack) {
    copyDir(srcAgent, dstAgent);
    log(`  .agent/ (full tree)`);
    return;
  }

  // Always-copy top-level files
  fs.mkdirSync(dstAgent, { recursive: true });
  for (const name of fs.readdirSync(srcAgent, { withFileTypes: true })) {
    if (name.isFile()) {
      copyFile(path.join(srcAgent, name.name), path.join(dstAgent, name.name));
    }
  }

  // Filtered agents
  const agentsSrc = path.join(srcAgent, 'agents');
  if (pathExists(agentsSrc)) {
    for (const id of profile.agents) {
      const f = path.join(agentsSrc, `${id}.md`);
      if (pathExists(f)) copyFile(f, path.join(dstAgent, 'agents', `${id}.md`));
    }
    log(`  .agent/agents/ (${profile.agents.length} filtered)`);
  }

  // Filtered skills (each skill is a directory)
  const skillsSrc = path.join(srcAgent, 'skills');
  if (pathExists(skillsSrc)) {
    for (const id of profile.skills) {
      const d = path.join(skillsSrc, id);
      if (pathExists(d)) copyDir(d, path.join(dstAgent, 'skills', id));
    }
    log(`  .agent/skills/ (${profile.skills.length} filtered)`);
  }

  // Filtered workflows
  const wfSrc = path.join(srcAgent, 'workflows');
  if (pathExists(wfSrc)) {
    for (const id of profile.workflows) {
      const f = path.join(wfSrc, `${id}.md`);
      if (pathExists(f)) copyFile(f, path.join(dstAgent, 'workflows', `${id}.md`));
    }
    log(`  .agent/workflows/ (${profile.workflows.length} filtered)`);
  }

  // Rules: copy whole dir (rules are universal)
  const rulesSrc = path.join(srcAgent, 'rules');
  if (pathExists(rulesSrc)) copyDir(rulesSrc, path.join(dstAgent, 'rules'));
}

module.exports = {
  id: 'antigravity',
  name: 'Antigravity',
  targetPaths: ['.agent/'],
  emit
};
