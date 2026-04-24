function filterAgentRoutingTable(md, keepSet) {
  // Find the "## Agent Routing" section and filter its table rows.
  const lines = md.split(/\r?\n/);
  const out = [];
  let inRouting = false;
  let sawTableHeader = false;
  let pastTable = false;

  for (let i = 0; i < lines.length; i++) {
    const line = lines[i];
    if (/^##\s+Agent Routing\s*$/.test(line)) {
      inRouting = true; sawTableHeader = false; pastTable = false;
      out.push(line);
      continue;
    }
    if (inRouting && /^##\s+/.test(line)) {
      inRouting = false; pastTable = true;
      out.push(line);
      continue;
    }
    if (inRouting && /^\|/.test(line)) {
      if (!sawTableHeader) {
        out.push(line);
        // Next line is expected separator ("|---|---|..."); keep it too.
        sawTableHeader = line.includes('---') ? sawTableHeader : true;
        continue;
      }
      if (/^\|\s*-+/.test(line)) { out.push(line); continue; } // separator
      // Data row — keep only if references a kept agent
      const m = line.match(/`([a-z-]+)\.md`/);
      if (m && keepSet.has(m[1])) out.push(line);
      continue;
    }
    out.push(line);
  }
  return out.join('\n');
}

function stripSlashCommandsSection(md) {
  const lines = md.split(/\r?\n/);
  const out = [];
  let inSection = false;
  for (let i = 0; i < lines.length; i++) {
    const line = lines[i];
    if (/^##\s+Available Slash Commands\s*$/.test(line)) { inSection = true; continue; }
    if (inSection && /^##\s+/.test(line)) { inSection = false; /* fall through to push */ }
    if (!inSection) out.push(line);
  }
  return out.join('\n');
}

module.exports = { filterAgentRoutingTable, stripSlashCommandsSection };
