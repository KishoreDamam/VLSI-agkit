const profiles = require('./profiles');
const adapters = require('./adapters');

function parseToolsCsv(csv) {
  if (!csv || !csv.trim()) throw new Error('--tools requires at least one tool');
  const ids = csv.split(',').map(s => s.trim()).filter(Boolean);
  for (const id of ids) {
    if (!adapters.VALID_IDS.has(id)) {
      throw new Error(`Unknown tool "${id}". Valid: ${[...adapters.VALID_IDS].join(', ')}`);
    }
  }
  return ids;
}

function validateNonInteractiveFlags({ role, tools }) {
  if (!role) throw new Error('--role is required in non-interactive mode');
  if (!tools) throw new Error('--tools is required in non-interactive mode');
  if (!profiles.VALID_IDS.has(role)) {
    throw new Error(
      `Unknown role "${role}". Valid: ${[...profiles.VALID_IDS].join(', ')}`
    );
  }
  parseToolsCsv(tools);
}

async function promptInteractive({ defaultDir = '.' } = {}) {
  const { select, checkbox, input } = require('@inquirer/prompts');

  const role = await select({
    message: 'Select your role profile:',
    choices: profiles.list().map(p => ({
      name: `${p.name} — ${p.description}`,
      value: p.id
    })),
    default: 'full-stack'
  });

  const tools = await checkbox({
    message: 'Select tools to install for:',
    choices: adapters.list().map(a => ({ name: a.name, value: a.id })),
    required: true,
    validate: (v) => v.length > 0 || 'Pick at least one tool'
  });

  const dir = await input({
    message: 'Target directory:',
    default: defaultDir
  });

  return { role, tools, dir };
}

async function promptOverwrite(pathLabel) {
  const { confirm } = require('@inquirer/prompts');
  return confirm({
    message: `${pathLabel} already exists — overwrite?`,
    default: false
  });
}

module.exports = {
  parseToolsCsv,
  validateNonInteractiveFlags,
  promptInteractive,
  promptOverwrite
};
