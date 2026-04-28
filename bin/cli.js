#!/usr/bin/env node

const fs = require('fs');
const path = require('path');

const args = process.argv.slice(2);
const command = args[0];

const COLORS = {
  reset: '\x1b[0m',
  green: '\x1b[32m',
  cyan: '\x1b[36m',
  yellow: '\x1b[33m',
  red: '\x1b[31m',
  bold: '\x1b[1m'
};

function log(msg, color = '') {
  console.log(`${color}${msg}${COLORS.reset}`);
}

function copyDir(src, dest) {
  fs.mkdirSync(dest, { recursive: true });
  const entries = fs.readdirSync(src, { withFileTypes: true });

  for (const entry of entries) {
    const srcPath = path.join(src, entry.name);
    const destPath = path.join(dest, entry.name);

    if (entry.isDirectory()) {
      copyDir(srcPath, destPath);
    } else {
      fs.copyFileSync(srcPath, destPath);
    }
  }
}

function init(targetDir = '.') {
  const packageDir = path.dirname(__dirname);
  const agentSrc = path.join(packageDir, '.agent');
  const agentDest = path.join(targetDir, '.agent');

  log('\n🚀 VLSI Kit - AI Agent Kit for VLSI Development\n', COLORS.cyan + COLORS.bold);

  // Check if .agent already exists
  if (fs.existsSync(agentDest)) {
    log('⚠️  .agent directory already exists!', COLORS.yellow);
    log('   Use --force to overwrite.\n', COLORS.yellow);

    if (!args.includes('--force')) {
      process.exit(1);
    }
    log('   Overwriting existing .agent directory...\n', COLORS.yellow);
    fs.rmSync(agentDest, { recursive: true, force: true });
  }

  // Copy .agent directory
  log('📁 Copying VLSI agent files...', COLORS.cyan);
  copyDir(agentSrc, agentDest);

  // Copy GEMINI.md to root if it doesn't exist
  const geminiSrc = path.join(agentSrc, 'rules', 'GEMINI.md');
  const geminiDest = path.join(targetDir, 'GEMINI.md');

  if (!fs.existsSync(geminiDest)) {
    log('📄 Creating GEMINI.md in project root...', COLORS.cyan);
    fs.copyFileSync(geminiSrc, geminiDest);
  }

  // Copy GitHub Copilot instructions to .github/ if it doesn't exist
  const copilotSrc = path.join(agentSrc, 'rules', 'copilot-instructions.md');
  const githubDir = path.join(targetDir, '.github');
  const copilotDest = path.join(githubDir, 'copilot-instructions.md');

  if (fs.existsSync(copilotSrc) && !fs.existsSync(copilotDest)) {
    log('📄 Creating .github/copilot-instructions.md...', COLORS.cyan);
    fs.mkdirSync(githubDir, { recursive: true });
    fs.copyFileSync(copilotSrc, copilotDest);
  }

  log('\n✅ VLSI Kit initialized successfully!\n', COLORS.green + COLORS.bold);
  log('📦 Installed:', COLORS.cyan);
  log('   • 14 Specialist Agents');
  log('   • 18 VLSI Skills');
  log('   • 10 Workflows');
  log('   • GEMINI.md (Gemini CLI)');
  log('   • .github/copilot-instructions.md (GitHub Copilot Chat)\n');
  log('📖 Usage:', COLORS.cyan);
  log('   • Use @agent-name to invoke agents');
  log('   • Use /workflow to run workflows');
  log('   • Example: @rtl-designer or /design\n');
  log('🔗 More info: https://github.com/kishore-damam/vlsi-kit\n');
}

function showHelp() {
  log('\n🔧 VLSI Agent Kit CLI\n', COLORS.cyan + COLORS.bold);
  log('Usage: vlsi-agkit <command> [options]\n');
  log('Commands:');
  log('  init [--force]   Initialize VLSI Agent Kit in current directory');
  log('  help             Show this help message');
  log('  version          Show version\n');
  log('Examples:');
  log('  npx @kishore-damam/vlsi-agkit init');
  log('  vlsi-agkit init --force\n');
}

function showVersion() {
  const pkg = require('../package.json');
  log(`VLSI Agent Kit v${pkg.version}`);
}

// Main
switch (command) {
  case 'init':
    init(args[1] || '.');
    break;
  case 'version':
  case '-v':
  case '--version':
    showVersion();
    break;
  case 'help':
  case '-h':
  case '--help':
  default:
    showHelp();
    break;
}
