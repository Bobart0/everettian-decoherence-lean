#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."

required=(
  .editorconfig .gitattributes .gitignore .github/copilot-instructions.md
  .github/workflows/lean.yml AGENTS.md CLAUDE.md CHANGELOG.md CITATION.cff
  CLAIM_MATRIX.md CONTRIBUTING.md LICENSE MILESTONES.md README.md SORRY_BUDGET
  VERSION lakefile.toml lean-toolchain EverettianDecoherence.lean
  EverettianDecoherence/AGENTS.md EverettianDecoherence/Core/UpstreamAPI.lean
  EverettianDecoherence/Audit/AGENTS.md
  EverettianDecoherence/Audit/UpstreamAPIContract.lean
  EverettianDecoherence/Audit/MainResults.lean docs/AGENTS.md docs/AGENT_WORKFLOW.md
  docs/API_STABILITY.md docs/ARCHITECTURE.md docs/BOOTSTRAP_AUDIT.md
  docs/DECISION_LOG.md docs/DEPENDENCY_POLICY.md docs/GITHUB_SETTINGS.md
  docs/PROGRAM_STATUS.md docs/REPRODUCIBILITY.md docs/SCOPE_AND_LIMITATIONS.md
  scripts/AGENTS.md scripts/check_agent_harness.sh scripts/check_bilingual_docs.sh
  scripts/check_dependency_pins.sh scripts/check_line_limits.sh
  scripts/check_repository_terminology.sh scripts/check_upstream_api_boundary.sh
  scripts/guard.sh scripts/validate.sh
)

status=0
for file in "${required[@]}"; do
  if [ ! -f "$file" ]; then
    echo "REQUIRED_FILE_MISSING=$file"
    status=1
  fi
done

for file in scripts/*.sh; do
  if [ ! -x "$file" ]; then
    echo "SCRIPT_NOT_EXECUTABLE=$file"
    status=1
  fi
done

grep -qF 'AGENTS.md' CLAUDE.md || { echo 'CLAUDE_AGENTS_REFERENCE_MISSING'; status=1; }
grep -qF 'AGENTS.md' .github/copilot-instructions.md || { echo 'COPILOT_AGENTS_REFERENCE_MISSING'; status=1; }
grep -qF 'bash scripts/guard.sh' .github/workflows/lean.yml || { echo 'CI_GUARD_CALL_MISSING'; status=1; }
grep -qF 'lake build' .github/workflows/lean.yml || { echo 'CI_BUILD_CALL_MISSING'; status=1; }
grep -qF 'EverettianDecoherence/Audit/UpstreamAPIContract.lean' .github/workflows/lean.yml || { echo 'CI_CONTRACT_CALL_MISSING'; status=1; }
grep -qF 'main' .github/workflows/lean.yml || { echo 'CI_MAIN_BRANCH_MISSING'; status=1; }
[ "$(tr -d '[:space:]' < SORRY_BUDGET)" = '0' ] || { echo 'SORRY_BUDGET_NOT_ZERO'; status=1; }

if [ "$status" -eq 0 ]; then
  echo 'AGENT_HARNESS=PASS'
else
  echo 'AGENT_HARNESS=FAIL'
  exit 1
fi
