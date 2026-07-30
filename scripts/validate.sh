#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."

before=$(git status --porcelain)
bash scripts/guard.sh
lake env lean EverettianDecoherence/Metrics/FiniteProfileBounds.lean
lake env lean EverettianDecoherence/Metrics/NormSquarePerturbation.lean
lake env lean EverettianDecoherence/Metrics/StateRecordPerturbation.lean
lake build EverettianDecoherence.Metrics.StateRecordPerturbation
lake env lean EverettianDecoherence/Audit/StateRecordPerturbation.lean
lake build EverettianDecoherence.Audit.StateRecordPerturbation
lake env lean EverettianDecoherence/Metrics/FiniteL2Bounds.lean
lake build EverettianDecoherence.Metrics.FiniteL2Bounds
lake env lean EverettianDecoherence/Metrics/OrthogonalRecordDecomposition.lean
lake build EverettianDecoherence.Metrics.OrthogonalRecordDecomposition
lake env lean EverettianDecoherence/Metrics/StateRecordDimensionFree.lean
lake build EverettianDecoherence.Metrics.StateRecordDimensionFree
lake env lean EverettianDecoherence/Audit/StateRecordDimensionFree.lean
lake build EverettianDecoherence.Audit.StateRecordDimensionFree
lake env lean EverettianDecoherence/Metrics/FiniteProfileL1.lean
lake env lean EverettianDecoherence/Metrics/RecordProfileL1.lean
lake build EverettianDecoherence.Metrics.RecordProfileL1
lake env lean EverettianDecoherence/Audit/RecordProfileL1.lean
lake build EverettianDecoherence.Audit.RecordProfileL1
lake env lean EverettianDecoherence/Core/UpstreamAPI.lean
lake env lean EverettianDecoherence/Audit/UpstreamAPIContract.lean
lake build EverettianDecoherence.Audit.UpstreamAPIContract
lake env lean EverettianDecoherence/Audit/MainResults.lean
lake env lean EverettianDecoherence.lean
lake build
git diff --check
after=$(git status --porcelain)
if [ "$before" != "$after" ]; then
  echo 'VALIDATION_MODIFIED_TRACKED_STATE=FAIL'
  exit 1
fi
echo 'VALIDATION_RESULT=PASS'
