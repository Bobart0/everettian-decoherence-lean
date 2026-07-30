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
lake env lean EverettianDecoherence/Approximation/ProjectorCommutator.lean
lake build EverettianDecoherence.Approximation.ProjectorCommutator
lake env lean EverettianDecoherence/Approximation/ApproximateRecordPreservation.lean
lake build EverettianDecoherence.Approximation.ApproximateRecordPreservation
lake env lean EverettianDecoherence/Audit/ApproximateRecordPreservation.lean
lake build EverettianDecoherence.Audit.ApproximateRecordPreservation
lake env lean EverettianDecoherence/Metrics/FiniteL2Comparison.lean
lake build EverettianDecoherence.Metrics.FiniteL2Comparison
lake env lean EverettianDecoherence/Approximation/OperatorNormProjectorCommutator.lean
lake build EverettianDecoherence.Approximation.OperatorNormProjectorCommutator
lake env lean EverettianDecoherence/Approximation/UniformRecordPreservation.lean
lake build EverettianDecoherence.Approximation.UniformRecordPreservation
lake env lean EverettianDecoherence/Audit/UniformRecordPreservation.lean
lake build EverettianDecoherence.Audit.UniformRecordPreservation
lake env lean EverettianDecoherence/Metrics/FiniteL2Triangle.lean
lake env lean EverettianDecoherence/Approximation/ComposedProjectorCommutator.lean
lake env lean EverettianDecoherence/Approximation/ComposedRecordPreservation.lean
lake env lean EverettianDecoherence/Audit/ComposedRecordPreservation.lean
lake env lean EverettianDecoherence/Approximation/IteratedProjectorCommutator.lean
lake env lean EverettianDecoherence/Approximation/IteratedRecordPreservation.lean
lake env lean EverettianDecoherence/Audit/IteratedRecordPreservation.lean
lake env lean EverettianDecoherence/Factorization/FiniteBipartiteCoordinates.lean
lake env lean EverettianDecoherence/Factorization/FiniteBipartiteFactorization.lean
lake env lean EverettianDecoherence/Audit/FiniteBipartiteFactorization.lean
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
