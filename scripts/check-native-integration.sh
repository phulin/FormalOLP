#!/usr/bin/env bash
set -euo pipefail

# Check the small, native OLP integrations.  The historical Lean Pool
# checkout is deliberately not a build input; this check only validates the
# native files named in the review manifest and their source records.

repo_root=${FORMALOLP_ROOT:-$(git rev-parse --show-toplevel)}
manifest=${FORMALOLP_NATIVE_MANIFEST:-"$repo_root/docs/native-integration-manifest.tsv"}

fail() {
  printf 'native integration check: %s\n' "$1" >&2
  exit 1
}

[[ -d "$repo_root" ]] || fail "repository root is absent: $repo_root"
[[ -f "$manifest" ]] || fail "missing native integration manifest: $manifest"

[[ ! -d "$repo_root/LeanPool" ]] || \
  fail "active LeanPool source directory remains; use the archived reference record"

if imports=$(rg -n --glob '*.lean' \
    '^[[:space:]]*import[[:space:]]+LeanPool([.]|$)' \
    "$repo_root/FormalOLP" "$repo_root/FormalOLP.lean" "$repo_root/test" 2>/dev/null || true); then
  [[ -z "$imports" ]] || fail "active source imports LeanPool:\n$imports"
fi

declare -A seen
declare -A expected_kind=(
  [FormalOLP/SetsFunctionsRelations.lean]=existing-scaffold
  [FormalOLP/FirstOrderLogic/SemanticNotions.lean]=existing-scaffold
  [FormalOLP/SetsFunctionsRelations/Functions.lean]=native-adaptation
  [FormalOLP/Computability/RelativeComputability.lean]=native-adaptation
  [FormalOLP/Computability/TuringReducibility.lean]=native-adaptation
  [FormalOLP/PropositionalLogic/Syntax.lean]=native-adaptation
  [FormalOLP/IntuitionisticLogic/Kripke.lean]=native-adaptation
  [FormalOLP/IntuitionisticLogic/Soundness.lean]=native-adaptation
  [FormalOLP/SetTheory/Basic.lean]=native-adaptation
  [FormalOLP/NormalModalLogic/Syntax.lean]=native-adaptation
  [FormalOLP/NormalModalLogic/Semantics.lean]=native-adaptation
  [FormalOLP/NormalModalLogic/Soundness.lean]=native-adaptation
  [FormalOLP/AppliedModalLogic/Epistemic.lean]=native-olp
  [FormalOLP/Counterfactuals/Sphere.lean]=native-olp
  [FormalOLP/Incompleteness/RobinsonArithmetic.lean]=native-olp
  [FormalOLP/IntuitionisticLogic/NaturalDeduction.lean]=native-olp
  [FormalOLP/ModelTheory/Basic.lean]=native-mathlib
  [FormalOLP/ProofTheory/NaturalDeduction.lean]=native-olp
  [FormalOLP/PropositionalLogic/Semantics.lean]=native-olp
  [FormalOLP/SecondOrderLogic/Semantics.lean]=native-olp
  [FormalOLP/TuringMachines/Basic.lean]=native-mathlib
  [FormalOLP/Methods/Induction.lean]=native-olp
  [FormalOLP/ManyValuedLogic/Kleene.lean]=native-olp
  [FormalOLP/LambdaCalculus/DeBruijn.lean]=native-olp
)
rows=0

check_reference() {
  local ref=$1
  local label=$2
  case "$ref" in
    ""|/*|../*|*/../*|./*|*/./*)
      fail "invalid $label path: $ref"
      ;;
  esac
  [[ -f "$repo_root/$ref" ]] || fail "$label file is absent: $ref"
}

check_references() {
  local refs=$1
  local label=$2
  local ref
  local -a paths
  IFS=';' read -r -a paths <<< "$refs"
  ((${#paths[@]} > 0)) || fail "empty $label reference list"
  for ref in "${paths[@]}"; do
    check_reference "$ref" "$label"
  done
}

while IFS=$'\t' read -r native_path digest source_kind attribution_source olp_source ledger extra; do
  [[ -z "$native_path" || "${native_path:0:1}" == "#" ]] && continue
  [[ -z "$extra" ]] || fail "too many fields in manifest row: $native_path"
  [[ -n "$digest" && -n "$source_kind" && -n "$attribution_source" && -n "$olp_source" && -n "$ledger" ]] || \
    fail "incomplete manifest row: $native_path"
  [[ "$native_path" == FormalOLP/* ]] || fail "native path is outside FormalOLP/: $native_path"
  case "$native_path" in
    */|*..*|/*) fail "invalid native path: $native_path" ;;
  esac
  [[ "$digest" =~ ^[[:xdigit:]]{64}$ ]] || fail "invalid SHA-256 for $native_path"
  [[ -n "${expected_kind[$native_path]+present}" ]] || \
    fail "manifest row is outside the declared integration scope: $native_path"
  [[ "$source_kind" == "${expected_kind[$native_path]}" ]] || \
    fail "wrong source kind for $native_path: $source_kind (expected ${expected_kind[$native_path]})"
  [[ -z "${seen[$native_path]+present}" ]] || fail "duplicate manifest row: $native_path"
  seen["$native_path"]=1

  native_file="$repo_root/$native_path"
  [[ -f "$native_file" ]] || fail "native file is absent: $native_path"
  actual=$(sha256sum "$native_file" | awk '{print $1}')
  [[ "$actual" == "$digest" ]] || \
    fail "hash mismatch for $native_path (manifest $digest, actual $actual)"

  check_references "$attribution_source" attribution
  check_reference "$olp_source" OLP-source
  check_reference "$ledger" provenance-ledger
  if [[ "$source_kind" == native-adaptation ]]; then
    for notice in \
      third_party/lean-pool/LICENSE \
      third_party/lean-pool/NOTICE \
      third_party/lean-pool/NOTICE.extra.yml; do
      case ";$attribution_source;" in
        *";$notice;"*) ;;
        *) fail "native adaptation omits preserved license notice: $native_path ($notice)" ;;
      esac
    done
  fi
  rows=$((rows + 1))
done < "$manifest"

(( rows > 0 )) || fail "manifest has no native integration rows"
for native_path in "${!expected_kind[@]}"; do
  [[ -n "${seen[$native_path]+present}" ]] || \
    fail "manifest omits declared integration file: $native_path"
done
printf 'native integration provenance verified: %d files\n' "$rows"
