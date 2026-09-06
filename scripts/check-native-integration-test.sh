#!/usr/bin/env bash
set -euo pipefail

checker=${1:-"$(dirname "$0")/check-native-integration.sh"}
repo_root=$(git -C "$(dirname "$checker")/.." rev-parse --show-toplevel)
source_manifest="$repo_root/docs/native-integration-manifest.tsv"
fixture_dir=$(mktemp -d)
trap 'rm -rf "$fixture_dir"' EXIT

FORMALOLP_ROOT="$repo_root" FORMALOLP_NATIVE_MANIFEST="$source_manifest" \
  "$checker" >/dev/null

# A changed digest must fail even when every path is still present.
tampered="$fixture_dir/tampered.tsv"
awk -F '\t' -v OFS='\t' '
  BEGIN { changed = 0 }
  /^[[:space:]]*#/ || /^[[:space:]]*$/ { print; next }
  !changed { $2 = "0000000000000000000000000000000000000000000000000000000000000000"; changed = 1 }
  { print }
' "$source_manifest" > "$tampered"
if FORMALOLP_ROOT="$repo_root" FORMALOLP_NATIVE_MANIFEST="$tampered" \
    "$checker" >/dev/null 2>&1; then
  printf 'tampered digest unexpectedly passed\n' >&2
  exit 1
fi

# Removing one declared row must fail the complete-scope check.  This catches
# accidental whitelist shrinkage even if all remaining hashes are correct.
omitted="$fixture_dir/omitted.tsv"
awk '
  BEGIN { removed = 0 }
  /^[[:space:]]*#/ || /^[[:space:]]*$/ { print; next }
  !removed { removed = 1; next }
  { print }
' "$source_manifest" > "$omitted"
if FORMALOLP_ROOT="$repo_root" FORMALOLP_NATIVE_MANIFEST="$omitted" \
    "$checker" >/dev/null 2>&1; then
  printf 'omitted manifest row unexpectedly passed\n' >&2
  exit 1
fi

printf 'native integration checker positive, tamper-negative, and omission-negative fixtures passed\n'
