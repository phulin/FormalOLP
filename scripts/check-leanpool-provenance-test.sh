#!/usr/bin/env bash
set -euo pipefail

checker=${1:-"$(dirname "$0")/check-leanpool-provenance.sh"}
fixture=$(mktemp -d)
trap 'rm -rf "$fixture"' EXIT
mkdir -p "$fixture/LeanPool" "$fixture/third_party/lean-pool"
printf 'fixture source\n' > "$fixture/LeanPool/Example.lean"
printf 'fixture notice\n' > "$fixture/third_party/lean-pool/LICENSE"
source_hash=$(sha256sum "$fixture/LeanPool/Example.lean" | awk '{print $1}')
notice_hash=$(sha256sum "$fixture/third_party/lean-pool/LICENSE" | awk '{print $1}')
manifest="$fixture/docs-lean-pool-manifest.tsv"
printf '%s\n' '# path	original_sha256	current_sha256	pool_commit	license	upstream_sha	modifications' > "$manifest"
printf 'LeanPool/Example.lean\t%s\t%s\ttest\tApache-2.0\tn/a\tnone\n' "$source_hash" "$source_hash" >> "$manifest"
printf 'third_party/lean-pool/LICENSE\t%s\t%s\ttest\tApache-2.0\tn/a\tnone\n' "$notice_hash" "$notice_hash" >> "$manifest"

# The checker supports an explicit temporary manifest for this fixture.
FORMALOLP_ROOT="$fixture" FORMALOLP_MANIFEST="$manifest" "$checker" >/dev/null

printf 'tampered source\n' >> "$fixture/LeanPool/Example.lean"
if FORMALOLP_ROOT="$fixture" FORMALOLP_MANIFEST="$manifest" "$checker" >/dev/null 2>&1; then
  printf 'negative fixture unexpectedly passed after tampering\n' >&2
  exit 1
fi
printf 'provenance checker positive and tamper-negative fixtures passed\n'
