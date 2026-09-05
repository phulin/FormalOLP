#!/usr/bin/env bash
set -euo pipefail

# Verify the byte-level inventory for a copied Lean Pool closure.  The manifest
# is intentionally kept outside the vendored tree so that adding or removing a
# source file cannot silently bypass the provenance review.

repo_root=${FORMALOLP_ROOT:-$(git rev-parse --show-toplevel)}
manifest=${FORMALOLP_MANIFEST:-"$repo_root/docs/lean-pool-manifest.tsv"}
vendor_root="$repo_root/LeanPool"

if [[ ! -d "$vendor_root" ]]; then
  printf 'LeanPool directory is absent; no vendor inventory to verify.\n'
  exit 0
fi
if [[ ! -f "$manifest" ]]; then
  printf 'missing provenance manifest: %s\n' "$manifest" >&2
  exit 1
fi

declare -A listed_hashes
while IFS=$'\t' read -r path original_sha256 current_sha256 pool_sha license upstream_sha modifications; do
  [[ -z "$path" || "${path:0:1}" == "#" ]] && continue
  if [[ -z "$original_sha256" || -z "$current_sha256" || -z "$pool_sha" || -z "$license" || -z "$upstream_sha" || -z "$modifications" ]]; then
    printf 'incomplete provenance row for %s\n' "$path" >&2
    exit 1
  fi
  if [[ ("$path" != LeanPool/* && "$path" != third_party/lean-pool/LICENSE && "$path" != third_party/lean-pool/NOTICE && "$path" != third_party/lean-pool/NOTICE.extra.yml) || "$path" == */ || "$path" == *..* ]]; then
    printf 'invalid vendored path: %s\n' "$path" >&2
    exit 1
  fi
  if [[ -n "${listed_hashes[$path]+x}" ]]; then
    printf 'duplicate provenance row: %s\n' "$path" >&2
    exit 1
  fi
  listed_hashes["$path"]="$current_sha256"
  file="$repo_root/$path"
  [[ -f "$file" ]] || { printf 'manifest path is absent: %s\n' "$path" >&2; exit 1; }
  actual=$(sha256sum "$file" | awk '{print $1}')
  [[ "$actual" == "$current_sha256" ]] || {
    printf 'hash mismatch for %s: manifest %s, actual %s\n' "$path" "$current_sha256" "$actual" >&2
    exit 1
  }
  if [[ "$original_sha256" != "$current_sha256" && "$modifications" == "none" ]]; then
    printf 'modified file lacks a modification record: %s\n' "$path" >&2
    exit 1
  fi
done < "$manifest"

while IFS= read -r file; do
  path=${file#"$repo_root/"}
  [[ -n "${listed_hashes[$path]+x}" ]] || {
    printf 'vendored file is absent from manifest: %s\n' "$path" >&2
    exit 1
  }
done < <(find "$vendor_root" -type f -print | sort)

for notice in "$repo_root/third_party/lean-pool/LICENSE" "$repo_root/third_party/lean-pool/NOTICE" "$repo_root/third_party/lean-pool/NOTICE.extra.yml"; do
  [[ -f "$notice" ]] || continue
  path=${notice#"$repo_root/"}
  [[ -n "${listed_hashes[$path]+x}" ]] || {
    printf 'license notice is absent from manifest: %s\n' "$path" >&2
    exit 1
  }
done

printf 'Lean Pool provenance inventory is complete: %d files.\n' "${#listed_hashes[@]}"
