#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
MODE="${1:-development}"

case "$MODE" in
  development|complete) ;;
  *)
    echo "usage: $0 [development|complete]" >&2
    exit 2
    ;;
esac

cd "$ROOT/lean"

if [[ "${CUBOID_SKIP_BUILD:-0}" != "1" ]]; then
  lake build
fi

AUDIT_OUTPUT="$(mktemp)"
trap 'rm -f "$AUDIT_OUTPUT"' EXIT
lake env lean Cuboid2/AxiomAudit.lean | tee "$AUDIT_OUTPUT"

CUSTOM_DECLS="$(grep -R -n -E '^[[:space:]]*(axiom|opaque)[[:space:]]' Cuboid2 || true)"
if [[ -n "$CUSTOM_DECLS" ]]; then
  echo "project-specific axiom/opaque declarations are forbidden:" >&2
  echo "$CUSTOM_DECLS" >&2
  exit 1
fi

REMAINING="$(grep -R -n -w sorry Cuboid2 || true)"
if [[ -n "$REMAINING" ]]; then
  echo "remaining Lean placeholders:"
  echo "$REMAINING"
else
  echo "remaining Lean placeholders: none"
fi

if [[ "$MODE" == "complete" ]]; then
  if [[ -n "$REMAINING" ]]; then
    echo "complete-mode audit failed: source placeholders remain" >&2
    exit 1
  fi
  if grep -q 'sorryAx' "$AUDIT_OUTPUT"; then
    echo "complete-mode audit failed: public theorem depends on sorryAx" >&2
    exit 1
  fi
fi

echo "Lean replay and axiom audit completed in $MODE mode"
