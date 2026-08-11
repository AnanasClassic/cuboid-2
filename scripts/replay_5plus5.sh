#!/usr/bin/env bash
set -euo pipefail

python_bin="${PYTHON_BIN:-python3}"
tmp_dir="$(mktemp -d)"
trap 'rm -rf "$tmp_dir"' EXIT

curl -fsSL https://arxiv.org/src/2601.04240 -o "$tmp_dir/source.tar"
actual="$(sha256sum "$tmp_dir/source.tar" | cut -d' ' -f1)"
expected="96d7e4b7d3cb75af238a0ca8cd143a8d555daf6ac9e8c2cc94a099b5aea04760"
test "$actual" = "$expected"
tar -xf "$tmp_dir/source.tar" -C "$tmp_dir"

# The second code block is the complete discriminant/Sturm certificate.
awk '/\\begin\{code\}/{n++;next} /\\end\{code\}/{if(n==2) exit} n==2' \
  "$tmp_dir/cuboid2_5+5.tex" | "$python_bin" -

