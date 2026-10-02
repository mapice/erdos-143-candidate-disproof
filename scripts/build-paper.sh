#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/../paper"
mkdir -p build
for pass in 1 2; do
  pdflatex -interaction=nonstopmode -halt-on-error -output-directory=build erdos143-candidate.tex > "build/pass-${pass}.txt"
done
if grep -Eq 'LaTeX Warning: (There were undefined references|Reference .* undefined|Label\(s\) may have changed)' build/erdos143-candidate.log; then
  printf 'Unresolved LaTeX references; inspect paper/build/erdos143-candidate.log\n' >&2
  exit 1
fi
printf 'Paper compiled: paper/build/erdos143-candidate.pdf\n'
