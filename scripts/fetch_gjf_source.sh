#!/bin/sh
# Download the TeX source of GJF (arXiv:1811.00589, only v1 exists) into literature/ (gitignored).
set -e
cd "$(dirname "$0")/.."
mkdir -p literature
curl -sL https://arxiv.org/e-print/1811.00589 | gunzip > literature/gjf-1811.00589.tex
echo "wrote literature/gjf-1811.00589.tex ($(wc -l < literature/gjf-1811.00589.tex) lines)"
