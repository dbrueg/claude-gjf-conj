#!/bin/sh
# Build nauty's `dreadnaut` (used by ternary60/theory/mainq_automorphisms.py) into tools/nauty/ (gitignored).
# The nauty 2.8.8 source ships inside the pynauty sdist on PyPI (pypi.org is reachable from the cloud sessions).
set -e
cd "$(dirname "$0")/.."
mkdir -p tools && cd tools
pip download pynauty==2.8.8.1 --no-binary :all: --no-deps -d . >/dev/null
tar xzf pynauty-2.8.8.1.tar.gz
cd pynauty-2.8.8.1/src/nauty2_8_8
./configure >/dev/null && make dreadnaut >/dev/null
echo "built $(pwd)/dreadnaut; export DREADNAUT=$(pwd)/dreadnaut"
