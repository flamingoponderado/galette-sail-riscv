#!/bin/sh
# Regenerate sail/rv64d.v, sail/rv64d_types.v and sail/riscv_extras.v from
# deps/sail-riscv with the Sail in opam switch galette-sail, then regenerate
# theories/Regfile.v.  Usage: scripts/gen-sail.sh [--check]
set -e
cd "$(dirname "$0")/.."
eval "$(opam env --switch=galette-sail --set-switch)"
cmake -S deps/sail-riscv -B _sailbuild -DCMAKE_BUILD_TYPE=RelWithDebInfo \
  -DDOWNLOAD_GMP=FALSE -DDOWNLOAD_JSONCONS=FALSE -DDOWNLOAD_CLI11=FALSE -DDOWNLOAD_ASIO=FALSE > /dev/null
cmake --build _sailbuild --target generated_rocq_rv64d
out=sail
if [ "$1" = "--check" ]; then out=$(mktemp -d); fi
cp _sailbuild/rocq/rv64d.v _sailbuild/rocq/rv64d_types.v "$out"/
cp deps/sail-riscv/handwritten_support/riscv_extras.v "$out"/
python3 scripts/gen-regfile.py "$out"/rv64d_types.v > "$out"/Regfile.v
if [ "$1" = "--check" ]; then
  for f in rv64d.v rv64d_types.v riscv_extras.v; do cmp "$out/$f" "sail/$f"; done
  cmp "$out/Regfile.v" theories/Regfile.v
  echo "generated files are up to date"
else
  mv sail/Regfile.v theories/Regfile.v
fi
