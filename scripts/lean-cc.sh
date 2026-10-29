#!/bin/sh
# Use the host libc for system crypto, while keeping Lean's matching C++/uv libraries.
# -L affects library lookup; LIBRARY_PATH would also select Lean's older startup objects.
set -eu
plutus_lean_root=${LEAN_SYSROOT:-$(lean --print-prefix)}
exec cc "-L$plutus_lean_root/lib" "$@"
