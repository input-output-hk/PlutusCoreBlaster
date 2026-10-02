#!/usr/bin/env bash
set -euo pipefail
if [[ $# -ne 1 ]]; then
  echo "usage: $0 <project name>" >&2
  exit 2
fi
checker="$(dirname "$0")/check_lean_project_compilation.sh"
"$checker" "$1"
"$checker" Cryptograph
"$checker" Tests Tests Tests/Conformance
"$checker" Lemmas
