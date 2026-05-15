#!/usr/bin/env bash

exec_found=0

if [[ $# -ge 1 ]]
then
  LIB_NAME=$1
  FIND_PATH=${2:-$LIB_NAME}
  EXCLUDE_PATH=$3
  if [[ -n "$EXCLUDE_PATH" ]]
  then
    # Exclude both the EXCLUDE_PATH directory subtree and its sibling barrel file
    # (e.g. excluding "Tests/Conformance" drops both "Tests/Conformance/**" and "Tests/Conformance.lean").
    LEAN_FILES=`find $FIND_PATH -name '*.lean' 2>/dev/null | grep -Ev "^${EXCLUDE_PATH}(/|\.lean$)"`
  else
    LEAN_FILES=`find $FIND_PATH -name '*.lean' 2>/dev/null`
  fi
  EXEC_FILES=`cat lakefile.lean | grep root | sed 's/root := .//g'`
  # build lean project with log
  echo "Building Lean project $LIB_NAME ..."
  lake build $LIB_NAME 2>&1 | tee build.log
  if [[ $? -ne 0 ]]
  then
    cat build.log
    exit 1
  fi
  for i in $LEAN_FILES
  do
   LEAN_MODULE=`echo $i | sed 's/\.\///g' | sed 's/\//./g' | sed 's/.lean//g'`
   RES=`cat build.log | grep -o "Built $LEAN_MODULE"`
   for j in $EXEC_FILES
    do
     if [[ $LEAN_MODULE = $j ]]
     then
      let "exec_found=1"
     fi
    done
   if [[ $RES = "" ]] && [ "$exec_found" -eq 0 ]
   then
     echo "Lean module $LEAN_MODULE NOT compiled !!!"
     exit 1
   fi
   let "exec_found=0"
  done
  # rm build log
  rm -rf build.log
else
cat <<EOF
 usage: check_lean_project_compilation.sh <LIB NAME> [<FIND PATH>] [<EXCLUDE PATH>]
   LIB NAME    : Lake target to build (e.g. Tests, Tests.Conformance)
   FIND PATH   : directory to walk for .lean files (default: LIB NAME)
   EXCLUDE PATH: subdirectory under FIND PATH to skip
EOF
  exit 1
fi
