#!/usr/bin/env bash

exec_found=0
if [[ $# -lt 1 || $# -gt 2 ]]
then
cat <<EOF
 usage: check_lean_project_with_lemmas.sh <PROJECT NAME> [<EXCLUDE_PATTERN>]

   <EXCLUDE_PATTERN>  optional ERE; matching .lean files are not
                      required to appear in the build log (use this
                      to skip files that are only built by another
                      target, e.g. test files built via 'lake test').
EOF
  exit 1
fi

PROJECT_NAME=$1
EXCLUDE_PATTERN=${2:-}
LEMMAS_FOLDER="Lemmas"
LEAN_FILES=`find $PROJECT_NAME -name '*.lean' 2>/dev/null`
if [[ -n "$EXCLUDE_PATTERN" ]]
then
  LEAN_FILES=`echo "$LEAN_FILES" | grep -Ev "$EXCLUDE_PATTERN"`
fi
EXEC_FILES=`cat lakefile.lean | grep root | sed 's/root := .//g'`
# build lean project with log
echo "Building Lean project $PROJECT_NAME ..."
lake build $PROJECT_NAME 2>&1 | tee build.log
if [[ $? -ne 0 ]]
then
  cat build.log
  exit 1
fi
# build lemmas
lake build $LEMMAS_FOLDER 2>&1 | tee -a build.log
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
