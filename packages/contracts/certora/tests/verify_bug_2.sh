#!/bin/bash

# Apply a bug, run prover and restore original file
# Run from the root git directory. Run without paramenter to not apply any patches
# Examples:
#    ./packages/contracts/certora/tests/verify_bug.sh --rule initializeCalledOnce
#    ./packages/contracts/certora/tests/verify_bug.sh 2
#    ./packages/contracts/certora/tests/verify_bug.sh 3 --rule initializeCalledOnce

MSG="[run] $@"
FILE_NAME="original"

# Check if bug number is not empty, else set to 'original'
if [[ $1 =~ ^[0-9]+$ ]]
then
  FILE_NAME="bug$1"
  shift 1  # shift arguments to exclude the first one
  MSG="[prove $FILE_NAME] $@"
fi

# Apply injected bug patch
git apply packages/contracts/certora/tests/bugs2/${FILE_NAME}.patch

# Pass the rest parameters to certoraRun
cd packages/contracts
certoraRun certora/confs/AssetMappings2.conf --msg "${MSG}" "$@" 
cd ../../

# Restore original
git apply -R packages/contracts/certora/tests/bugs2/${FILE_NAME}.patch
