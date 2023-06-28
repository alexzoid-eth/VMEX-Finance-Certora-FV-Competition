#!/bin/bash

# Apply a bug, run prover and restore original file. Run from the root git directory
# verify_bug.sh [bugN]

BUG_NUMBER=$1
MSG="$@"
git apply packages/contracts/certora/tests/bugs/bug${BUG_NUMBER}.patch
cd packages/contracts
shift 1  # shift arguments to exclude the first one
certoraRun certora/confs/AssetMappings.conf --msg "bug${MSG}" "$@" # pass all other parameters to certoraRun
cd ../../
git apply -R packages/contracts/certora/tests/bugs/bug${BUG_NUMBER}.patch
