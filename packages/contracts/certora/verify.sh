#!/bin/bash

# Apply a bug, run prover and restore original file

git apply packages/contracts/certora/bugs/bug$1.patch
cd packages/contracts
certoraRun certora/confs/AssetMappings.conf
cd ../../
git apply -R packages/contracts/certora/bugs/bug$1.patch