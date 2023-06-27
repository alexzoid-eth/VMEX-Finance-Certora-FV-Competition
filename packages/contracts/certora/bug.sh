#!/bin/bash

# Create a bugX based on diff with AssetMappings_original.sol. Run from the root git directory

CONTRACT_FILE="./packages/contracts/contracts/protocol/lendingpool/AssetMappings.sol"
BUG_DIR="packages/contracts/certora/bugs"
BUG_FILE_NUMBER=$(printf "%s\n" ${BUG_DIR}/bug*.patch | sort -t 'g' -k 2n | tail -n 1 | tr -dc '0-9' | awk '{$1=$1+1; print}')
BUG_FILE_PATH="${BUG_DIR}/bug${BUG_FILE_NUMBER}.patch"

git diff master -- ${CONTRACT_FILE} > ${BUG_FILE_PATH}

git apply -R ${BUG_FILE_PATH}