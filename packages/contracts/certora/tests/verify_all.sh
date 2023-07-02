#!/bin/bash

# Verify specification and all injected bugs

for f in packages/contracts/certora/tests/bugs/*.patch
do
    filename=$(basename -- "$f")
    base="${filename%%.*}"

    # If base is "original", pass nothing
    # Else, extract the bug number and pass it
    if [[ "$base" == "original" ]]; then
        packages/contracts/certora/tests/verify_bug.sh
    else
        bug_number="${base#bug}"
        packages/contracts/certora/tests/verify_bug.sh "$bug_number"
    fi
done