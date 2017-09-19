#!/usr/bin/env bash

# Generate evaluation values for all given reqs
NUM_PROCESSES=15


PATH_TO_TOPOS="topos/*/"

find $PATH_TO_TOPOS -type f -name *.graphml | sort | while read line; do
    if [[ $line =~ topos/small.* ]]; then
        echo $line
    fi
    if [[ $line =~ topos/mid.* ]]; then
        echo $line
    fi
    if [[ $line =~ topos/large.* ]]; then
        echo $line
    fi
done | xargs -n 1 -I{} -P $NUM_PROCESSES sh -c "time python eval_scripts/ospf_generate_reqs.py -f {}"

