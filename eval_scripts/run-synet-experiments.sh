#!/usr/bin/env bash

# Generate evaluation values for all given reqs
NUM_PROCESSES=20
NUM_REPEATS=10

for proto in "static" "ospf";
do
    for n in 5 6 7 8;
    do
        for RUN_ID in $(seq 1 $NUM_REPEATS);
        do
            echo $n $proto $RUN_ID
        done

    done
done | xargs -n 3 -I{} -P $NUM_PROCESSES sh -c "sh ./eval_scripts/run-synet.sh {}"
