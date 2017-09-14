#!/bin/bash

NUM_REPEATS=1
NUM_PROCESSES=1
NUM_REQS=1
RANDPATHS=100
SEED=2160495024583726158


PATH_TO_TOPOS="topos/topozoo/"

echo "Running experiments"

find $PATH_TO_TOPOS -type f -name *.graphml | sort | while read line; do
	for reqs in 1 2 4 8 16 32;
    do
        for fixed in 0.00 0.25 0.50 0.75 1.00;
        do
            for RUN_ID in $(seq 1 $NUM_REPEATS);
            do
		        echo $line $reqs $RANDPATHS $fixed $SEED $RUN_ID
	        done
	    done
	done
done | xargs -n 6 -I{} -P $NUM_PROCESSES sh -c "sh run-topo.sh {}"
