#!/bin/bash

NUM_REPEATS=1
NUM_PROCESSES=1
NUM_REQS=1
GRID_SIZE=3

PATH_TO_TOPOS="topos"

echo "Running experiments"


find $PATH_TO_TOPOS -type f -name *.graphml | sort | while read line; do
	for reqs in $(seq 1 $NUM_REQS);
    do
        for fixed in 0.00 0.25 0.50 0.75 1.00;
        do
            for RUN_ID in $(seq 1 $NUM_REPEATS);
            do
		        echo $line $reqs $fixed $RUN_ID
	        done
	    done
	done
done | xargs -n 4 -I{} -P $NUM_PROCESSES sh -c "sh run-topo.sh {}"


for gridsize in $(seq 3 $GRID_SIZE);
do
    for reqs in $(seq 1 $NUM_REQS);
    do
        for fixed in 0.00 0.25 0.50 0.75 1.00;
        do
            for RUN_ID in $(seq 1 $NUM_REPEATS);
            do
		        echo $gridsize $reqs $fixed $RUN_ID
	        done
	    done
	done
done | xargs -n 4 -I{} -P $NUM_PROCESSES sh -c "sh run-grid.sh {}"



