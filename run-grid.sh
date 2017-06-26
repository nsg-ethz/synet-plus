#!/bin/bash

PATH_TO_CONFIGS="topos"
PATH_TO_LOGS="logs"
SYNET_SCRIPT="synet/ospf_test.py"

GRID=$1
REQS=$2
FIXED=$3
RUN_ID=$4

LOG_FILE="$PATH_TO_LOGS/grid$GRID-$REQS-$FIXED-$RUN_ID.txt"

echo "Running Grid$GRIDx$GRID $REQS $FIXED $RUN_ID"

START=$(date +%s)
stdbuf -oL python $SYNET_SCRIPT -s $GRID -r $REQS --fixed=$FIXED > $LOG_FILE
END=$(date +%s)

TIME=$((END-START))
echo "Total time: $TIME" >> $LOG_FILE
