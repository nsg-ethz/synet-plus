#!/bin/bash

PATH_TO_CONFIGS="topos"
PATH_TO_LOGS="logs"
SYNET_SCRIPT="synet/ospf_test.py"

TOPO=$1
REQS=$2
FIXED=$3
RUN_ID=$4

BASE=$(basename $TOPO | sed 's/.graphml//')

LOG_FILE="$PATH_TO_LOGS/$BASE-$REQS-$FIXED-$RUN_ID.txt"

echo "Running $BASE $REQS $FIXED $RUN_ID"

START=$(date +%s)
stdbuf -oL python $SYNET_SCRIPT -f $TOPO -r $REQS --fixed=$FIXED > $LOG_FILE
END=$(date +%s)

TIME=$((END-START))
echo "Total time: $TIME" >> $LOG_FILE
