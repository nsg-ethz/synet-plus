#!/bin/bash

#PATH_TO_CONFIGS="topos/topozoo"
PATH_TO_LOGS="logs"
SYNET_SCRIPT="synet/drivers/ospf_driver.py"

TOPO=$1
REQS=$2
RANDPATHS=$3
FIXED=$4
SEED=$5
RUN_ID=$6

BASE=$(basename $TOPO | sed 's/.graphml//')

LOG_FILE="$PATH_TO_LOGS/$BASE-$REQS-$FIXED-$RUN_ID.txt"

echo "Running topology=$BASE num_reqs=$REQS fixed=$FIXED seed=$SEED run-id=$RUN_ID"

START=$(date +%s)
stdbuf -oL python -O $SYNET_SCRIPT -f $TOPO -r $REQS -p $RANDPATHS --fixed=$FIXED --seed=$SEED > $LOG_FILE
END=$(date +%s)

TIME=$((END-START))
echo "Total time: $TIME" >> $LOG_FILE
