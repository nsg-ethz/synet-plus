#!/usr/bin/env bash

PATH_TO_LOGS="ebgplogs"
SYNET_SCRIPT="python ./eval_scripts/new_ebgp_eval.py"

TOPO=$1
VALUES=$2
REQ_TYPE=$3
REQS=$4
FIXED=$5
SKETCH=$6
RUN_ID=$7

BASE=$(basename $TOPO | sed 's/.graphml//')

LOG_FILE="$PATH_TO_LOGS/$BASE-$SKETCH-$REQ_TYPE-$REQS-$FIXED-$RUN_ID.txt"

echo "Running topology=$BASE reqs_type=$REQ_TYPE num_reqs=$REQS fixed=$FIXED run-id=$RUN_ID"

START=$(date +%s)
stdbuf -oL $SYNET_SCRIPT $TOPO --values=$VALUES --type=$REQ_TYPE --reqsize=$REQS --fixed=$FIXED --sketch=$SKETCH> $LOG_FILE 2>&1
END=$(date +%s)

TIME=$((END-START))
echo "Total time: $TIME" >> $LOG_FILE
