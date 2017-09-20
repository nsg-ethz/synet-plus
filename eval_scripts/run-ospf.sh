#!/usr/bin/env bash

PATH_TO_LOGS="logs"
SYNET_SCRIPT="python ./eval_scripts/ospf_eval.py"

TOPO=$1
VALUES=$2
SYN=$3
REQ_TYPE=$4
REQS=$5
FIXED=$6
RUN_ID=$7

BASE=$(basename $TOPO | sed 's/.graphml//')

LOG_FILE="$PATH_TO_LOGS/$BASE-$SYN-$REQ_TYPE-$REQS-$FIXED-$RUN_ID.txt"

echo "Running topology=$BASE syn_type=$SYN reqs_type=$REQ_TYPE num_reqs=$REQS fixed=$FIXED run-id=$RUN_ID"

START=$(date +%s)
stdbuf -oL $SYNET_SCRIPT --topo=$TOPO --values=$VALUES --syn=$SYN --type=$REQ_TYPE --reqsize=$REQS --fixed=$FIXED > $LOG_FILE
END=$(date +%s)

TIME=$((END-START))
echo "Total time: $TIME" >> $LOG_FILE
