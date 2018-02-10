#!/usr/bin/env bash

PATH_TO_LOGS="synetlogs"
SYNET_SCRIPT="python ./eval_scripts/synet_compare.py"

TOPO=$1
PROTO=$2
RUN_ID=$3

LOG_FILE="$PATH_TO_LOGS/$TOPO-$PROTO-$RUN_ID.txt"

echo "Running topology=$TOPOx$TOPO with protocol=$PROTO run-id=$RUN_ID"

START=$(date +%s)
stdbuf -oL $SYNET_SCRIPT -n=$TOPO -p=$PROTO > $LOG_FILE 2>&1
END=$(date +%s)

TIME=$((END-START))
echo "Total time: $TIME" >> $LOG_FILE
