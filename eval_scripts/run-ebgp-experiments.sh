#!/usr/bin/env bash

# Generate evaluation values for all given reqs
NUM_PROCESSES=20
NUM_REPEATS=1


PATH_TO_TOPOS="topos/*/"
#topos/small/Arnes topos/small/Bics topos/small/Canerie topos/small/Renater2008 topos/small/CrlNetworkServices;
#topos/mid/Columbus topos/mid/Esnet topos/mid/Latnet topos/mid/Sinet topos/mid/Uninett2011
#topos/large/Cogentco topos/large/Colt	topos/large/GtsCe  topos/large/TataNld topos/large/UsCarrier


for file in topos/small/Arnes topos/small/Bics topos/small/Canerie topos/small/Renater2008 topos/small/CrlNetworkServices topos/mid/Columbus topos/mid/Esnet topos/mid/Latnet topos/mid/Sinet topos/mid/Uninett2011 topos/large/Cogentco topos/large/Colt topos/large/GtsCe topos/large/TataNld topos/large/UsCarrier;
do
topo="${file}.graphml"
values="${file}_ospf_reqs.py "
    for reqs in 1 2 4 8 16;
    do
        for req_type in "order" "simple";
        do
            for fixed in "0";
            do
                for RUN_ID in $(seq 1 $NUM_REPEATS);
                do
                    echo $topo $values $req_type $reqs $fixed $RUN_ID
                done
            done
        done
    done
done | xargs -n 6 -I{} -P $NUM_PROCESSES sh -c "sh ./eval_scripts/run-ebgp.sh {}"
