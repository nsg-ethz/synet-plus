#!/usr/bin/env bash

# Generate evaluation values for all given reqs
NUM_PROCESSES=1
NUM_REPEATS=1


PATH_TO_TOPOS="topos/*/"
#topos/small/Arnes topos/small/Bics.graphml topos/small/Canerie topos/small/Renater2008 topos/small/CrlNetworkServices;
#topos/mid/Columbus.graphml topos/mid/Esnet.graphml topos/mid/Latnet.graphml topos/mid/Sinet.graphml topos/mid/Uninett2011.graphml
#topos/large/Cogentco.graphml  topos/large/Colt.graphml	topos/large/GtsCe.graphml  topos/large/TataNld.graphml	topos/large/UsCarrier.graphml

for file in topos/small/Arnes topos/small/Canerie topos/small/Renater2008 topos/small/CrlNetworkServices;
do
    topo="${file}.graphml"
    values="${file}_ospf_reqs.py "
    for syn in cegis concrete;
    do
        #for reqs in 1 2 4 8 16;
        for reqs in 1;
        do
            for req_type in simple kconnected ecmp order;
            do
                for fixed in "0" "0.25" "0.5" "1.0";
                do
                    for RUN_ID in $(seq 1 $NUM_REPEATS);
                    do
                        echo $topo $values $syn $req_type $reqs $fixed $RUN_ID
                    done
                done
            done
        done
    done
done | xargs -n 7 -I{} -P $NUM_PROCESSES sh -c "sh ./eval_scripts/run-ospf.sh {}"
