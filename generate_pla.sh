#!/bin/bash
 
onesort=(
    "ivybench/ex/vmt/lockserv_automaton.vmt"
    "ivybench/ex/vmt/ring_not_dead.vmt"
    "ivybench/ex/vmt/ring.vmt"
    "ivybench/ex/vmt/simple-decentralized-lock.vmt"
    "ivybench/i4/vmt/chord_ring_maintenance.vmt"
    "ivybench/i4/vmt/two_phase_commit.vmt"
    "ivybench/mypyv/vmt/firewall.vmt"
    "ivybench/mypyv/vmt/learning_switch.vmt"
    "ivybench/mypyv/vmt/lockserv.vmt"
    "ivybench/tla/vmt/Consensus.vmt"
    "ivybench/tla/vmt/TCommit.vmt"
    "ivybench/tla/vmt/TwoPhase.vmt"
)

twosort=(
    "ivybench/ex/vmt/decentralized-lock_abstract.vmt"
    "ivybench/ex/vmt/decentralized-lock.vmt"
    "ivybench/ex/vmt/distributed_lock_abstract.vmt"
    "ivybench/ex/vmt/distributed_lock_maxheld.vmt"
    "ivybench/ex/vmt/majorityset-leader-election.vmt"
    "ivybench/ex/vmt/quorum-leader-election.vmt"
    "ivybench/ex/vmt/ring_id_not_dead_limited.vmt"
    "ivybench/i4/vmt/distributed_lock.vmt"
    "ivybench/i4/vmt/leader_election_in_ring.vmt"
    "ivybench/i4/vmt/learning_switch.vmt"
    "ivybench/i4/vmt/lock_server.vmt"
    "ivybench/mypyv/vmt/consensus_wo_decide.vmt"
    "ivybench/mypyv/vmt/ring_id_not_dead.vmt"
    "ivybench/mypyv/vmt/ring_id.vmt"
    "ivybench/mypyv/vmt/ticket.vmt"
)

threesort=(
    "ivybench/ex/vmt/simple-election.vmt"
    "ivybench/ex/vmt/toy_consensus.vmt"
    "ivybench/mypyv/vmt/client_server_ae.vmt"
    "ivybench/mypyv/vmt/consensus_epr.vmt"
    "ivybench/mypyv/vmt/consensus_forall.vmt"
    "ivybench/mypyv/vmt/hybrid_reliable_broadcast.vmt"
    "ivybench/mypyv/vmt/sharded_kv_no_lost_keys.vmt"
    "ivybench/mypyv/vmt/sharded_kv.vmt"
    "ivybench/mypyv/vmt/toy_consensus_epr.vmt"
    "ivybench/mypyv/vmt/toy_consensus_forall.vmt"
    "ivybench/tla/vmt/Simple.vmt"
    "ivybench/tla/vmt/SimpleRegular.vmt"
)

foursort=(
    "ivybench/i4/vmt/database_chain_replication.vmt"
    "ivybench/mypyv/vmt/client_server_db_ae.vmt"
)

for f in "${onesort[@]}"; do
    echo -e "\n"
    echo $f
    for i in {1..20}; do 
        filename=$(basename $f .vmt)
        mkdir -p pla/raw/${filename}
        echo $i | timeout 5m python ic3po/top.py -m frpo $f >| pla/raw/${filename}/${filename}_${i}.txt
        if [ $? -eq 124 ]; then 
            echo "the command timed out"
            continue 2
        fi
        mkdir -p pla/processed/${filename}
        python3 pla_converter.py pla/raw/${filename}/${filename}_${i}.txt >| pla/processed/${filename}/${filename}_${i}.pla
    done
done
for f in "${twosort[@]}"; do
    echo -e "\n"
    echo $f
    for i in {1..15}; do 
        for j in {1..15}; do
            filename=$(basename $f .vmt)
            mkdir -p pla/raw/${filename}
            (echo $i; echo $j) | timeout 5m python ic3po/top.py -m frpo $f >| pla/raw/${filename}/${filename}_${i}.txt
            if [ $? -eq 124 ]; then 
                echo "the command timed out"
                continue 3
            fi
            mkdir -p pla/processed/${filename}
            python3 pla_converter.py pla/raw/${filename}/${filename}_${i}.txt >| pla/processed/${filename}/${filename}_${i}.pla
        done
    done
done
for f in "${threesort[@]}"; do
    echo -e "\n"
    echo $f
    for i in {1..15}; do 
        for j in {1..15}; do
            for k in {1..15}; do
                filename=$(basename $f .vmt)
                mkdir -p pla/raw/${filename}
                (echo $i; echo $j; echo $k) | timeout 5m python ic3po/top.py -m frpo $f >| pla/raw/${filename}/${filename}_${i}.txt
                if [ $? -eq 124 ]; then 
                    echo "the command timed out"
                    continue 4
                fi
                mkdir -p pla/processed/${filename}
                python3 pla_converter.py pla/raw/${filename}/${filename}_${i}.txt >| pla/processed/${filename}/${filename}_${i}.pla
            done
        done
    done
done
for f in "${foursort[@]}"; do
    echo -e "\n"
    echo $f
    for i in {1..15}; do 
        for j in {1..15}; do
            for k in {1..15}; do
                for l in {1..15}; do
                    filename=$(basename $f .vmt)
                    mkdir -p pla/raw/${filename}
                    (echo $i; echo $j; echo $k; echo $l) | timeout 5m python ic3po/top.py -m frpo $f >| pla/raw/${filename}/${filename}_${i}.txt
                    if [ $? -eq 124 ]; then 
                        echo "the command timed out"
                        continue 5
                    fi
                    mkdir -p pla/processed/${filename}
                    python3 pla_converter.py pla/raw/${filename}/${filename}_${i}.txt >| pla/processed/${filename}/${filename}_${i}.pla
                done
            done
        done
    done
done
