#!/bin/bash

(echo $1; echo $2) | python2 ic3po/top.py -m frpo toy_lock/normal/toy_lock.vmt >| toy_lock/normal/raw/toy_lock_${1}_${2}.txt
python3 pla_converter.py toy_lock/normal/raw/toy_lock_${1}_${2}.txt >| toy_lock/normal/processed/toy_lock_${1}_${2}.pla