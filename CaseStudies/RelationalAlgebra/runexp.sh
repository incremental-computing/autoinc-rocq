#!/bin/bash
dune build
echo "Experiment 1 (Join)"
./_build/default/Experiment_1_Join.exe
echo "Experiment 2 (JoinAgg)"
./_build/default/Experiment_2_Agg_Join.exe


