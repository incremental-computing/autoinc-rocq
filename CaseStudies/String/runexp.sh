#!/bin/bash
dune build
echo "Experiment with unoptimized string operators"
./_build/default/test/exp_string_op.exe
echo "Experiment with optimized string operators"
./_build/default/test/exp_string_op_opt.exe



