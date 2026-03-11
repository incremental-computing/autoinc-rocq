# Supplementary materials

We provide this repository as the supplementary materials for the paper "Stateful Differential Operators for Incremental Computing". 

This repository includes the Rocq (Coq) formalization along with the extracted OCaml code used in our experiments.

## Installation
We have only tested the installation on macOS, but we expect it to work on Linux systems as well.

### Rocq (Coq) formalization

The formalization is known to compile with Rocq 9.1.0. 
To install Rocq 9.1.0, please first install the package manager [opam](https://opam.ocaml.org/doc/Install.html). 

Once `opam` is installed, run the following commands to initialize `opam` and install Rocq:
```
opam init
eval $(opam env)
opam pin add rocq-prover 9.1.0
```

After that, you can compile this project with the command `make`. 
Perhaps you need to generate the Makefile before running `make`:
```
rocq makefile -f _CoqProject -o Makefile
```

(The installation guide of specific version Rocq can also be found at [Rocq's official site](https://rocq-prover.org/docs/using-opam).)

### Case studies
The two case studies code is stored in the [CaseStudies](./CaseStudies/) folder. We recommend compiling it using the [dune](https://github.com/ocaml/dune) build system, which is installed alongside Rocq.
The code is known to work with OCaml 4.14.1.

Run the first case study's experiment:
```
cd CaseStudies/RelationalAlgebra 
chmod 777 runexp.sh
./runexp.sh
```

Run the second case study's experiment:
```
cd CaseStudies/String 
chmod 777 runexp.sh
./runexp.sh
```

## Project structure
- [`Change`](./Change/): The definition of change structures [`Change.v`](./Change/Change.v) and various instances of change structure.
- [`Operator`](./Operator/): The definition of stateless and stateful differential operators ([Operator.v](./Operator/Operator.v)) and differential operators mentioned in paper:
  
  - [`Join`](./Operator/BagOp.v)
  - [`Aggregation`]((./Operator/BagOp.v))
  - [`TrimRight`](./Operator/TrimOps.v)
  - String operators mentioned in Section 6.3: `./Operator/StringOp.v` 