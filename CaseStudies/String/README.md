## Installation

1. Install [opam](https://opam.ocaml.org/doc/Install.html): 
```
bash -c "sh <(curl -fsSL https://opam.ocaml.org/install.sh)"
```
2. Initialize opam `opam init`
3. Set the environment (compiler version) for this project
```
opam switch create autoinc 4.14.1
opam switch autoinc
opam install ocaml-lsp-server
```

## Build
```
dune build
```