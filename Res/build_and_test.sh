#!/bin/bash

make clean
make -j2
echo "Performing tests in Coq's environment..."
coqc test_re.v
echo "Cleaning previous OCaml builds"
rm -rf extr.*
echo "Extracting new one..."
coqc extract.v > extr.ml
echo "Sanitizing data"
ocamlbuild -clean test_ocaml.native
echo "Compiling OCaml code..."
ocamlbuild -no-hygiene test_ocaml.native
echo "Replaying Coq tests with extracted OCaml code..."
./test_ocaml.native
echo "Done!!!!"
