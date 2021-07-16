# Term Rewriter

## Dependencies
This code requires an ocaml interface the the GNU MultiPrecision library (gmp).

For ocaml opam is also helpful. To install these dependencies on Ubuntu run:

`sudo apt-get install opam libgmp-dev libmpfr-dev`

To initialize opam run:

`opam init`

Then the ocaml packages (along with a help REPL interface utop) can be installed with

`opam install mlgmpidl utop`.

## Building
To build the library MyLib run:

`dune build`

## Usage
For now I've been using utop to interact with the library. To do this run:

`utop`

This will open an ocaml REPL. To load the built library run:

`#use_output "dune top"`

To load the file src/poly.ml run

`#use "src/poly.ml"`.