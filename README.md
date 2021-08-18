# Term Rewriter

## Dependencies
This code requires an ocaml interface the the GNU MultiPrecision library (gmp).

For ocaml opam is also helpful. To install these dependencies on Ubuntu run:

`sudo apt-get install opam libgmp-dev libmpfr-dev`

To initialize opam run:

`opam init`

Then the ocaml packages can be installed by running the following in the project directory with:

`opam install . --deps-only`

Also, utop is helpful. To install run

`opam install utop`

## Building
To build the library MyLib run:

`dune build`

## Usage
For now I've been using utop to interact with the library. To do this run:

`dune utop lib`

which launches utop with the library defined in the lib directory.

To launch utop with additional libraries, for example str, run

`dune utop lib -- -require str`

Then inside utop files can be loaded with

`#use "examples/elastic.ml"`

for example
