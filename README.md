# Term Rewriter

## Dependencies
This code requires an ocaml interface to the GNU MultiPrecision library (gmp).

For ocaml opam is also helpful. To install these dependencies on Ubuntu run:

`sudo apt-get install opam libgmp-dev libmpfr-dev`

To initialize opam run:

`opam init`

Then the ocaml packages can be installed by running the following in the project directory with:

`opam install . --deps-only`

Also, utop is helpful. To install run

`opam install utop`

For this branch of the repo the [ocaml faugere library](https://github.com/cyphertjohn/faugere) is required for Grobner basis calculation.

## Building
To build the library MyLib run:

`dune build`

## Usage
For now I've been using utop to interact with the library. 

Running `dune build` will create a custom utop with the library already loaded on startup. To interact with the library run `./mytoplevel.exe` after building.
