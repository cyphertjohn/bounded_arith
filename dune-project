(lang dune 2.8)
(name bound)
(using menhir 2.1)

(license MIT)
(authors "John Cyphert")
(maintainers "github.com/cyphertjohn")
(homepage "github.com/cyphertjohn/bounded_arith")
(bug_reports "github.com/cyphertjohn/bounded_arith")

(generate_opam_files true)

(package
 (name bound)
 (synopsis "A library for generating symbolic bounds")
 (depends
   (zarith :build)
   (z3 :build)
   (menhir :build)
   (batteries :build)
   (faugere :build)
   (faugere_zarith :build)
 )
)