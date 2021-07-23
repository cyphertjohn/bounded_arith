(lang dune 2.8)
(name bound)
(using menhir 2.1)


(generate_opam_files true)

(license MIT)
(authors "John Cyphert")
(maintainers "github.com/cyphertjohn")

(package
 (name bound)
 (synopsis "A library for generating symbolic bounds")
 (depends
   (mlgmpidl (>= 1.2.13))
 )
)