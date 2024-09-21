(lang dune 3.7)

(name toad)

(source
 (github AldanTanneo/toad))

(authors "César Sagaert")

(license MIT)

(using menhir 2.1)

(package
 (name toad)
 (depends ocaml dune menhir menhirLib ppx_deriving))
