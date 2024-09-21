# Toad

A Rust-inspired, garbage collected (using Boehm GC) toy language.

Full of very ugly code and flimsy stuff, but a good learning experience anyway

## Building

You will need Ocaml and the Dune build system, and the Boehm-GC package installed (`libgc-dev` package on Debian, `gc-devel` on Fedora).

Then the compiler can be built with `dune build`, installed with `dune install`.

## Testing

Running `toadc test.toad -o test` should give you a test executable. Any argument passed to `toadc` after `--` will be forwarded to the C compiler.
