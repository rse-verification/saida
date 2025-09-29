(lang dune 3.2)
(using dune_site 0.1)
(name frama-c-saida)

(generate_opam_files true)

(license GPL-2.0-or-later)
(maintainers "Ola Wingbrant" "Jesper Amilon")
(authors "The Saida development team")
(source (github rse-verification/saida))
(homepage "https://github.com/rse-verification/saida")
(version dev)

(package 
  (name frama-c-saida)
 (depends
  (ocaml (>= 4.14.2))
  (frama-c (= 31.0)))
 (synopsis "ACSL contract inference for helper functions")
 (description "This plugin for the Frama-C platform for source code analysis
of C programs provides inference of ACSL contracts for helper functions."))
