(lang dune 3.15)
(using coq 0.8)

(name vericaesar)

(generate_opam_files true)

(source
 (github BridgeTheMasterBuilder/vericaeser))

(authors "Master Builder")

(maintainers "Master Builder")

(license GPL-3.0-or-later)

(package
 (name vericaesar)
 (synopsis "Formally verified Caesar cipher written in Rocq/Coq")
 (depends ocaml dune
  (cmdliner (>= 1.2.0))))
