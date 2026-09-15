(lang dune 3.21)
(using rocq 0.11)
(using directory-targets 0.1)

(generate_opam_files true)

(name coq-analysis)

(package
 (name coq-analysis)
 (synopsis "Formalized real analysis with Waterproof")
 (depends rocq-core rocq-stdlib (coq-waterproof (>= 3.1.0+9.1))))
