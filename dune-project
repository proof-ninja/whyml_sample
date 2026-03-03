(lang dune 3.21)

(name infv)

(generate_opam_files true)

(source
 (github proof-ninja/whyml_sample))

(authors "Yoshihiro Imai <y.imai@proof-ninja.co.jp>"
         "ymoymoon")

(maintainers "Yoshihiro Imai <y.imai@proof-ninja.co.jp>")

(license LICENSE)

(documentation https://github.com/proof-ninja/whyml_sample)

(package
 (name infv)
 (synopsis "Inference Language with Why3")
 (description "Inference Language with Why3")
 (depends 
    (ocaml (>= 4.09.1)) 
    (why3 (= 1.5.1)))
 (tags
  ("why3")))

; See the complete stanza docs at https://dune.readthedocs.io/en/stable/reference/dune-project/index.html
