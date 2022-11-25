(lang dune 3.6)

(name fstar)
(generate_opam_files false)

(source
 (github FStarLang/FStar))

(authors "Nik Swamy <nswamy@microsoft.com>,Jonathan Protzenko <protz@microsoft.com>,Tahina Ramananandro <taramana@microsoft.com>")

(maintainers "taramana@microsoft.com")

(license LICENSE)

(documentation http://fstar-lang.org)

(package
 (name fstar)
 (allow_empty)
 (synopsis "Verification system for effectful programs")
 (depends ocaml dune zarith)
 (tags
  (topics "to describe" your project)))
