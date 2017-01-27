(** POLY1305 **)

1- Code structure of Poly1305:

The library files (realized directly in ML) are the following:
- sint.fst
  Constains the definition of the secret integers and defines all the allowed operations on such secrets
- SInt.UInt8.fst / SInt.UInt63.fst
  Specialize the Sint module from the file above to bytes and native OCaml integers (63bits)
- SBuffer.fst / SBytes.fst
  Buffer (with pointer arithmetic) modelization in F*
- bigint.fst
  Specification of the big integer modelization and evaluation functions
- bignum.fst
  Core of the implementation of Poly1305, implements the modular arithmetic required in the primitive
- poly.fst
  High level functions of poly1305, poly1305_mac is the main function to be exported

2- Instructions to verify and run poly1305:

- INSTALL the latest version of F* from sources (https://github.com/FStarLang/FStar/blob/master/INSTALL.md)
- move to the current directory (FStar/examples/primitives)
- run ("make poly-ml") to extract and run the code without verifying it
  Note: the code extracts to OCaml, and requires the ocaml libraries batteries, zarith and stdint
- run ("make poly") to verify the code (may require a desktop machine to have all assertions going through)

