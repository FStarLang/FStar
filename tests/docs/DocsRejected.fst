(*
   Negative regression: a malformed [doc] payload is rejected by the
   typechecker, not silently accepted and dropped later.

   [doc] is an ordinary attribute of type [string -> Tot unit] and
   attributes are typechecked, so a payload of the wrong type is a type
   error at the declaration, with the usual error 189.
*)
module DocsRejected

[@@expect_failure [189]; doc 5]
let bad_payload (x:int) : int = x

[@@expect_failure [173]; doc "one" "two"]
let too_many_arguments (x:int) : int = x
