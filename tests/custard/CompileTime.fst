module CompileTime

(* Section 30.10.  A definition that asks to be evaluated at extraction time
   rather than compiled.

   Custard does not evaluate closed terms on its own initiative: a program that
   computes something at run time is meant to compute it at run time, and
   reducing whenever it could would make every definition's body part of every
   caller.  So this is opt-in, one definition at a time.

   [string_length] is EverParse's, from CDDL.Pulse.AST.Literal, and shows why
   the feature is worth having: it is [length (list_of_string x)] applied only
   ever to literals, so every call has an answer, but compiling it asks C for a
   [list char], which C does not have.  With the attribute the [list] never
   exists -- [len] below is the constant 5 in the generated code, and the C
   test asserts that no list type is emitted.

   [dbl] is the same feature without the interesting types, and pins the point
   that the reduction is real rather than an unfolding: [dbl 21] arrives as the
   literal 42.

   [main] checks its own answers, so a wrong constant is a nonzero exit rather
   than something to read out of the generated C.

   The companion reject test CompileTimeBad checks the other half of the
   contract: an application whose argument is not known is an error naming the
   definition, not a silent fall-back to compiling it. *)

open FStar.Attributes

module U32 = FStar.UInt32

let string_length (x: string) : nat =
  FStar.List.Tot.length (FStar.String.list_of_string x)

let rec dbl (n: nat) : nat = if n = 0 then 0 else 2 + dbl (n - 1)

(* The attribute goes on the wrapper rather than on [string_length], so that
   what is evaluated is a whole expression ending in a machine integer: an
   unbounded [nat] has no C representation either, and a definition marked for
   compile-time evaluation is free to have a type C could not compile, because
   none of it is compiled. *)
[@@custard_compile_time]
let string_len32 (x: string) : U32.t =
  U32.uint_to_t (string_length x % 4294967296)

[@@custard_compile_time]
let dbl32 (n: nat) : U32.t = U32.uint_to_t (dbl n % 4294967296)

let main () : U32.t =
  let len = string_len32 "hello" in
  let d = dbl32 21 in
  if U32.(len =^ 5ul) && U32.(d =^ 42ul) then 0ul else 1ul
