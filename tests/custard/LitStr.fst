module LitStr

(* Section 30.11.  A compile-time demand that reaches a binder through a
   pattern.

   Section 30.10 makes evaluation opt-in but says nothing about how the
   argument comes to be a constant.  In EverParse it does not, by itself:
   CDDL.Pulse.AST.Literal.impl_literal destructures a literal and hands the
   string it finds to the marked function, and a pattern variable is a runtime
   name, so error 372 fires.

   Rule 4b does not help here, and the difference is the point.  It is keyed
   on a constructor that stores a *type*, whose justification is that such a
   value has no runtime representation at all.  LStr stores a string, which
   has a perfectly good one; what makes it compile-time is not the value's
   nature but the use it is put to.  So rule 4c reads that use off the body:
   a binder a marked application depends on -- directly, or by way of the
   match that binds what the application is applied to -- is Mono.

   [ok_direct] is the control, applied to a literal with nothing in between.
   [impl_lit] carries CDDL's shape and no annotation; before rule 4c it needed
   [@@@monomorphize] on its binder, and then the same error reappeared one
   level up at its caller, which is the treadmill rule 4b exists to end.

   [main] checks its own answers. *)

module U32 = FStar.UInt32

let string_length (x: string) : Tot nat =
  List.Tot.length (String.list_of_string x)

[@@FStar.Attributes.custard_compile_time]
let string_len32 (x: string { string_length x < pow2 32 })
  : Tot (y: U32.t { U32.v y == string_length x })
  = U32.uint_to_t (string_length x)

(* The shape of CDDL.Spec.AST.Base.literal: a constructor storing a string. *)
type lit = | LStr : string -> lit | LInt : int -> lit

let wf (l: lit) : bool =
  match l with | LStr s -> string_length s < pow2 32 | LInt _ -> true

let ok_direct () : U32.t =
  assert_norm (string_length "abc" < pow2 32);
  string_len32 "abc"

let impl_lit (l: lit { wf l }) : U32.t =
  match l with
  | LStr s -> string_len32 s
  | LInt _ -> 0ul

(* A second instantiation, so that the specialization is keyed on the value
   rather than merely erased. *)
let main () : U32.t =
  assert_norm (wf (LStr "abc"));
  assert_norm (wf (LStr "hello"));
  assert_norm (wf (LInt 7));
  let a = ok_direct () in
  let b = impl_lit (LStr "abc") in
  let c = impl_lit (LStr "hello") in
  let d = impl_lit (LInt 7) in
  if U32.(a =^ 3ul) && U32.(b =^ 3ul) && U32.(c =^ 5ul) && U32.(d =^ 0ul)
  then 0ul else 1ul
