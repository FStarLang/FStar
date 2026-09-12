module RecTyAcc

(* Section 30.8 and 30.9.  Three ways to reach a record's [Type0] field, one
   of which used to work.

   The record is CDDL's bundle: a field of kind [Type0] and a sibling whose
   type is that field.  [ok_proj] spells the field as a projection, and
   section 30.5 reduces it.  The other two spell the same field differently,
   and it should not matter which:

   - [bug_match] destructures with a [match], which binds the type to a
     *variable* -- error 364, "the argument is the runtime parameter it".
     Section 30.8 resolves such a match at specialization time, unfolding just
     the scrutinee heads that a type-storing constructor is matched on.

   - [bug_acc] goes through an accessor, so the bundle reaches an ordinary
     runtime binder -- error 368, "the binder 'b' has type any".  Rule 4b
     (section 30.9) makes that binder [Mono] without an annotation, because a
     value whose own contents decide its representation has no runtime one to
     have.

   This is EverParse's shape twice over: the [match] is
   CDDL.Pulse.Bundle.MapGroup and the accessor is CDDL.Pulse.Bundle.Base.

   [main] checks its own answer, so a wrong reinterpretation is a nonzero exit
   rather than something to read out of the generated C. *)

module U8 = FStar.UInt8
module U32 = FStar.UInt32

let mk_cps (n: U8.t) (t': Type0) (cont: U8.t -> t') : t' = cont n

noeq type bundle = { b_impl_type: Type0; b_dflt: b_impl_type }

type ast = | AU8 | AU32 | ANode : ast -> ast

let rec mk_bundle ([@@@monomorphize] a: ast) : bundle =
  match a with
  | AU32 -> { b_impl_type = U32.t; b_dflt = 70000ul }
  | AU8  -> { b_impl_type = U8.t;  b_dflt = 200uy }
  | ANode a' -> mk_bundle a'

let ok_proj ([@@@monomorphize] a: ast) (x: U8.t) : (mk_bundle a).b_impl_type =
  mk_cps x (mk_bundle a).b_impl_type (fun _ -> (mk_bundle a).b_dflt)

let by_match ([@@@monomorphize] a: ast) (x: U8.t) : (mk_bundle a).b_impl_type =
  match mk_bundle a with
  | Mkbundle it d -> mk_cps x it (fun _ -> d)

let get_impl_type (b: bundle)
  : Pure Type0 (requires True) (ensures fun t -> t == b.b_impl_type)
  = match b with | Mkbundle it _ -> it

let get_dflt (b: bundle) : get_impl_type b =
  match b with | Mkbundle _ d -> d

let by_acc ([@@@monomorphize] a: ast) (x: U8.t) : get_impl_type (mk_bundle a) =
  mk_cps x (get_impl_type (mk_bundle a)) (fun _ -> get_dflt (mk_bundle a))

let main () : U32.t =
  let p = ok_proj  (ANode AU8) 1uy in
  let m = by_match (ANode AU8) 2uy in
  let a = by_acc   (ANode AU8) 3uy in
  let q = by_match (ANode (ANode AU32)) 4uy in
  if U8.(p =^ 200uy) && U8.(m =^ 200uy) && U8.(a =^ 200uy)
     && U32.(q =^ 70000ul)
  then 0ul else 1ul
