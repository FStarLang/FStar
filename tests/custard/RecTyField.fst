module RecTyField

(* Section 30.6 and 30.7.  A record with a [Type0] field, built by a
   *recursive* function over a syntax tree, and projected in a type position.

   The reduction of section 30.5 is what makes [(mk_bundle a).b_impl_type]
   ground, and here that reduction has to unfold a recursive definition -- so
   it needs [Zeta], and [Zeta] is what {!norm_optional} exists to make safe:
   a recursive unfolding need not terminate, and running out of budget has to
   mean the [any] this would have produced anyway rather than error 365.

   That alone is not enough.  [bundle] collapses to [b_dflt] (section 5.2),
   whose declared type is the erased field, so the specialized builders come
   out declared [any] however concrete their bodies are.  Section 30.7 reads
   the answer back off the body, and the chain -- builder, forwarder, the
   [ANode] recursion -- is what makes it a fixpoint rather than a single
   substitution.

   The [unfold] builder is the control: it is gone by extraction time, so it
   never depended on any of this and must keep working. *)

module U8 = FStar.UInt8
module U32 = FStar.UInt32

let mk_cps (n: U8.t) (t': Type0) (cont: U8.t -> t') : t' = cont n

noeq type bundle = { b_impl_type: Type0; b_dflt: b_impl_type }

type ast = | AU8 | AU32 | ANode : ast -> ast

unfold let mk_bundle_flat (a: ast) : bundle =
  match a with
  | AU32 -> { b_impl_type = U32.t; b_dflt = 7ul }
  | _    -> { b_impl_type = U8.t;  b_dflt = 3uy }

let use_flat ([@@@monomorphize] a: ast) (x: U8.t) : (mk_bundle_flat a).b_impl_type =
  mk_cps x (mk_bundle_flat a).b_impl_type (fun _ -> (mk_bundle_flat a).b_dflt)

let rec mk_bundle ([@@@monomorphize] a: ast) : bundle =
  match a with
  | AU32 -> { b_impl_type = U32.t; b_dflt = 70000ul }
  | AU8  -> { b_impl_type = U8.t;  b_dflt = 200uy }
  | ANode a' -> mk_bundle a'

let use_rec ([@@@monomorphize] a: ast) (x: U8.t) : (mk_bundle a).b_impl_type =
  mk_cps x (mk_bundle a).b_impl_type (fun _ -> (mk_bundle a).b_dflt)

let main () : U32.t =
  let a = use_flat AU8 1uy in
  let b = use_rec (ANode AU8) 2uy in
  let c = use_rec (ANode (ANode AU32)) 3uy in
  if U8.(a =^ 3uy) && U8.(b =^ 200uy) && U32.(c =^ 70000ul)
  then 0ul else 1ul
