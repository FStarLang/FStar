module Steel.C.Model.Struct
include Steel.ST.C.Model.Struct

module STC = Steel.ST.Coercions
module P = FStar.PCM
open Steel.C.Model.PCM
open Steel.C.Model.Connection
open Steel.C.Model.Ref
// module Ptr = Steel.C.Model.Ptr
open Steel.Effect
module A = Steel.Effect.Atomic

open FStar.FunctionalExtensionality
open FStar.Classical


(*
let struct_view_to_view_prop
  (#a:Type) (#b: a -> Type) (#p:(k:a -> pcm (b k)))
  (fa:a -> prop)
  (view_t:(refine a fa -> Type))
  (field_view:(k:refine a fa -> sel_view (p k) (view_t k)))
: restricted_t a b -> Tot prop
= fun (f : restricted_t a b) ->
  forall (k:a).
    (fa k ==> (field_view k).to_view_prop (f k))

let struct_view_to_view
  (#a:Type) (#b: a -> Type) (#p:(k:a -> pcm (b k)))
  (#fa:a -> prop)
  (view_t:(refine a fa -> Type))
  (field_view:(k:refine a fa -> sel_view (p k) (view_t k)))
: refine (restricted_t a b) (struct_view_to_view_prop fa view_t field_view) ->
  Tot (restricted_t (refine a fa) view_t)
= fun (f: refine (restricted_t a b) (struct_view_to_view_prop fa view_t field_view)) ->
  let g = on_dom (refine a fa) (fun (k: refine a fa) -> (field_view k).to_view (f k)) in
  g

let struct_view_to_carrier
  (#a:Type) (#b: a -> Type) (#p:(k:a -> pcm (b k)))
  (#fa:a -> prop)
  (dec_fa: decidable fa)
  (view_t:(refine a fa -> Type))
  (field_view:(k:refine a fa -> sel_view (p k) (view_t k)))
: restricted_t (refine a fa) view_t ->
  Tot (refine (restricted_t a b) (struct_view_to_view_prop fa view_t field_view))
= fun (f: restricted_t (refine a fa) view_t) ->
  let g: restricted_t a b = on_dom a (fun k ->
    if dec_fa k then
      (field_view k).to_carrier (f k) <: b k
    else one (p k))
  in g

// let struct_view_to_carrier_not_one
//   (#a:Type) (#b: a -> Type) (#p:(k:a -> pcm (b k)))
//   (#fa:a -> prop)
//   (dec_fa: decidable fa)
//   (view_t:(refine a fa -> Type))
//   (field_view:(k:refine a fa -> sel_view (p k) (view_t k)))
//   (x:restricted_t (refine a fa) view_t)
// : Lemma
//     (requires exists (k:a). fa k)
//     (ensures struct_view_to_carrier dec_fa view_t field_view x =!= one (prod_pcm p))
// = let k = FStar.IndefiniteDescription.indefinite_description_ghost a fa in
//   (field_view k).to_carrier_not_one (x k)

let struct_view_to_view_frame
  (#a:Type) (#b: a -> Type) (#p:(k:a -> pcm (b k)))
  (#fa:a -> prop)
  (dec_fa: decidable fa)
  (view_t:(refine a fa -> Type))
  (field_view:(k:refine a fa -> sel_view (p k) (view_t k)))
  (x:restricted_t (refine a fa) view_t)
  (frame: restricted_t a b)
: Lemma
    (requires (composable (prod_pcm p) (struct_view_to_carrier dec_fa view_t field_view x) frame))
    (ensures
      struct_view_to_view_prop fa view_t field_view
        (op (prod_pcm p) (struct_view_to_carrier dec_fa view_t field_view x) frame) /\ 
      struct_view_to_view view_t field_view
        (op (prod_pcm p) (struct_view_to_carrier dec_fa view_t field_view x) frame) == x)
= let aux (k:refine a fa)
  : Lemma (
      (field_view k).to_view_prop (op (p k) ((field_view k).to_carrier (x k)) (frame k)) /\
      (field_view k).to_view (op (p k) ((field_view k).to_carrier (x k)) (frame k)) == x k)
  = assert (composable (p k) ((field_view k).to_carrier (x k)) (frame k));
    (field_view k).to_view_frame (x k) (frame k)
  in forall_intro aux;
  assert (
    struct_view_to_view view_t field_view
       (op (prod_pcm p) (struct_view_to_carrier dec_fa view_t field_view x) frame) `feq` x)
*)

let mem (#a:eqtype) (xs:list a) x : prop = List.mem x xs == true

let struct_view_to_view_prop 
  (#a:eqtype) (#b: a -> Type) (#p:(k:a -> pcm (b k)))
  (#view_t:a -> Type)
  (#can_view_units: bool)
  (field_view:(k:a -> sel_view (p k) (view_t k) can_view_units))
  (included: list a)
: restricted_t a b -> prop
= fun f -> forall (k:a). (mem included k ==> (field_view k).to_view_prop (f k))

let struct_view_to_view
  (#a:eqtype) (#b: a -> Type) (#p:(k:a -> pcm (b k)))
  (#view_t:a -> Type)
  (#can_view_units: bool)
  (field_view:(k:a -> sel_view (p k) (view_t k) can_view_units))
  (included: list a)
: refine (restricted_t a b) (struct_view_to_view_prop field_view included) ->
  Tot (restricted_t (refine a (mem included)) view_t)
= fun f -> on_dom (refine a (mem included)) (fun k -> (field_view k).to_view (f k))

let struct_view_to_carrier
  (#a:eqtype) (#b: a -> Type) (#p:(k:a -> pcm (b k)))
  (#view_t:a -> Type)
  (#can_view_units: bool)
  (field_view:(k:a -> sel_view (p k) (view_t k) can_view_units))
  (included: list a)
: restricted_t (refine a (mem included)) view_t ->
  Tot (refine (restricted_t a b) (struct_view_to_view_prop field_view included))
= fun f ->
  let g: restricted_t a b = on_dom a (fun k ->
    if k `List.mem` included then
      (field_view k).to_carrier (f k) <: b k
    else one (p k))
  in g

let struct_view_to_view_frame
  (#a:eqtype) (#b: a -> Type) (#p:(k:a -> pcm (b k)))
  (#view_t:a -> Type)
  (#can_view_units: bool)
  (field_view:(k:a -> sel_view (p k) (view_t k) can_view_units))
  (included: list a)
  (x:restricted_t (refine a (mem included)) view_t)
  (frame: restricted_t a b)
: Lemma
    (requires (composable (prod_pcm p) (struct_view_to_carrier field_view included x) frame))
    (ensures
      struct_view_to_view_prop field_view included
        (op (prod_pcm p) (struct_view_to_carrier field_view included x) frame) /\ 
      struct_view_to_view field_view included
        (op (prod_pcm p) (struct_view_to_carrier field_view included x) frame) == x)
= let aux (k:refine a (mem included))
  : Lemma (
      (field_view k).to_view_prop (op (p k) ((field_view k).to_carrier (x k)) (frame k)) /\
      (field_view k).to_view (op (p k) ((field_view k).to_carrier (x k)) (frame k)) == x k)
  = assert (composable (p k) ((field_view k).to_carrier (x k)) (frame k));
    (field_view k).to_view_frame (x k) (frame k)
  in forall_intro aux;
  assert (
    struct_view_to_view field_view included
       (op (prod_pcm p) (struct_view_to_carrier field_view included x) frame) `feq` x)

let struct_view
  (#a:eqtype) (#b: a -> Type) (#p:(k:a -> pcm (b k)))
  (#view_t:a -> Type)
  (#can_view_units: bool)
  (field_view:(k:a -> sel_view (p k) (view_t k) can_view_units))
  (included: list a)
: sel_view (prod_pcm p)
    (restricted_t (refine a (mem included)) view_t)
    (can_view_units || Nil? included)
= {
  to_view_prop = struct_view_to_view_prop field_view included;
  to_view = struct_view_to_view field_view included;
  to_carrier = struct_view_to_carrier field_view included;
  to_carrier_not_one = begin
    let aux () : Lemma
      (requires ~ (can_view_units || Nil? included))
      (ensures
        ~ (exists x. struct_view_to_carrier field_view included x == one (prod_pcm p)) /\
        ~ (struct_view_to_view_prop field_view included (one (prod_pcm p))))
    = let k :: _ = included in ()
    in move_requires aux () end;
  to_view_frame = struct_view_to_view_frame field_view included;
}
