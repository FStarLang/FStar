module Steel.C.Model.Union
include Steel.ST.C.Model.Union

module STC = Steel.ST.Coercions
module P = FStar.PCM
open Steel.C.Model.PCM
open Steel.C.Model.Connection
open Steel.C.Model.Ref
open Steel.C.Model.Struct
open Steel.Effect
module A = Steel.Effect.Atomic

open FStar.FunctionalExtensionality

let union_view_to_view_prop
  (#a:Type) (#b: a -> Type) (#p:(k:a -> pcm (b k)))
  (#view_t:a -> Type) (case_view:(k:a -> sel_view (p k) (view_t k) false))
: union p -> Tot prop
= fun u ->
  u =!= one (union_pcm p) /\
  (forall k. case_refinement_f p k u ==> (case_view k).to_view_prop (u k))

let union_view_to_view
  (#a:Type) (#b: a -> Type) (#p:(k:a -> pcm (b k)))
  (#view_t:a -> Type) (case_view:(k:a -> sel_view (p k) (view_t k) false))
  (case_of:(u:union p -> k:a{case_refinement_f p k u}))
: refine (union p) (union_view_to_view_prop case_view) -> dtuple2 a view_t
= fun u -> let k = case_of u in (|k, (case_view k).to_view (u k)|)

let union_view_to_carrier
  (#a:eqtype) (#b: a -> Type) (#p:(k:a -> pcm (b k)))
  (#view_t:a -> Type) (case_view:(k:a -> sel_view (p k) (view_t k) false))
: dtuple2 a view_t -> refine (union p) (union_view_to_view_prop case_view)
= fun (|k, x|) -> field_to_union_f p k ((case_view k).to_carrier x)

let union_view
  (#a:eqtype) (#b: a -> Type) (#p:(k:a -> pcm (b k)))
  (#view_t:a -> Type) (case_view:(k:a -> sel_view (p k) (view_t k) false))
  (case_of:(u:union p -> k:a{case_refinement_f p k u}))
: Tot (sel_view (union_pcm p) (dtuple2 a view_t) false)
= {
  to_view_prop = union_view_to_view_prop case_view;
  to_view = union_view_to_view case_view case_of;
  to_carrier = union_view_to_carrier case_view;
  to_carrier_not_one = ();
  to_view_frame = (fun (|k, x|) u -> (case_view k).to_view_frame x (u k));
}
