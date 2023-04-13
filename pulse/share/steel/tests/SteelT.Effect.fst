module SteelT.Effect
open Steel.Memory
irreducible
let resolve_framing : unit = ()

type pre_t = slprop u#1
type post_t (a:Type) = a -> slprop u#1

type repr (a:Type u#a) (pre:pre_t) (post:post_t a) = unit -> unit

let returnc (a:Type u#a) (x:a) (p:a -> slprop)
: repr a (p x) p
= admit()

let bind (a:Type) (b:Type)
  (#[@@@resolve_framing] pre_f:pre_t)
  (#[@@@resolve_framing] post_f:post_t a)
  (#[@@@resolve_framing] post_g:post_t b)
  (f:repr a pre_f post_f)
  (g:(x:a -> repr b (post_f x) post_g))
: repr b pre_f post_g
= admit()


reifiable reflectable
layered_effect {
  SteelT : a:Type -> pre:pre_t -> post:post_t a -> Effect
  with
  repr = repr;
  return = returnc;
  bind = bind
}

let bind_pure_steel (a:Type) (b:Type)
  (wp:pure_wp a)
  (pre_g:pre_t) (post_g:post_t b)
  (f:eqtype_as_type unit -> PURE a wp) (g:(x:a -> repr b pre_g post_g))
: repr b pre_g post_g
= admit()

polymonadic_bind (PURE, SteelT) |> SteelT = bind_pure_steel

let bind_steel_pure (a:Type) (b:Type)
    (pre_f:pre_t) (post_f:slprop)
    (wp_g:a -> pure_wp b)
    (f:repr a pre_f (fun _ -> post_f))
    (g:(x:a -> eqtype_as_type unit -> PURE b (wp_g x)))
: repr b pre_f (fun _ -> post_f)
= admit()

polymonadic_bind (SteelT, PURE) |> SteelT = bind_steel_pure
