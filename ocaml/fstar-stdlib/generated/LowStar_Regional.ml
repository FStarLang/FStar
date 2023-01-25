open Prims
type ('st, 'a) regional =
  | Rgl of 'st * unit * unit * 'a * unit * unit * unit * unit * unit * unit *
  unit * ('st -> unit -> 'a) * ('st -> 'a -> unit) 
let uu___is_Rgl : 'st 'a . ('st, 'a) regional -> Prims.bool =
  fun projectee -> true
let __proj__Rgl__item__state : 'st 'a . ('st, 'a) regional -> 'st =
  fun projectee ->
    match projectee with
    | Rgl
        (state, region_of, loc_of, dummy, r_inv, r_inv_reg, repr, r_repr,
         r_sep, irepr, r_alloc_p, r_alloc, r_free)
        -> state
let __proj__Rgl__item__dummy : 'st 'a . ('st, 'a) regional -> 'a =
  fun projectee ->
    match projectee with
    | Rgl
        (state, region_of, loc_of, dummy, r_inv, r_inv_reg, repr, r_repr,
         r_sep, irepr, r_alloc_p, r_alloc, r_free)
        -> dummy
let __proj__Rgl__item__r_alloc :
  'st 'a . ('st, 'a) regional -> 'st -> unit -> 'a =
  fun projectee ->
    match projectee with
    | Rgl
        (state, region_of, loc_of, dummy, r_inv, r_inv_reg, repr, r_repr,
         r_sep, irepr, r_alloc_p, r_alloc, r_free)
        -> r_alloc
let __proj__Rgl__item__r_free :
  'st 'a . ('st, 'a) regional -> 'st -> 'a -> unit =
  fun projectee ->
    match projectee with
    | Rgl
        (state, region_of, loc_of, dummy, r_inv, r_inv_reg, repr, r_repr,
         r_sep, irepr, r_alloc_p, r_alloc, r_free)
        -> r_free
type ('a, 'rst, 'rg, 'uuuuu, 'uuuuu1) rg_inv = Obj.t
let rg_dummy : 'a 'rst . ('rst, 'a) regional -> 'a =
  fun rg -> __proj__Rgl__item__dummy rg
let rg_alloc : 'a 'rst . ('rst, 'a) regional -> unit -> 'a =
  fun rg ->
    fun r -> __proj__Rgl__item__r_alloc rg (__proj__Rgl__item__state rg) ()
let rg_free : 'a 'rst . ('rst, 'a) regional -> 'a -> unit =
  fun rg ->
    fun v -> __proj__Rgl__item__r_free rg (__proj__Rgl__item__state rg) v