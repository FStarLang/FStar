open Fstarcompiler
open Prims
type 'a set = ('a, Prims.bool) FStar_FunctionalExtensionality.restricted_t
type ('a, 's1, 's2) equal = unit
let mem (x : 'a) (s : 'a set) : Prims.bool= s x
let empty (uu___ : unit) : 'a set=
  FStar_FunctionalExtensionality.on_domain (fun x -> false)
let singleton (x : 'a) : 'a set=
  FStar_FunctionalExtensionality.on_domain (fun y -> y = x)
let union (s1 : 'a set) (s2 : 'a set) : 'a set=
  FStar_FunctionalExtensionality.on_domain (fun x -> (s1 x) || (s2 x))
let intersect (s1 : 'a set) (s2 : 'a set) : 'a set=
  FStar_FunctionalExtensionality.on_domain (fun x -> (s1 x) && (s2 x))
let complement (s : 'a set) : 'a set=
  FStar_FunctionalExtensionality.on_domain (fun x -> Prims.op_Negation (s x))
type ('a, 's1, 's2) disjoint = unit
type ('a, 's1, 's2) subset = unit
let add (x : 'a) (s : 'a set) : 'a set= union s (singleton x)
let remove (x : 'a) (s : 'a set) : 'a set=
  intersect s (complement (singleton x))
let rec as_set' : 'a . 'a Prims.list -> 'a set =
  fun l ->
    match l with
    | [] -> empty ()
    | hd::tl -> union (singleton hd) (as_set' tl)
let as_set (l : 'a Prims.list) : 'a set=
  match l with | [] -> empty () | hd::tl -> union (singleton hd) (as_set' tl)
