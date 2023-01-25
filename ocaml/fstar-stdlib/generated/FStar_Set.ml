open Prims
type 'a set = ('a, Prims.bool) FStar_FunctionalExtensionality.restricted_t
type ('a, 's1, 's2) equal = unit
let mem : 'a . 'a -> 'a set -> Prims.bool = fun x -> fun s -> s x
let empty : 'a . unit -> 'a set =
  fun uu___ -> FStar_FunctionalExtensionality.on_domain (fun x -> false)
let singleton : 'a . 'a -> 'a set =
  fun x -> FStar_FunctionalExtensionality.on_domain (fun y -> y = x)
let union : 'a . 'a set -> 'a set -> 'a set =
  fun s1 ->
    fun s2 ->
      FStar_FunctionalExtensionality.on_domain (fun x -> (s1 x) || (s2 x))
let intersect : 'a . 'a set -> 'a set -> 'a set =
  fun s1 ->
    fun s2 ->
      FStar_FunctionalExtensionality.on_domain (fun x -> (s1 x) && (s2 x))
let complement : 'a . 'a set -> 'a set =
  fun s ->
    FStar_FunctionalExtensionality.on_domain
      (fun x -> Prims.op_Negation (s x))
type ('a, 's1, 's2) disjoint = unit
type ('a, 's1, 's2) subset = unit
let add : 'a . 'a -> 'a set -> 'a set =
  fun x -> fun s -> union s (singleton x)
let remove : 'a . 'a -> 'a set -> 'a set =
  fun x -> fun s -> intersect s (complement (singleton x))
let rec as_set' : 'a . 'a Prims.list -> 'a set =
  fun l ->
    match l with
    | [] -> empty ()
    | hd::tl -> union (singleton hd) (as_set' tl)
let as_set : 'a . 'a Prims.list -> 'a set =
  fun l ->
    match l with
    | [] -> empty ()
    | hd::tl -> union (singleton hd) (as_set' tl)