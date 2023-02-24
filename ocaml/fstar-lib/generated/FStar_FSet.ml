open Prims
type ('a, 'f, 'xs) has_elements = unit
type 'a set = ('a, Prims.bool) FStar_FunctionalExtensionality.restricted_t
let intro_set :
  'a .
    ('a, Prims.bool) FStar_FunctionalExtensionality.restricted_t ->
      unit -> 'a set
  = fun f -> fun xs -> f
let emptyset : 'a . unit -> 'a set =
  fun uu___ ->
    intro_set
      (FStar_FunctionalExtensionality.on_domain (fun uu___1 -> false)) ()
let insert : 'a . 'a -> 'a set -> 'a set =
  fun x ->
    fun s ->
      intro_set
        (FStar_FunctionalExtensionality.on_domain
           (fun x' -> (x = x') || (s x'))) ()
let set_remove :
  'a .
    'a ->
      ('a, Prims.bool) FStar_FunctionalExtensionality.restricted_t ->
        ('a, Prims.bool) FStar_FunctionalExtensionality.restricted_t
  =
  fun x ->
    fun s ->
      FStar_FunctionalExtensionality.on_domain
        (fun x' -> (Prims.op_Negation (x = x')) && (s x'))
let rec list_remove : 'a . 'a -> 'a Prims.list -> 'a Prims.list =
  fun x ->
    fun xs ->
      match xs with
      | [] -> []
      | x'::xs1 ->
          if x = x' then list_remove x xs1 else x' :: (list_remove x xs1)
let remove : 'a . 'a -> 'a set -> 'a set =
  fun x -> fun s -> intro_set (set_remove x s) ()
type ('a, 's, 'x) notin = unit