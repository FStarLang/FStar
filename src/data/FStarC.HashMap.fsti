module FStarC.HashMap

(* A finite map keyed by hash code. Keys with colliding hash codes are kept
apart (and compared with the deq instance), so this is an exact map, as long
as keys that are equal according to deq have equal hash codes. *)

open FStarC.Effect
open FStarC.Class.Deq
open FStarC.Class.Hashable

val hashmap (k v : Type) : Type0

type t = hashmap

val empty (#k #v : _) : hashmap k v

val add (#k #v : _)
  {| deq k |}
  {| hashable k |}
  (key : k)
  (value : v)
  (m : hashmap k v)
: ML (hashmap k v)

val remove (#k #v : _)
  {| deq k |}
  {| hashable k |}
  (key : k)
  (m : hashmap k v)
  : ML (hashmap k v)

val lookup (#k #v : _)
  {| deq k |}
  {| hashable k |}
  (key : k)
  (m : hashmap k v)
  : ML (option v)

(* lookup |> Some?.v *)
val get (#k #v : _)
  {| deq k |}
  {| hashable k |}
  (key : k)
  (m : hashmap k v)
  : ML v

val mem (#k #v : _)
  {| deq k |}
  {| hashable k |}
  (key : k)
  (m : hashmap k v)
  : ML bool

val fold (#k #v : _)
  {| deq k |}
  {| hashable k |}
  (f : k -> v -> 'a -> ML 'a)
  (m : hashmap k v)
  (init:'a)
: ML 'a

val cached_fun (#a #b : Type) {| hashable a |} {| deq a |} (f : a -> ML b)
  : ML ((a -> ML b) & (unit -> ML unit))
