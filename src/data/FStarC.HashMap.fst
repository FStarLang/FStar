module FStarC.HashMap

(* This is implemented with a red black tree. We should use an actual hash table *)

open FStarC
open FStarC.Effect
open FStarC.Class.Hashable

let hashmap (k v : Type) : Tot Type0 =
  PIMap.t (k & v)

let empty (#k #v : _) : hashmap k v
  = PIMap.empty ()

let add (#k #v : _)
  {| deq k |}
  {| hashable k |}
  (key : k)
  (value : v)
  (m : hashmap k v)
  : hashmap k v
  = PIMap.add m (Hash.to_int <| hash key) (key, value)

let remove (#k #v : _)
  {| deq k |}
  {| hashable k |}
  (key : k)
  (m : hashmap k v)
  : hashmap k v
  = PIMap.remove m (Hash.to_int <| hash key) // coarse

let lookup (#k #v : _)
  {| deq k |}
  {| hashable k |}
  (key : k)
  (m : hashmap k v)
  : option v
  = match PIMap.try_find m (Hash.to_int <| hash key) with
    | Some (key', v) when key =? key' -> Some v
    | _ -> None

(* lookup |> Some?.v *)
let get (#k #v : _)
  {| deq k |}
  {| hashable k |}
  (key : k)
  (m : hashmap k v)
  : v
  = Some?.v (lookup key m)

let mem (#k #v : _)
  {| deq k |}
  {| hashable k |}
  (key : k)
  (m : hashmap k v)
  : bool
  = Some? (lookup key m)

let cached_fun (#a #b : Type) {| hashable a |} {| deq a |} (f : a -> b) =
  let cache = mk_ref (empty #a #b) in
  let f_cached =
    fun x ->
      match lookup x (!cache) with
      | Some y -> y
      | None ->
        let y = f x in
        cache := add x y !cache;
        y
  in
  f_cached, (fun () -> cache := empty #a #b)

