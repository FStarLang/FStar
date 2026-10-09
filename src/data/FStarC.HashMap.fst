module FStarC.HashMap

open FStarC.Class.Deq
(* This is implemented with a red black tree. We should use an actual hash table *)

open FStarC
open FStarC.Effect
open FStarC.Class.Hashable

(* Each hash code maps to a bucket of the entries with that hash code, so
collisions are kept apart rather than overwriting each other. *)
let hashmap (k v : Type) : Tot Type0 =
  PIMap.t (list (k & v))

let empty (#k #v : _) : hashmap k v
  = PIMap.empty ()

let bucket (#k #v : _) {| hashable k |} (key : k) (m : hashmap k v)
  : ML (int & list (k & v))
  = let h = Hash.to_int <| hash key in
    h, (match PIMap.try_find m h with Some b -> b | None -> [])

let add (#k #v : _)
  {| deq k |}
  {| hashable k |}
  (key : k)
  (value : v)
  (m : hashmap k v)
  
  = let h, b = bucket key m in
    PIMap.add m h ((key, value) :: List.filter (fun (key', _) -> not (key =? key')) b)

let remove (#k #v : _)
  {| deq k |}
  {| hashable k |}
  (key : k)
  (m : hashmap k v)
  
  = let h, b = bucket key m in
    match List.filter (fun (key', _) -> not (key =? key')) b with
    | [] -> PIMap.remove m h
    | b -> PIMap.add m h b

let lookup (#k #v : _)
  {| deq k |}
  {| hashable k |}
  (key : k)
  (m : hashmap k v)
  
  = let _, b = bucket key m in
    match List.tryFind (fun (key', _) -> key =? key') b with
    | Some (_, v) -> Some v
    | None -> None

(* lookup |> Some?.v *)
let get (#k #v : _)
  {| deq k |}
  {| hashable k |}
  (key : k)
  (m : hashmap k v)
  
  = Some?.v (lookup key m)

let mem (#k #v : _)
  {| deq k |}
  {| hashable k |}
  (key : k)
  (m : hashmap k v)
  
  = Some? (lookup key m)


let fold (#k #v : _)
  {| deq k |}
  {| hashable k |}
  (f : k -> v -> 'a -> ML 'a)
  (m : hashmap k v)
  (init:'a)
: ML 'a
= PIMap.fold m (fun _ b a -> List.fold_left (fun a (k,v) -> f k v a) a b) init

let cached_fun (#a #b : Type) {| hashable a |} {| deq a |} (f : a -> ML b) =
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