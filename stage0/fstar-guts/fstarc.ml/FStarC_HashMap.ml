open Prims
type ('k, 'v) hashmap = ('k * 'v) FStarC_PIMap.t
type ('k, 'v) t = ('k, 'v) hashmap
let empty (uu___ : unit) : ('k, 'v) hashmap= FStarC_PIMap.empty ()
let add (uu___ : 'k FStarC_Class_Deq.deq)
  (uu___1 : 'k FStarC_Class_Hashable.hashable) (key : 'k) (value : 'v)
  (m : ('k, 'v) hashmap) : ('k, 'v) hashmap=
  let uu___2 =
    let uu___3 = FStarC_Class_Hashable.hash uu___1 key in
    FStarC_Hash.to_int uu___3 in
  FStarC_PIMap.add m uu___2 (key, value)
let remove (uu___ : 'k FStarC_Class_Deq.deq)
  (uu___1 : 'k FStarC_Class_Hashable.hashable) (key : 'k)
  (m : ('k, 'v) hashmap) : ('k, 'v) hashmap=
  let uu___2 =
    let uu___3 = FStarC_Class_Hashable.hash uu___1 key in
    FStarC_Hash.to_int uu___3 in
  FStarC_PIMap.remove m uu___2
let lookup (uu___ : 'k FStarC_Class_Deq.deq)
  (uu___1 : 'k FStarC_Class_Hashable.hashable) (key : 'k)
  (m : ('k, 'v) hashmap) : 'v FStar_Pervasives_Native.option=
  let uu___2 =
    let uu___3 =
      let uu___4 = FStarC_Class_Hashable.hash uu___1 key in
      FStarC_Hash.to_int uu___4 in
    FStarC_PIMap.try_find m uu___3 in
  match uu___2 with
  | FStar_Pervasives_Native.Some (key', v1) when
      FStarC_Class_Deq.op_Equals_Question uu___ key key' ->
      FStar_Pervasives_Native.Some v1
  | uu___3 -> FStar_Pervasives_Native.None
let get (uu___ : 'k FStarC_Class_Deq.deq)
  (uu___1 : 'k FStarC_Class_Hashable.hashable) (key : 'k)
  (m : ('k, 'v) hashmap) : 'v=
  let uu___2 = lookup uu___ uu___1 key m in
  FStar_Pervasives_Native.__proj__Some__item__v uu___2
let mem (uu___ : 'k FStarC_Class_Deq.deq)
  (uu___1 : 'k FStarC_Class_Hashable.hashable) (key : 'k)
  (m : ('k, 'v) hashmap) : Prims.bool=
  let uu___2 = lookup uu___ uu___1 key m in
  FStar_Pervasives_Native.uu___is_Some uu___2
let fold (uu___ : 'k FStarC_Class_Deq.deq)
  (uu___1 : 'k FStarC_Class_Hashable.hashable) (f : 'k -> 'v -> 'a -> 'a)
  (m : ('k, 'v) hashmap) (init : 'a) : 'a=
  FStarC_PIMap.fold m
    (fun uu___2 uu___3 a1 -> match uu___3 with | (k1, v1) -> f k1 v1 a1) init
let cached_fun (uu___ : 'a FStarC_Class_Hashable.hashable)
  (uu___1 : 'a FStarC_Class_Deq.deq) (f : 'a -> 'b) :
  (('a -> 'b) * (unit -> unit))=
  let cache = let uu___2 = empty () in FStarC_Effect.mk_ref uu___2 in
  let f_cached x =
    let uu___2 =
      let uu___3 = FStarC_Effect.op_Bang cache in
      lookup uu___1 uu___ x uu___3 in
    match uu___2 with
    | FStar_Pervasives_Native.Some y -> y
    | FStar_Pervasives_Native.None ->
        let y = f x in
        ((let uu___4 =
            let uu___5 = FStarC_Effect.op_Bang cache in
            add uu___1 uu___ x y uu___5 in
          FStarC_Effect.op_Colon_Equals cache uu___4);
         y) in
  (f_cached,
    (fun uu___2 ->
       let uu___3 = empty () in FStarC_Effect.op_Colon_Equals cache uu___3))
