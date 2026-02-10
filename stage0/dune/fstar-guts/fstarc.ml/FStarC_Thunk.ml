open Prims
type 'a thunk = (unit -> 'a, 'a) FStar_Pervasives.either FStarC_Effect.ref
type 'a t = 'a thunk
let mk (f : unit -> 'a) : 'a thunk=
  FStarC_Effect.alloc (FStar_Pervasives.Inl f)
let mkv (v : 'a) : 'a thunk= FStarC_Effect.alloc (FStar_Pervasives.Inr v)
let force (t1 : 'a thunk) : 'a=
  let uu___ = FStarC_Effect.op_Bang t1 in
  match uu___ with
  | FStar_Pervasives.Inr a1 -> a1
  | FStar_Pervasives.Inl f ->
      let a1 = f () in
      (FStarC_Effect.op_Colon_Equals t1 (FStar_Pervasives.Inr a1); a1)
let map (f : 'a -> 'b) (t1 : 'a thunk) : 'b thunk=
  mk (fun uu___ -> let uu___1 = force t1 in f uu___1)
