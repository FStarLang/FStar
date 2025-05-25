open Prims
let (gensym_st : Prims.int FStarC_Effect.ref) =
  FStarC_Effect.mk_ref Prims.int_zero
let (next_id : unit -> Prims.int) =
  fun uu___ ->
    let r = FStarC_Effect.op_Bang gensym_st in
    FStarC_Effect.op_Colon_Equals gensym_st (r + Prims.int_one); r
let (reset_gensym : unit -> unit) =
  fun uu___ -> FStarC_Effect.op_Colon_Equals gensym_st Prims.int_zero
let with_frozen_gensym : 'a . (unit -> 'a) -> 'a =
  fun f ->
    let v = FStarC_Effect.op_Bang gensym_st in
    let r =
      try (fun uu___ -> match () with | () -> f ()) ()
      with
      | uu___ ->
          (FStarC_Effect.op_Colon_Equals gensym_st v;
           FStarC_Effect.raise uu___) in
    FStarC_Effect.op_Colon_Equals gensym_st v; r
