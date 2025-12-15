open Prims
let query_cache_ref : FStarC_Hash.hash_code FStarC_RBSet.t FStarC_Effect.ref=
  let uu___ =
    Obj.magic
      (FStarC_Class_Setlike.empty ()
         (Obj.magic
            (FStarC_RBSet.setlike_rbset FStarC_Class_Hashable.ord_hash_code))
         ()) in
  FStarC_Effect.mk_ref uu___
let on (uu___ : unit) : Prims.bool=
  (FStarC_Options.query_cache ()) && (FStarC_Options.ide ())
let query_cache_add (g : FStarC_TypeChecker_Env.env)
  (q : FStarC_Syntax_Syntax.term) : unit=
  let uu___ = on () in
  if uu___
  then
    let h =
      FStarC_Class_Hashable.hash
        (FStarC_Class_Hashable.hashable_tuple2
           FStarC_TypeChecker_Env.hashable_env
           FStarC_Syntax_Hash.hashable_term) (g, q) in
    let uu___1 =
      let uu___2 = FStarC_Effect.op_Bang query_cache_ref in
      Obj.magic
        (FStarC_Class_Setlike.add ()
           (Obj.magic
              (FStarC_RBSet.setlike_rbset FStarC_Class_Hashable.ord_hash_code))
           h (Obj.magic uu___2)) in
    FStarC_Effect.op_Colon_Equals query_cache_ref uu___1
  else ()
let try_find_query_cache (g : FStarC_TypeChecker_Env.env)
  (q : FStarC_Syntax_Syntax.term) : Prims.bool=
  let uu___ = on () in
  if uu___
  then
    let h =
      FStarC_Class_Hashable.hash
        (FStarC_Class_Hashable.hashable_tuple2
           FStarC_TypeChecker_Env.hashable_env
           FStarC_Syntax_Hash.hashable_term) (g, q) in
    let r =
      let uu___1 = FStarC_Effect.op_Bang query_cache_ref in
      FStarC_Class_Setlike.mem ()
        (Obj.magic
           (FStarC_RBSet.setlike_rbset FStarC_Class_Hashable.ord_hash_code))
        h (Obj.magic uu___1) in
    r
  else false
