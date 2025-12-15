open Fstarcompiler
open Prims
exception Appears 
let uu___is_Appears (projectee : Prims.exn) : Prims.bool=
  match projectee with | Appears -> true | uu___ -> false
let name_appears_in (nm : FStarC_Reflection_Types.name)
  (t : FStar_Tactics_NamedView.term) :
  (Prims.bool, unit) FStar_Tactics_Effect.tac_repr=
  fun ps ->
    let x t1 ps1 =
      let x1 = FStar_Tactics_NamedView.inspect t1 ps1 in
      match x1 with
      | FStar_Tactics_NamedView.Tv_FVar fv ->
          (if (FStarC_Reflection_V2_Builtins.inspect_fv fv) = nm
           then FStarC_Tactics_V2_Builtins.raise_core Appears ps1
           else ();
           t1)
      | uu___ -> t1 in
    let x1 =
      FStarC_Tactics_V2_Builtins.catch
        (fun uu___ ps1 ->
           (let x3 = FStar_Tactics_Visit.visit_tm x t ps1 in ()); false) ps in
    match x1 with
    | Fstarcompiler.FStar_Pervasives.Inr x2 -> Obj.magic (Obj.repr x2)
    | Fstarcompiler.FStar_Pervasives.Inl (Appears) ->
        Obj.magic (Obj.repr true)
    | Fstarcompiler.FStar_Pervasives.Inl e ->
        Obj.magic (Obj.repr (FStarC_Tactics_V2_Builtins.raise_core e ps))
let _ =
  Fstarcompiler.FStarC_Tactics_Native.register_tactic
    "FStar.Tactics.Names.name_appears_in" (Prims.of_int (3))
    (fun psc ->
       fun ncb ->
         fun us ->
           fun args ->
             Fstarcompiler.FStarC_Tactics_InterpFuns.mk_tactic_interpretation_2
               "FStar.Tactics.Names.name_appears_in (plugin)"
               (Fstarcompiler.FStarC_Tactics_Native.from_tactic_2
                  name_appears_in)
               (Fstarcompiler.FStarC_Syntax_Embeddings.e_list
                  Fstarcompiler.FStarC_Syntax_Embeddings.e_string)
               Fstarcompiler.FStarC_Reflection_V2_Embeddings.e_term
               Fstarcompiler.FStarC_Syntax_Embeddings.e_bool psc ncb us args)
