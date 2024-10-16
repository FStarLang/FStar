open Prims
let (dbg_Imp : Prims.bool FStarC_Compiler_Effect.ref) =
  FStarC_Compiler_Debug.get_toggle "Imp"
let (term_to_string :
  FStarC_TypeChecker_Env.env -> FStarC_Syntax_Syntax.term -> Prims.string) =
  fun e ->
    fun t ->
      FStarC_Syntax_Print.term_to_string' e.FStarC_TypeChecker_Env.dsenv t
let (goal_to_string_verbose : FStarC_Tactics_Types.goal -> Prims.string) =
  fun g ->
    let uu___ =
      FStarC_Class_Show.show FStarC_Syntax_Print.showable_ctxu
        g.FStarC_Tactics_Types.goal_ctx_uvar in
    let uu___1 =
      let uu___2 = FStarC_Tactics_Types.check_goal_solved' g in
      match uu___2 with
      | FStar_Pervasives_Native.None -> ""
      | FStar_Pervasives_Native.Some t ->
          let uu___3 =
            let uu___4 = FStarC_Tactics_Types.goal_env g in
            term_to_string uu___4 t in
          FStarC_Compiler_Util.format1 "\tGOAL ALREADY SOLVED!: %s" uu___3 in
    FStarC_Compiler_Util.format2 "%s%s\n" uu___ uu___1
let (unshadow :
  FStarC_Syntax_Syntax.binders ->
    FStarC_Syntax_Syntax.term ->
      (FStarC_Syntax_Syntax.binders * FStarC_Syntax_Syntax.term))
  =
  fun bs ->
    fun t ->
      let sset bv s =
        let uu___ =
          let uu___1 =
            FStarC_Ident.range_of_id bv.FStarC_Syntax_Syntax.ppname in
          FStar_Pervasives_Native.Some uu___1 in
        FStarC_Syntax_Syntax.gen_bv s uu___ bv.FStarC_Syntax_Syntax.sort in
      let fresh_until b f =
        let rec aux i =
          let t1 =
            let uu___ =
              let uu___1 =
                FStarC_Class_Show.show FStarC_Class_Show.showable_int i in
              Prims.strcat "'" uu___1 in
            Prims.strcat b uu___ in
          let uu___ = f t1 in if uu___ then t1 else aux (i + Prims.int_one) in
        let uu___ = f b in if uu___ then b else aux Prims.int_zero in
      let rec go seen subst bs1 bs' t1 =
        match bs1 with
        | [] ->
            let uu___ = FStarC_Syntax_Subst.subst subst t1 in
            ((FStarC_Compiler_List.rev bs'), uu___)
        | b::bs2 ->
            let b1 =
              let uu___ = FStarC_Syntax_Subst.subst_binders subst [b] in
              match uu___ with
              | b2::[] -> b2
              | uu___1 -> failwith "impossible: unshadow subst_binders" in
            let uu___ =
              ((b1.FStarC_Syntax_Syntax.binder_bv),
                (b1.FStarC_Syntax_Syntax.binder_qual)) in
            (match uu___ with
             | (bv0, q) ->
                 let nbs =
                   let uu___1 =
                     FStarC_Class_Show.show FStarC_Ident.showable_ident
                       bv0.FStarC_Syntax_Syntax.ppname in
                   fresh_until uu___1
                     (fun s ->
                        Prims.op_Negation (FStarC_Compiler_List.mem s seen)) in
                 let bv = sset bv0 nbs in
                 let b2 =
                   FStarC_Syntax_Syntax.mk_binder_with_attrs bv q
                     b1.FStarC_Syntax_Syntax.binder_positivity
                     b1.FStarC_Syntax_Syntax.binder_attrs in
                 let uu___1 =
                   let uu___2 =
                     let uu___3 =
                       let uu___4 =
                         let uu___5 = FStarC_Syntax_Syntax.bv_to_name bv in
                         (bv0, uu___5) in
                       FStarC_Syntax_Syntax.NT uu___4 in
                     [uu___3] in
                   FStarC_Compiler_List.op_At subst uu___2 in
                 go (nbs :: seen) uu___1 bs2 (b2 :: bs') t1) in
      go [] [] bs [] t
let (goal_to_string :
  Prims.string ->
    (Prims.int * Prims.int) FStar_Pervasives_Native.option ->
      FStarC_Tactics_Types.proofstate ->
        FStarC_Tactics_Types.goal -> Prims.string)
  =
  fun kind ->
    fun maybe_num ->
      fun ps ->
        fun g ->
          let w =
            let uu___ = FStarC_Options.print_implicits () in
            if uu___
            then
              let uu___1 = FStarC_Tactics_Types.goal_env g in
              let uu___2 = FStarC_Tactics_Types.goal_witness g in
              term_to_string uu___1 uu___2
            else
              (let uu___2 = FStarC_Tactics_Types.check_goal_solved' g in
               match uu___2 with
               | FStar_Pervasives_Native.None -> "_"
               | FStar_Pervasives_Native.Some t ->
                   let uu___3 = FStarC_Tactics_Types.goal_env g in
                   let uu___4 = FStarC_Tactics_Types.goal_witness g in
                   term_to_string uu___3 uu___4) in
          let num =
            match maybe_num with
            | FStar_Pervasives_Native.None -> ""
            | FStar_Pervasives_Native.Some (i, n) ->
                let uu___ =
                  FStarC_Class_Show.show FStarC_Class_Show.showable_int i in
                let uu___1 =
                  FStarC_Class_Show.show FStarC_Class_Show.showable_int n in
                FStarC_Compiler_Util.format2 " %s/%s" uu___ uu___1 in
          let maybe_label =
            match g.FStarC_Tactics_Types.label with
            | "" -> ""
            | l -> Prims.strcat " (" (Prims.strcat l ")") in
          let uu___ =
            let rename_binders subst bs =
              FStarC_Compiler_List.map
                (fun uu___1 ->
                   let x = uu___1.FStarC_Syntax_Syntax.binder_bv in
                   let y =
                     let uu___2 = FStarC_Syntax_Syntax.bv_to_name x in
                     FStarC_Syntax_Subst.subst subst uu___2 in
                   let uu___2 =
                     let uu___3 = FStarC_Syntax_Subst.compress y in
                     uu___3.FStarC_Syntax_Syntax.n in
                   match uu___2 with
                   | FStarC_Syntax_Syntax.Tm_name y1 ->
                       let uu___3 =
                         let uu___4 = uu___1.FStarC_Syntax_Syntax.binder_bv in
                         let uu___5 =
                           FStarC_Syntax_Subst.subst subst
                             x.FStarC_Syntax_Syntax.sort in
                         {
                           FStarC_Syntax_Syntax.ppname =
                             (uu___4.FStarC_Syntax_Syntax.ppname);
                           FStarC_Syntax_Syntax.index =
                             (uu___4.FStarC_Syntax_Syntax.index);
                           FStarC_Syntax_Syntax.sort = uu___5
                         } in
                       {
                         FStarC_Syntax_Syntax.binder_bv = uu___3;
                         FStarC_Syntax_Syntax.binder_qual =
                           (uu___1.FStarC_Syntax_Syntax.binder_qual);
                         FStarC_Syntax_Syntax.binder_positivity =
                           (uu___1.FStarC_Syntax_Syntax.binder_positivity);
                         FStarC_Syntax_Syntax.binder_attrs =
                           (uu___1.FStarC_Syntax_Syntax.binder_attrs)
                       }
                   | uu___3 -> failwith "Not a renaming") bs in
            let goal_binders =
              (g.FStarC_Tactics_Types.goal_ctx_uvar).FStarC_Syntax_Syntax.ctx_uvar_binders in
            let goal_ty = FStarC_Tactics_Types.goal_type g in
            let uu___1 = FStarC_Options.tactic_raw_binders () in
            if uu___1
            then (goal_binders, goal_ty)
            else
              (let subst =
                 FStarC_TypeChecker_Primops_Base.psc_subst
                   ps.FStarC_Tactics_Types.psc in
               let binders = rename_binders subst goal_binders in
               let ty = FStarC_Syntax_Subst.subst subst goal_ty in
               (binders, ty)) in
          match uu___ with
          | (goal_binders, goal_ty) ->
              let uu___1 = unshadow goal_binders goal_ty in
              (match uu___1 with
               | (goal_binders1, goal_ty1) ->
                   let actual_goal =
                     if ps.FStarC_Tactics_Types.tac_verb_dbg
                     then goal_to_string_verbose g
                     else
                       (let uu___3 =
                          let uu___4 =
                            FStarC_Compiler_List.map
                              FStarC_Syntax_Print.binder_to_string_with_type
                              goal_binders1 in
                          FStarC_Compiler_String.concat ", " uu___4 in
                        let uu___4 =
                          let uu___5 = FStarC_Tactics_Types.goal_env g in
                          term_to_string uu___5 goal_ty1 in
                        FStarC_Compiler_Util.format3 "%s |- %s : %s\n" uu___3
                          w uu___4) in
                   FStarC_Compiler_Util.format4 "%s%s%s:\n%s\n" kind num
                     maybe_label actual_goal)
let (ps_to_string :
  (Prims.string * FStarC_Tactics_Types.proofstate) -> Prims.string) =
  fun uu___ ->
    match uu___ with
    | (msg, ps) ->
        let p_imp imp =
          FStarC_Class_Show.show FStarC_Syntax_Print.showable_uvar
            (imp.FStarC_TypeChecker_Common.imp_uvar).FStarC_Syntax_Syntax.ctx_uvar_head in
        let n_active =
          FStarC_Compiler_List.length ps.FStarC_Tactics_Types.goals in
        let n_smt =
          FStarC_Compiler_List.length ps.FStarC_Tactics_Types.smt_goals in
        let n = n_active + n_smt in
        let uu___1 =
          let uu___2 =
            let uu___3 =
              let uu___4 =
                FStarC_Class_Show.show FStarC_Class_Show.showable_int
                  ps.FStarC_Tactics_Types.depth in
              FStarC_Compiler_Util.format2 "State dump @ depth %s (%s):\n"
                uu___4 msg in
            let uu___4 =
              let uu___5 =
                if
                  ps.FStarC_Tactics_Types.entry_range <>
                    FStarC_Compiler_Range_Type.dummyRange
                then
                  let uu___6 =
                    FStarC_Compiler_Range_Ops.string_of_def_range
                      ps.FStarC_Tactics_Types.entry_range in
                  FStarC_Compiler_Util.format1 "Location: %s\n" uu___6
                else "" in
              let uu___6 =
                let uu___7 =
                  let uu___8 = FStarC_Compiler_Effect.op_Bang dbg_Imp in
                  if uu___8
                  then
                    let uu___9 =
                      (FStarC_Common.string_of_list ()) p_imp
                        ps.FStarC_Tactics_Types.all_implicits in
                    FStarC_Compiler_Util.format1 "Imps: %s\n" uu___9
                  else "" in
                [uu___7] in
              uu___5 :: uu___6 in
            uu___3 :: uu___4 in
          let uu___3 =
            let uu___4 =
              FStarC_Compiler_List.mapi
                (fun i ->
                   fun g ->
                     goal_to_string "Goal"
                       (FStar_Pervasives_Native.Some ((Prims.int_one + i), n))
                       ps g) ps.FStarC_Tactics_Types.goals in
            let uu___5 =
              FStarC_Compiler_List.mapi
                (fun i ->
                   fun g ->
                     goal_to_string "SMT Goal"
                       (FStar_Pervasives_Native.Some
                          (((Prims.int_one + n_active) + i), n)) ps g)
                ps.FStarC_Tactics_Types.smt_goals in
            FStarC_Compiler_List.op_At uu___4 uu___5 in
          FStarC_Compiler_List.op_At uu___2 uu___3 in
        FStarC_Compiler_String.concat "" uu___1
let (goal_to_json : FStarC_Tactics_Types.goal -> FStarC_Json.json) =
  fun g ->
    let g_binders =
      (g.FStarC_Tactics_Types.goal_ctx_uvar).FStarC_Syntax_Syntax.ctx_uvar_binders in
    let g_type = FStarC_Tactics_Types.goal_type g in
    let uu___ = unshadow g_binders g_type in
    match uu___ with
    | (g_binders1, g_type1) ->
        let j_binders =
          let uu___1 =
            let uu___2 = FStarC_Tactics_Types.goal_env g in
            FStarC_TypeChecker_Env.dsenv uu___2 in
          FStarC_Syntax_Print.binders_to_json uu___1 g_binders1 in
        let uu___1 =
          let uu___2 =
            let uu___3 =
              let uu___4 =
                let uu___5 =
                  let uu___6 =
                    let uu___7 =
                      let uu___8 =
                        let uu___9 = FStarC_Tactics_Types.goal_env g in
                        let uu___10 = FStarC_Tactics_Types.goal_witness g in
                        term_to_string uu___9 uu___10 in
                      FStarC_Json.JsonStr uu___8 in
                    ("witness", uu___7) in
                  let uu___7 =
                    let uu___8 =
                      let uu___9 =
                        let uu___10 =
                          let uu___11 = FStarC_Tactics_Types.goal_env g in
                          term_to_string uu___11 g_type1 in
                        FStarC_Json.JsonStr uu___10 in
                      ("type", uu___9) in
                    [uu___8;
                    ("label",
                      (FStarC_Json.JsonStr (g.FStarC_Tactics_Types.label)))] in
                  uu___6 :: uu___7 in
                FStarC_Json.JsonAssoc uu___5 in
              ("goal", uu___4) in
            [uu___3] in
          ("hyps", j_binders) :: uu___2 in
        FStarC_Json.JsonAssoc uu___1
let (ps_to_json :
  (Prims.string * FStarC_Tactics_Types.proofstate) -> FStarC_Json.json) =
  fun uu___ ->
    match uu___ with
    | (msg, ps) ->
        let uu___1 =
          let uu___2 =
            let uu___3 =
              let uu___4 =
                let uu___5 =
                  let uu___6 =
                    let uu___7 =
                      let uu___8 =
                        FStarC_Compiler_List.map goal_to_json
                          ps.FStarC_Tactics_Types.goals in
                      FStarC_Json.JsonList uu___8 in
                    ("goals", uu___7) in
                  let uu___7 =
                    let uu___8 =
                      let uu___9 =
                        let uu___10 =
                          FStarC_Compiler_List.map goal_to_json
                            ps.FStarC_Tactics_Types.smt_goals in
                        FStarC_Json.JsonList uu___10 in
                      ("smt-goals", uu___9) in
                    [uu___8] in
                  uu___6 :: uu___7 in
                ("urgency",
                  (FStarC_Json.JsonInt (ps.FStarC_Tactics_Types.urgency))) ::
                  uu___5 in
              ("depth",
                (FStarC_Json.JsonInt (ps.FStarC_Tactics_Types.depth))) ::
                uu___4 in
            ("label", (FStarC_Json.JsonStr msg)) :: uu___3 in
          let uu___3 =
            if
              ps.FStarC_Tactics_Types.entry_range <>
                FStarC_Compiler_Range_Type.dummyRange
            then
              let uu___4 =
                let uu___5 =
                  FStarC_Compiler_Range_Ops.json_of_def_range
                    ps.FStarC_Tactics_Types.entry_range in
                ("location", uu___5) in
              [uu___4]
            else [] in
          FStarC_Compiler_List.op_At uu___2 uu___3 in
        FStarC_Json.JsonAssoc uu___1
let (do_dump_proofstate :
  FStarC_Tactics_Types.proofstate -> Prims.string -> unit) =
  fun ps ->
    fun msg ->
      let uu___ =
        (let uu___1 = FStarC_Options.silent () in Prims.op_Negation uu___1)
          || (FStarC_Options.interactive ()) in
      if uu___
      then
        FStarC_Options.with_saved_options
          (fun uu___1 ->
             FStarC_Options.set_option "print_effect_args"
               (FStarC_Options.Bool true);
             FStarC_Compiler_Util.print_generic "proof-state" ps_to_string
               ps_to_json (msg, ps);
             FStarC_Compiler_Util.flush_stdout ())
      else ()