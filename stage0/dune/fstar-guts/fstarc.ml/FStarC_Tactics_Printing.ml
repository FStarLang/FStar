open Prims
let dbg_Imp : Prims.bool FStarC_Effect.ref= FStarC_Debug.get_toggle "Imp"
let term_to_doc (e : FStarC_TypeChecker_Env.env)
  (t : FStarC_Syntax_Syntax.term) : FStar_Pprint.document=
  let uu___ =
    FStarC_Syntax_Print.term_to_doc' e.FStarC_TypeChecker_Env.dsenv t in
  FStar_Pprint.group uu___
let term_to_string (e : FStarC_TypeChecker_Env.env)
  (t : FStarC_Syntax_Syntax.term) : Prims.string=
  FStarC_Syntax_Print.term_to_string' e.FStarC_TypeChecker_Env.dsenv t
let unshadow (bs : FStarC_Syntax_Syntax.binders)
  (t : FStarC_Syntax_Syntax.term) :
  (FStarC_Syntax_Syntax.binders * FStarC_Syntax_Syntax.term)=
  let sset bv s =
    let uu___ =
      let uu___1 =
        let uu___2 =
          FStarC_Class_HasRange.pos FStarC_Syntax_Syntax.hasRange_bv bv in
        (s, uu___2) in
      FStarC_Ident.mk_ident uu___1 in
    {
      FStarC_Syntax_Syntax.ppname = uu___;
      FStarC_Syntax_Syntax.index = (bv.FStarC_Syntax_Syntax.index);
      FStarC_Syntax_Syntax.sort = (bv.FStarC_Syntax_Syntax.sort)
    } in
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
        ((FStarC_List.rev bs'), uu___)
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
                 (fun s -> Prims.op_Negation (FStarC_List.mem s seen)) in
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
               FStarC_List.op_At subst uu___2 in
             go (nbs :: seen) uu___1 bs2 (b2 :: bs') t1) in
  go [] [] bs [] t
let maybe_rename_binders (ps : FStarC_Tactics_Types.proofstate)
  (bs : FStarC_Syntax_Syntax.binders) (t : FStarC_Syntax_Syntax.term) :
  (FStarC_Syntax_Syntax.binders * FStarC_Syntax_Syntax.term)=
  let rename_binders subst bs1 =
    FStarC_List.map
      (fun uu___ ->
         let x = uu___.FStarC_Syntax_Syntax.binder_bv in
         let y =
           let uu___1 = FStarC_Syntax_Syntax.bv_to_name x in
           FStarC_Syntax_Subst.subst subst uu___1 in
         let uu___1 =
           let uu___2 = FStarC_Syntax_Subst.compress y in
           uu___2.FStarC_Syntax_Syntax.n in
         match uu___1 with
         | FStarC_Syntax_Syntax.Tm_name y1 ->
             let uu___2 =
               let uu___3 = uu___.FStarC_Syntax_Syntax.binder_bv in
               let uu___4 =
                 FStarC_Syntax_Subst.subst subst x.FStarC_Syntax_Syntax.sort in
               {
                 FStarC_Syntax_Syntax.ppname =
                   (uu___3.FStarC_Syntax_Syntax.ppname);
                 FStarC_Syntax_Syntax.index =
                   (uu___3.FStarC_Syntax_Syntax.index);
                 FStarC_Syntax_Syntax.sort = uu___4
               } in
             {
               FStarC_Syntax_Syntax.binder_bv = uu___2;
               FStarC_Syntax_Syntax.binder_qual =
                 (uu___.FStarC_Syntax_Syntax.binder_qual);
               FStarC_Syntax_Syntax.binder_positivity =
                 (uu___.FStarC_Syntax_Syntax.binder_positivity);
               FStarC_Syntax_Syntax.binder_attrs =
                 (uu___.FStarC_Syntax_Syntax.binder_attrs)
             }
         | uu___2 -> failwith "Not a renaming") bs1 in
  let uu___ = FStarC_Options.tactic_raw_binders () in
  if uu___
  then (bs, t)
  else
    (let subst =
       FStarC_TypeChecker_Primops_Base.psc_subst ps.FStarC_Tactics_Types.psc in
     let bs1 = rename_binders subst bs in
     let t1 = FStarC_Syntax_Subst.subst subst t in (bs1, t1))
let goal_to_doc (kind : Prims.string)
  (maybe_num : (Prims.int * Prims.int) FStar_Pervasives_Native.option)
  (ps : FStarC_Tactics_Types.proofstate) (g : FStarC_Tactics_Types.goal) :
  FStar_Pprint.document=
  let w =
    let uu___ = FStarC_Options.print_implicits () in
    if uu___
    then
      let uu___1 = FStarC_Tactics_Types.goal_env g in
      let uu___2 = FStarC_Tactics_Types.goal_witness g in
      term_to_doc uu___1 uu___2
    else
      (let uu___2 = FStarC_Tactics_Types.check_goal_solved' g in
       match uu___2 with
       | FStar_Pervasives_Native.None -> FStar_Pprint.doc_of_string "_"
       | FStar_Pervasives_Native.Some t ->
           let uu___3 = FStarC_Tactics_Types.goal_env g in
           let uu___4 = FStarC_Tactics_Types.goal_witness g in
           term_to_doc uu___3 uu___4) in
  let num =
    match maybe_num with
    | FStar_Pervasives_Native.None -> FStar_Pprint.empty
    | FStar_Pervasives_Native.Some (i, n) ->
        let uu___ = FStarC_Class_PP.pp FStarC_Class_PP.pp_int i in
        let uu___1 =
          let uu___2 = FStarC_Class_PP.pp FStarC_Class_PP.pp_int n in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.slash uu___2 in
        FStar_Pprint.op_Hat_Hat uu___ uu___1 in
  let maybe_label =
    if g.FStarC_Tactics_Types.label = ""
    then FStar_Pprint.empty
    else
      FStar_Pprint.op_Hat_Hat (FStar_Pprint.break_ Prims.int_one)
        (FStar_Pprint.parens
           (FStar_Pprint.doc_of_string g.FStarC_Tactics_Types.label)) in
  let uu___ =
    let uu___1 = FStarC_Tactics_Types.goal_type g in
    (((g.FStarC_Tactics_Types.goal_ctx_uvar).FStarC_Syntax_Syntax.ctx_uvar_binders),
      uu___1) in
  match uu___ with
  | (goal_binders, goal_ty) ->
      let uu___1 = maybe_rename_binders ps goal_binders goal_ty in
      (match uu___1 with
       | (goal_binders1, goal_ty1) ->
           let uu___2 = unshadow goal_binders1 goal_ty1 in
           (match uu___2 with
            | (goal_binders2, goal_ty2) ->
                let pp_binder b =
                  let uu___3 =
                    let uu___4 =
                      let uu___5 =
                        let uu___6 =
                          let uu___7 =
                            let uu___8 =
                              FStarC_Class_PP.pp
                                FStarC_Syntax_Print.pretty_bv
                                b.FStarC_Syntax_Syntax.binder_bv in
                            FStar_Pprint.op_Hat_Slash_Hat uu___8
                              FStar_Pprint.colon in
                          FStar_Pprint.group uu___7 in
                        let uu___7 =
                          FStarC_Class_PP.pp FStarC_Syntax_Print.pretty_term
                            (b.FStarC_Syntax_Syntax.binder_bv).FStarC_Syntax_Syntax.sort in
                        FStar_Pprint.op_Hat_Slash_Hat uu___6 uu___7 in
                      FStar_Pprint.parens uu___5 in
                    FStar_Pprint.hang (Prims.of_int (2)) uu___4 in
                  FStar_Pprint.group uu___3 in
                let uu___3 =
                  let uu___4 =
                    let uu___5 =
                      let uu___6 =
                        FStarC_Pprint.separate_map
                          (FStar_Pprint.op_Hat_Hat FStar_Pprint.comma
                             (FStar_Pprint.break_ Prims.int_one)) pp_binder
                          goal_binders2 in
                      let uu___7 =
                        let uu___8 =
                          let uu___9 =
                            let uu___10 =
                              let uu___11 =
                                let uu___12 = FStarC_Tactics_Types.goal_env g in
                                term_to_doc uu___12 goal_ty2 in
                              FStar_Pprint.op_Hat_Slash_Hat
                                FStar_Pprint.colon uu___11 in
                            FStar_Pprint.op_Hat_Slash_Hat w uu___10 in
                          FStar_Pprint.op_Hat_Slash_Hat
                            (FStar_Pprint.doc_of_string "|-") uu___9 in
                        FStar_Pprint.group uu___8 in
                      FStar_Pprint.op_Hat_Slash_Hat uu___6 uu___7 in
                    FStar_Pprint.op_Hat_Slash_Hat maybe_label uu___5 in
                  FStar_Pprint.op_Hat_Hat
                    (FStar_Pprint.group
                       (FStar_Pprint.op_Hat_Slash_Hat
                          (FStar_Pprint.doc_of_string kind) num)) uu___4 in
                FStar_Pprint.hang (Prims.of_int (2)) uu___3))
let goal_to_string (kind : Prims.string)
  (maybe_num : (Prims.int * Prims.int) FStar_Pervasives_Native.option)
  (ps : FStarC_Tactics_Types.proofstate) (g : FStarC_Tactics_Types.goal) :
  Prims.string=
  let uu___ =
    let uu___1 = goal_to_doc kind maybe_num ps g in
    FStar_Pprint.render uu___1 in
  Prims.strcat uu___ "\n"
let goal_to_string_verbose (g : FStarC_Tactics_Types.goal) : Prims.string=
  let uu___ =
    let uu___1 =
      FStarC_Class_PP.pp FStarC_Syntax_Print.pretty_uvar
        (g.FStarC_Tactics_Types.goal_ctx_uvar).FStarC_Syntax_Syntax.ctx_uvar_head in
    FStar_Pprint.render uu___1 in
  Prims.strcat uu___ "\n"
let ps_to_doc (uu___ : (Prims.string * FStarC_Tactics_Types.proofstate)) :
  FStar_Pprint.document=
  match uu___ with
  | (msg, ps) ->
      let p_imp imp =
        FStarC_Class_PP.pp FStarC_Syntax_Print.pretty_uvar
          (imp.FStarC_TypeChecker_Common.imp_uvar).FStarC_Syntax_Syntax.ctx_uvar_head in
      let n_active = FStarC_List.length ps.FStarC_Tactics_Types.goals in
      let n_smt = FStarC_List.length ps.FStarC_Tactics_Types.smt_goals in
      let n = n_active + n_smt in
      let uu___1 =
        let uu___2 =
          let uu___3 =
            FStarC_Class_Show.show FStarC_Class_Show.showable_int
              ps.FStarC_Tactics_Types.depth in
          FStarC_Format.fmt2 "State dump @ depth %s (%s):" uu___3 msg in
        FStar_Pprint.doc_of_string uu___2 in
      let uu___2 =
        let uu___3 =
          let uu___4 =
            let uu___5 =
              if
                ps.FStarC_Tactics_Types.entry_range <>
                  FStarC_Range_Type.dummyRange
              then
                let uu___6 =
                  let uu___7 =
                    FStarC_Class_PP.pp FStarC_Range_Ops.pretty_range
                      ps.FStarC_Tactics_Types.entry_range in
                  FStar_Pprint.op_Hat_Hat uu___7 FStar_Pprint.hardline in
                FStar_Pprint.op_Hat_Hat
                  (FStar_Pprint.doc_of_string "Location: ") uu___6
              else FStar_Pprint.empty in
            FStar_Pprint.group uu___5 in
          let uu___5 =
            let uu___6 =
              let uu___7 =
                let uu___8 = FStarC_Effect.op_Bang dbg_Imp in
                if uu___8
                then
                  let uu___9 =
                    let uu___10 =
                      FStarC_Pprint.separate_map FStar_Pprint.comma p_imp
                        ps.FStarC_Tactics_Types.all_implicits in
                    FStar_Pprint.op_Hat_Hat uu___10 FStar_Pprint.hardline in
                  FStar_Pprint.op_Hat_Hat
                    (FStar_Pprint.doc_of_string "Imps: ") uu___9
                else FStar_Pprint.empty in
              FStar_Pprint.group uu___7 in
            let uu___7 =
              let uu___8 =
                let uu___9 =
                  let uu___10 =
                    FStarC_List.mapi
                      (fun i g ->
                         goal_to_doc "Goal"
                           (FStar_Pervasives_Native.Some
                              ((Prims.int_one + i), n)) ps g)
                      ps.FStarC_Tactics_Types.goals in
                  let uu___11 =
                    FStarC_List.mapi
                      (fun i g ->
                         goal_to_doc "SMT Goal"
                           (FStar_Pervasives_Native.Some
                              (((Prims.int_one + n_active) + i), n)) ps g)
                      ps.FStarC_Tactics_Types.smt_goals in
                  FStarC_List.op_At uu___10 uu___11 in
                FStar_Pprint.separate FStar_Pprint.hardline uu___9 in
              FStar_Pprint.op_Hat_Hat uu___8 FStar_Pprint.hardline in
            FStar_Pprint.op_Hat_Hat uu___6 uu___7 in
          FStar_Pprint.op_Hat_Hat uu___4 uu___5 in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu___3 in
      FStar_Pprint.op_Hat_Hat uu___1 uu___2
let ps_to_string (uu___ : (Prims.string * FStarC_Tactics_Types.proofstate)) :
  Prims.string=
  match uu___ with
  | (msg, ps) ->
      let uu___1 =
        let uu___2 = ps_to_doc (msg, ps) in FStar_Pprint.render uu___2 in
      Prims.strcat uu___1 "\n"
let goal_to_json (g : FStarC_Tactics_Types.goal) : FStarC_Json.json=
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
let ps_to_json (uu___ : (Prims.string * FStarC_Tactics_Types.proofstate)) :
  FStarC_Json.json=
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
                      FStarC_List.map goal_to_json
                        ps.FStarC_Tactics_Types.goals in
                    FStarC_Json.JsonList uu___8 in
                  ("goals", uu___7) in
                let uu___7 =
                  let uu___8 =
                    let uu___9 =
                      let uu___10 =
                        FStarC_List.map goal_to_json
                          ps.FStarC_Tactics_Types.smt_goals in
                      FStarC_Json.JsonList uu___10 in
                    ("smt-goals", uu___9) in
                  [uu___8] in
                uu___6 :: uu___7 in
              ("urgency",
                (FStarC_Json.JsonInt (ps.FStarC_Tactics_Types.urgency))) ::
                uu___5 in
            ("depth", (FStarC_Json.JsonInt (ps.FStarC_Tactics_Types.depth)))
              :: uu___4 in
          ("label", (FStarC_Json.JsonStr msg)) :: uu___3 in
        let uu___3 =
          if
            ps.FStarC_Tactics_Types.entry_range <>
              FStarC_Range_Type.dummyRange
          then
            let uu___4 =
              let uu___5 =
                let uu___6 =
                  FStarC_Range_Ops.refind_range
                    ps.FStarC_Tactics_Types.entry_range in
                FStarC_Range_Ops.json_of_def_range uu___6 in
              ("location", uu___5) in
            [uu___4]
          else [] in
        FStarC_List.op_At uu___2 uu___3 in
      FStarC_Json.JsonAssoc uu___1
let do_dump_proofstate (ps : FStarC_Tactics_Types.proofstate)
  (msg : Prims.string) : unit=
  let uu___ =
    (let uu___1 = FStarC_Options.silent () in Prims.op_Negation uu___1) ||
      (FStarC_Options.interactive ()) in
  if uu___
  then
    FStarC_Options.with_saved_options
      (fun uu___1 ->
         FStarC_Options.set_option "print_effect_args"
           (FStarC_Options.Bool true);
         FStarC_Format.print_generic "proof-state" ps_to_string ps_to_json
           (msg, ps);
         FStarC_Format.flush_stdout ())
  else ()
