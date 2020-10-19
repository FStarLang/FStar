open Prims
let (term_to_string :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> Prims.string) =
  fun e ->
    fun t ->
      FStar_Syntax_Print.term_to_string' e.FStar_TypeChecker_Env.dsenv t
let (goal_to_string_verbose : FStar_Tactics_Types.goal -> Prims.string) =
  fun g ->
    let uu___ =
      FStar_Syntax_Print.ctx_uvar_to_string
        g.FStar_Tactics_Types.goal_ctx_uvar in
    let uu___1 =
      let uu___2 = FStar_Tactics_Types.check_goal_solved' g in
      match uu___2 with
      | FStar_Pervasives_Native.None -> ""
      | FStar_Pervasives_Native.Some t ->
          let uu___3 =
            let uu___4 = FStar_Tactics_Types.goal_env g in
            term_to_string uu___4 t in
          FStar_Util.format1 "\tGOAL ALREADY SOLVED!: %s" uu___3 in
    FStar_Util.format2 "%s%s\n" uu___ uu___1
let (unshadow :
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.term))
  =
  fun bs ->
    fun t ->
      let s b = FStar_Ident.string_of_id b.FStar_Syntax_Syntax.ppname in
      let sset bv s1 =
        let uu___ =
          let uu___1 = FStar_Ident.range_of_id bv.FStar_Syntax_Syntax.ppname in
          FStar_Pervasives_Native.Some uu___1 in
        FStar_Syntax_Syntax.gen_bv s1 uu___ bv.FStar_Syntax_Syntax.sort in
      let fresh_until b f =
        let rec aux i =
          let t1 =
            let uu___ =
              let uu___1 = FStar_Util.string_of_int i in
              Prims.op_Hat "'" uu___1 in
            Prims.op_Hat b uu___ in
          let uu___ = f t1 in if uu___ then t1 else aux (i + Prims.int_one) in
        let uu___ = f b in if uu___ then b else aux Prims.int_zero in
      let rec go seen subst bs1 bs' t1 =
        match bs1 with
        | [] ->
            let uu___ = FStar_Syntax_Subst.subst subst t1 in
            ((FStar_List.rev bs'), uu___)
        | b::bs2 ->
            let b1 =
              let uu___ = FStar_Syntax_Subst.subst_binders subst [b] in
              match uu___ with
              | b2::[] -> b2
              | uu___1 -> failwith "impossible: unshadow subst_binders" in
            let uu___ = b1 in
            (match uu___ with
             | (bv0, q) ->
                 let nbs =
                   let uu___1 = s bv0 in
                   fresh_until uu___1
                     (fun s1 -> Prims.op_Negation (FStar_List.mem s1 seen)) in
                 let bv = sset bv0 nbs in
                 let b2 = (bv, q) in
                 let uu___1 =
                   let uu___2 =
                     let uu___3 =
                       let uu___4 =
                         let uu___5 = FStar_Syntax_Syntax.bv_to_name bv in
                         (bv0, uu___5) in
                       FStar_Syntax_Syntax.NT uu___4 in
                     [uu___3] in
                   FStar_List.append subst uu___2 in
                 go (nbs :: seen) uu___1 bs2 (b2 :: bs') t1) in
      go [] [] bs [] t
let (goal_to_string :
  Prims.string ->
    (Prims.int * Prims.int) FStar_Pervasives_Native.option ->
      FStar_Tactics_Types.proofstate ->
        FStar_Tactics_Types.goal -> Prims.string)
  =
  fun kind ->
    fun maybe_num ->
      fun ps ->
        fun g ->
          let w =
            let uu___ = FStar_Options.print_implicits () in
            if uu___
            then
              let uu___1 = FStar_Tactics_Types.goal_env g in
              let uu___2 = FStar_Tactics_Types.goal_witness g in
              term_to_string uu___1 uu___2
            else
              (let uu___2 = FStar_Tactics_Types.check_goal_solved' g in
               match uu___2 with
               | FStar_Pervasives_Native.None -> "_"
               | FStar_Pervasives_Native.Some t ->
                   let uu___3 = FStar_Tactics_Types.goal_env g in
                   let uu___4 = FStar_Tactics_Types.goal_witness g in
                   term_to_string uu___3 uu___4) in
          let num =
            match maybe_num with
            | FStar_Pervasives_Native.None -> ""
            | FStar_Pervasives_Native.Some (i, n) ->
                let uu___ = FStar_Util.string_of_int i in
                let uu___1 = FStar_Util.string_of_int n in
                FStar_Util.format2 " %s/%s" uu___ uu___1 in
          let maybe_label =
            match g.FStar_Tactics_Types.label with
            | "" -> ""
            | l -> Prims.op_Hat " (" (Prims.op_Hat l ")") in
          let goal_binders =
            (g.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_binders in
          let goal_ty =
            (g.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_typ in
          let uu___ = unshadow goal_binders goal_ty in
          match uu___ with
          | (goal_binders1, goal_ty1) ->
              let actual_goal =
                if ps.FStar_Tactics_Types.tac_verb_dbg
                then goal_to_string_verbose g
                else
                  (let uu___2 =
                     FStar_Syntax_Print.binders_to_string ", " goal_binders1 in
                   let uu___3 =
                     let uu___4 = FStar_Tactics_Types.goal_env g in
                     term_to_string uu___4 goal_ty1 in
                   FStar_Util.format3 "%s |- %s : %s\n" uu___2 w uu___3) in
              FStar_Util.format4 "%s%s%s:\n%s\n" kind num maybe_label
                actual_goal
let (ps_to_string :
  (Prims.string * FStar_Tactics_Types.proofstate) -> Prims.string) =
  fun uu___ ->
    match uu___ with
    | (msg, ps) ->
        let p_imp imp =
          FStar_Syntax_Print.uvar_to_string
            (imp.FStar_TypeChecker_Common.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_head in
        let n_active = FStar_List.length ps.FStar_Tactics_Types.goals in
        let n_smt = FStar_List.length ps.FStar_Tactics_Types.smt_goals in
        let n = n_active + n_smt in
        let uu___1 =
          let uu___2 =
            let uu___3 =
              let uu___4 =
                FStar_Util.string_of_int ps.FStar_Tactics_Types.depth in
              FStar_Util.format2 "State dump @ depth %s (%s):\n" uu___4 msg in
            let uu___4 =
              let uu___5 =
                if
                  ps.FStar_Tactics_Types.entry_range <>
                    FStar_Range.dummyRange
                then
                  let uu___6 =
                    FStar_Range.string_of_def_range
                      ps.FStar_Tactics_Types.entry_range in
                  FStar_Util.format1 "Location: %s\n" uu___6
                else "" in
              let uu___6 =
                let uu___7 =
                  let uu___8 =
                    FStar_TypeChecker_Env.debug
                      ps.FStar_Tactics_Types.main_context
                      (FStar_Options.Other "Imp") in
                  if uu___8
                  then
                    let uu___9 =
                      FStar_Common.string_of_list p_imp
                        ps.FStar_Tactics_Types.all_implicits in
                    FStar_Util.format1 "Imps: %s\n" uu___9
                  else "" in
                [uu___7] in
              uu___5 :: uu___6 in
            uu___3 :: uu___4 in
          let uu___3 =
            let uu___4 =
              FStar_List.mapi
                (fun i ->
                   fun g ->
                     goal_to_string "Goal"
                       (FStar_Pervasives_Native.Some ((Prims.int_one + i), n))
                       ps g) ps.FStar_Tactics_Types.goals in
            let uu___5 =
              FStar_List.mapi
                (fun i ->
                   fun g ->
                     goal_to_string "SMT Goal"
                       (FStar_Pervasives_Native.Some
                          (((Prims.int_one + n_active) + i), n)) ps g)
                ps.FStar_Tactics_Types.smt_goals in
            FStar_List.append uu___4 uu___5 in
          FStar_List.append uu___2 uu___3 in
        FStar_String.concat "" uu___1
let (goal_to_json : FStar_Tactics_Types.goal -> FStar_Util.json) =
  fun g ->
    let g_binders =
      (g.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_binders in
    let g_type = FStar_Tactics_Types.goal_type g in
    let uu___ = unshadow g_binders g_type in
    match uu___ with
    | (g_binders1, g_type1) ->
        let j_binders =
          let uu___1 =
            let uu___2 = FStar_Tactics_Types.goal_env g in
            FStar_TypeChecker_Env.dsenv uu___2 in
          FStar_Syntax_Print.binders_to_json uu___1 g_binders1 in
        let uu___1 =
          let uu___2 =
            let uu___3 =
              let uu___4 =
                let uu___5 =
                  let uu___6 =
                    let uu___7 =
                      let uu___8 =
                        let uu___9 = FStar_Tactics_Types.goal_env g in
                        let uu___10 = FStar_Tactics_Types.goal_witness g in
                        term_to_string uu___9 uu___10 in
                      FStar_Util.JsonStr uu___8 in
                    ("witness", uu___7) in
                  let uu___7 =
                    let uu___8 =
                      let uu___9 =
                        let uu___10 =
                          let uu___11 = FStar_Tactics_Types.goal_env g in
                          term_to_string uu___11 g_type1 in
                        FStar_Util.JsonStr uu___10 in
                      ("type", uu___9) in
                    [uu___8;
                    ("label",
                      (FStar_Util.JsonStr (g.FStar_Tactics_Types.label)))] in
                  uu___6 :: uu___7 in
                FStar_Util.JsonAssoc uu___5 in
              ("goal", uu___4) in
            [uu___3] in
          ("hyps", j_binders) :: uu___2 in
        FStar_Util.JsonAssoc uu___1
let (ps_to_json :
  (Prims.string * FStar_Tactics_Types.proofstate) -> FStar_Util.json) =
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
                        FStar_List.map goal_to_json
                          ps.FStar_Tactics_Types.goals in
                      FStar_Util.JsonList uu___8 in
                    ("goals", uu___7) in
                  let uu___7 =
                    let uu___8 =
                      let uu___9 =
                        let uu___10 =
                          FStar_List.map goal_to_json
                            ps.FStar_Tactics_Types.smt_goals in
                        FStar_Util.JsonList uu___10 in
                      ("smt-goals", uu___9) in
                    [uu___8] in
                  uu___6 :: uu___7 in
                ("urgency",
                  (FStar_Util.JsonInt (ps.FStar_Tactics_Types.urgency))) ::
                  uu___5 in
              ("depth", (FStar_Util.JsonInt (ps.FStar_Tactics_Types.depth)))
                :: uu___4 in
            ("label", (FStar_Util.JsonStr msg)) :: uu___3 in
          let uu___3 =
            if ps.FStar_Tactics_Types.entry_range <> FStar_Range.dummyRange
            then
              let uu___4 =
                let uu___5 =
                  FStar_Range.json_of_def_range
                    ps.FStar_Tactics_Types.entry_range in
                ("location", uu___5) in
              [uu___4]
            else [] in
          FStar_List.append uu___2 uu___3 in
        FStar_Util.JsonAssoc uu___1
let (do_dump_proofstate :
  FStar_Tactics_Types.proofstate -> Prims.string -> unit) =
  fun ps ->
    fun msg ->
      let uu___ =
        let uu___1 = FStar_Options.silent () in Prims.op_Negation uu___1 in
      if uu___
      then
        FStar_Options.with_saved_options
          (fun uu___1 ->
             FStar_Options.set_option "print_effect_args"
               (FStar_Options.Bool true);
             FStar_Util.print_generic "proof-state" ps_to_string ps_to_json
               (msg, ps);
             FStar_Util.flush_stdout ())
      else ()