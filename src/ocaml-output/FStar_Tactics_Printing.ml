open Prims
let (term_to_string :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> Prims.string) =
  fun e ->
    fun t ->
      FStar_Syntax_Print.term_to_string' e.FStar_TypeChecker_Env.dsenv t
let (goal_to_string_verbose : FStar_Tactics_Types.goal -> Prims.string) =
  fun g ->
    let uu____15 =
      FStar_Syntax_Print.ctx_uvar_to_string
        g.FStar_Tactics_Types.goal_ctx_uvar in
    let uu____16 =
      let uu____17 = FStar_Tactics_Types.check_goal_solved' g in
      match uu____17 with
      | FStar_Pervasives_Native.None -> ""
      | FStar_Pervasives_Native.Some t ->
          let uu____21 =
            let uu____22 = FStar_Tactics_Types.goal_env g in
            term_to_string uu____22 t in
          FStar_Util.format1 "\tGOAL ALREADY SOLVED!: %s" uu____21 in
    FStar_Util.format2 "%s%s\n" uu____15 uu____16
let (unshadow :
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.term))
  =
  fun bs ->
    fun t ->
      let s b = FStar_Ident.string_of_id b.FStar_Syntax_Syntax.ppname in
      let sset bv s1 =
        let uu____58 =
          let uu____61 =
            FStar_Ident.range_of_id bv.FStar_Syntax_Syntax.ppname in
          FStar_Pervasives_Native.Some uu____61 in
        FStar_Syntax_Syntax.gen_bv s1 uu____58 bv.FStar_Syntax_Syntax.sort in
      let fresh_until b f =
        let rec aux i =
          let t1 =
            let uu____85 =
              let uu____86 = FStar_Util.string_of_int i in
              Prims.op_Hat "'" uu____86 in
            Prims.op_Hat b uu____85 in
          let uu____87 = f t1 in
          if uu____87 then t1 else aux (i + Prims.int_one) in
        let uu____89 = f b in if uu____89 then b else aux Prims.int_zero in
      let rec go seen subst bs1 bs' t1 =
        match bs1 with
        | [] ->
            let uu____187 = FStar_Syntax_Subst.subst subst t1 in
            ((FStar_List.rev bs'), uu____187)
        | b::bs2 ->
            let b1 =
              let uu____231 = FStar_Syntax_Subst.subst_binders subst [b] in
              match uu____231 with
              | b1::[] -> b1
              | uu____269 -> failwith "impossible: unshadow subst_binders" in
            let uu____276 = b1 in
            (match uu____276 with
             | (bv0, q) ->
                 let nbs =
                   let uu____302 = s bv0 in
                   fresh_until uu____302
                     (fun s1 -> Prims.op_Negation (FStar_List.mem s1 seen)) in
                 let bv = sset bv0 nbs in
                 let b2 = (bv, q) in
                 let uu____315 =
                   let uu____318 =
                     let uu____321 =
                       let uu____322 =
                         let uu____329 = FStar_Syntax_Syntax.bv_to_name bv in
                         (bv0, uu____329) in
                       FStar_Syntax_Syntax.NT uu____322 in
                     [uu____321] in
                   FStar_List.append subst uu____318 in
                 go (nbs :: seen) uu____315 bs2 (b2 :: bs') t1) in
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
            let uu____379 = FStar_Options.print_implicits () in
            if uu____379
            then
              let uu____380 = FStar_Tactics_Types.goal_env g in
              let uu____381 = FStar_Tactics_Types.goal_witness g in
              term_to_string uu____380 uu____381
            else
              (let uu____383 = FStar_Tactics_Types.check_goal_solved' g in
               match uu____383 with
               | FStar_Pervasives_Native.None -> "_"
               | FStar_Pervasives_Native.Some t ->
                   let uu____387 = FStar_Tactics_Types.goal_env g in
                   let uu____388 = FStar_Tactics_Types.goal_witness g in
                   term_to_string uu____387 uu____388) in
          let num =
            match maybe_num with
            | FStar_Pervasives_Native.None -> ""
            | FStar_Pervasives_Native.Some (i, n) ->
                let uu____400 = FStar_Util.string_of_int i in
                let uu____401 = FStar_Util.string_of_int n in
                FStar_Util.format2 " %s/%s" uu____400 uu____401 in
          let maybe_label =
            match g.FStar_Tactics_Types.label with
            | "" -> ""
            | l -> Prims.op_Hat " (" (Prims.op_Hat l ")") in
          let goal_binders =
            (g.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_binders in
          let goal_ty =
            (g.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_typ in
          let uu____416 = unshadow goal_binders goal_ty in
          match uu____416 with
          | (goal_binders1, goal_ty1) ->
              let actual_goal =
                if ps.FStar_Tactics_Types.tac_verb_dbg
                then goal_to_string_verbose g
                else
                  (let uu____425 =
                     FStar_Syntax_Print.binders_to_string ", " goal_binders1 in
                   let uu____426 =
                     let uu____427 = FStar_Tactics_Types.goal_env g in
                     term_to_string uu____427 goal_ty1 in
                   FStar_Util.format3 "%s |- %s : %s\n" uu____425 w uu____426) in
              FStar_Util.format4 "%s%s%s:\n%s\n" kind num maybe_label
                actual_goal
let (ps_to_string :
  (Prims.string * FStar_Tactics_Types.proofstate) -> Prims.string) =
  fun uu____436 ->
    match uu____436 with
    | (msg, ps) ->
        let p_imp imp =
          FStar_Syntax_Print.uvar_to_string
            (imp.FStar_TypeChecker_Common.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_head in
        let n_active = FStar_List.length ps.FStar_Tactics_Types.goals in
        let n_smt = FStar_List.length ps.FStar_Tactics_Types.smt_goals in
        let n = n_active + n_smt in
        let uu____452 =
          let uu____455 =
            let uu____458 =
              let uu____459 =
                FStar_Util.string_of_int ps.FStar_Tactics_Types.depth in
              FStar_Util.format2 "State dump @ depth %s (%s):\n" uu____459
                msg in
            let uu____460 =
              let uu____463 =
                if
                  ps.FStar_Tactics_Types.entry_range <>
                    FStar_Range.dummyRange
                then
                  let uu____464 =
                    FStar_Range.string_of_def_range
                      ps.FStar_Tactics_Types.entry_range in
                  FStar_Util.format1 "Location: %s\n" uu____464
                else "" in
              let uu____466 =
                let uu____469 =
                  let uu____470 =
                    FStar_TypeChecker_Env.debug
                      ps.FStar_Tactics_Types.main_context
                      (FStar_Options.Other "Imp") in
                  if uu____470
                  then
                    let uu____471 =
                      FStar_Common.string_of_list p_imp
                        ps.FStar_Tactics_Types.all_implicits in
                    FStar_Util.format1 "Imps: %s\n" uu____471
                  else "" in
                [uu____469] in
              uu____463 :: uu____466 in
            uu____458 :: uu____460 in
          let uu____473 =
            let uu____476 =
              FStar_List.mapi
                (fun i ->
                   fun g ->
                     goal_to_string "Goal"
                       (FStar_Pervasives_Native.Some ((Prims.int_one + i), n))
                       ps g) ps.FStar_Tactics_Types.goals in
            let uu____487 =
              FStar_List.mapi
                (fun i ->
                   fun g ->
                     goal_to_string "SMT Goal"
                       (FStar_Pervasives_Native.Some
                          (((Prims.int_one + n_active) + i), n)) ps g)
                ps.FStar_Tactics_Types.smt_goals in
            FStar_List.append uu____476 uu____487 in
          FStar_List.append uu____455 uu____473 in
        FStar_String.concat "" uu____452
let (goal_to_json : FStar_Tactics_Types.goal -> FStar_Util.json) =
  fun g ->
    let g_binders =
      (g.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_binders in
    let g_type = FStar_Tactics_Types.goal_type g in
    let uu____513 = unshadow g_binders g_type in
    match uu____513 with
    | (g_binders1, g_type1) ->
        let j_binders =
          let uu____521 =
            let uu____522 = FStar_Tactics_Types.goal_env g in
            FStar_TypeChecker_Env.dsenv uu____522 in
          FStar_Syntax_Print.binders_to_json uu____521 g_binders1 in
        let uu____523 =
          let uu____530 =
            let uu____537 =
              let uu____542 =
                let uu____543 =
                  let uu____550 =
                    let uu____555 =
                      let uu____556 =
                        let uu____557 = FStar_Tactics_Types.goal_env g in
                        let uu____558 = FStar_Tactics_Types.goal_witness g in
                        term_to_string uu____557 uu____558 in
                      FStar_Util.JsonStr uu____556 in
                    ("witness", uu____555) in
                  let uu____559 =
                    let uu____566 =
                      let uu____571 =
                        let uu____572 =
                          let uu____573 = FStar_Tactics_Types.goal_env g in
                          term_to_string uu____573 g_type1 in
                        FStar_Util.JsonStr uu____572 in
                      ("type", uu____571) in
                    [uu____566;
                    ("label",
                      (FStar_Util.JsonStr (g.FStar_Tactics_Types.label)))] in
                  uu____550 :: uu____559 in
                FStar_Util.JsonAssoc uu____543 in
              ("goal", uu____542) in
            [uu____537] in
          ("hyps", j_binders) :: uu____530 in
        FStar_Util.JsonAssoc uu____523
let (ps_to_json :
  (Prims.string * FStar_Tactics_Types.proofstate) -> FStar_Util.json) =
  fun uu____610 ->
    match uu____610 with
    | (msg, ps) ->
        let uu____617 =
          let uu____624 =
            let uu____631 =
              let uu____638 =
                let uu____645 =
                  let uu____650 =
                    let uu____651 =
                      FStar_List.map goal_to_json
                        ps.FStar_Tactics_Types.goals in
                    FStar_Util.JsonList uu____651 in
                  ("goals", uu____650) in
                let uu____654 =
                  let uu____661 =
                    let uu____666 =
                      let uu____667 =
                        FStar_List.map goal_to_json
                          ps.FStar_Tactics_Types.smt_goals in
                      FStar_Util.JsonList uu____667 in
                    ("smt-goals", uu____666) in
                  [uu____661] in
                uu____645 :: uu____654 in
              ("depth", (FStar_Util.JsonInt (ps.FStar_Tactics_Types.depth)))
                :: uu____638 in
            ("label", (FStar_Util.JsonStr msg)) :: uu____631 in
          let uu____690 =
            if ps.FStar_Tactics_Types.entry_range <> FStar_Range.dummyRange
            then
              let uu____703 =
                let uu____708 =
                  FStar_Range.json_of_def_range
                    ps.FStar_Tactics_Types.entry_range in
                ("location", uu____708) in
              [uu____703]
            else [] in
          FStar_List.append uu____624 uu____690 in
        FStar_Util.JsonAssoc uu____617
let (do_dump_proofstate :
  FStar_Tactics_Types.proofstate -> Prims.string -> unit) =
  fun ps ->
    fun msg ->
      let uu____736 =
        let uu____737 = FStar_Options.silent () in
        Prims.op_Negation uu____737 in
      if uu____736
      then
        FStar_Options.with_saved_options
          (fun uu____741 ->
             FStar_Options.set_option "print_effect_args"
               (FStar_Options.Bool true);
             FStar_Util.print_generic "proof-state" ps_to_string ps_to_json
               (msg, ps);
             FStar_Util.flush_stdout ())
      else ()