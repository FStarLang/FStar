open Prims
let (term_to_string :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> Prims.string) =
  fun e  ->
    fun t  ->
      FStar_Syntax_Print.term_to_string' e.FStar_TypeChecker_Env.dsenv t
  
let (goal_to_string_verbose : FStar_Tactics_Types.goal -> Prims.string) =
  fun g  ->
    let uu____20 =
      FStar_Syntax_Print.ctx_uvar_to_string
        g.FStar_Tactics_Types.goal_ctx_uvar
       in
    let uu____22 =
      let uu____24 = FStar_Tactics_Types.check_goal_solved' g  in
      match uu____24 with
      | FStar_Pervasives_Native.None  -> ""
      | FStar_Pervasives_Native.Some t ->
          let uu____30 =
            let uu____32 = FStar_Tactics_Types.goal_env g  in
            term_to_string uu____32 t  in
          FStar_Util.format1 "\tGOAL ALREADY SOLVED!: %s" uu____30
       in
    FStar_Util.format2 "%s%s\n" uu____20 uu____22
  
let (unshadow :
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.term))
  =
  fun bs  ->
    fun t  ->
      let s b = (b.FStar_Syntax_Syntax.ppname).FStar_Ident.idText  in
      let sset bv s1 =
        FStar_Syntax_Syntax.gen_bv s1
          (FStar_Pervasives_Native.Some
             ((bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange))
          bv.FStar_Syntax_Syntax.sort
         in
      let fresh_until b f =
        let rec aux i =
          let t1 =
            let uu____108 =
              let uu____110 = FStar_Util.string_of_int i  in
              Prims.op_Hat "'" uu____110  in
            Prims.op_Hat b uu____108  in
          let uu____113 = f t1  in
          if uu____113 then t1 else aux (i + Prims.int_one)  in
        let uu____120 = f b  in if uu____120 then b else aux Prims.int_zero
         in
      let rec go seen subst bs1 bs' t1 =
        match bs1 with
        | [] ->
            let uu____225 = FStar_Syntax_Subst.subst subst t1  in
            ((FStar_List.rev bs'), uu____225)
        | b::bs2 ->
            let b1 =
              let uu____269 = FStar_Syntax_Subst.subst_binders subst [b]  in
              match uu____269 with
              | b1::[] -> b1
              | uu____307 -> failwith "impossible: unshadow subst_binders"
               in
            let uu____315 = b1  in
            (match uu____315 with
             | (bv0,q) ->
                 let nbs =
                   fresh_until (s bv0)
                     (fun s1  -> Prims.op_Negation (FStar_List.mem s1 seen))
                    in
                 let bv = sset bv0 nbs  in
                 let b2 = (bv, q)  in
                 let uu____356 =
                   let uu____359 =
                     let uu____362 =
                       let uu____363 =
                         let uu____370 = FStar_Syntax_Syntax.bv_to_name bv
                            in
                         (bv0, uu____370)  in
                       FStar_Syntax_Syntax.NT uu____363  in
                     [uu____362]  in
                   FStar_List.append subst uu____359  in
                 go (nbs :: seen) uu____356 bs2 (b2 :: bs') t1)
         in
      go [] [] bs [] t
  
let (goal_to_string :
  Prims.string ->
    (Prims.int * Prims.int) FStar_Pervasives_Native.option ->
      FStar_Tactics_Types.proofstate ->
        FStar_Tactics_Types.goal -> Prims.string)
  =
  fun kind  ->
    fun maybe_num  ->
      fun ps  ->
        fun g  ->
          let w =
            let uu____432 = FStar_Options.print_implicits ()  in
            if uu____432
            then
              let uu____436 = FStar_Tactics_Types.goal_env g  in
              let uu____437 = FStar_Tactics_Types.goal_witness g  in
              term_to_string uu____436 uu____437
            else
              (let uu____440 = FStar_Tactics_Types.check_goal_solved' g  in
               match uu____440 with
               | FStar_Pervasives_Native.None  -> "_"
               | FStar_Pervasives_Native.Some t ->
                   let uu____446 = FStar_Tactics_Types.goal_env g  in
                   let uu____447 = FStar_Tactics_Types.goal_witness g  in
                   term_to_string uu____446 uu____447)
             in
          let num =
            match maybe_num with
            | FStar_Pervasives_Native.None  -> ""
            | FStar_Pervasives_Native.Some (i,n) ->
                let uu____470 = FStar_Util.string_of_int i  in
                let uu____472 = FStar_Util.string_of_int n  in
                FStar_Util.format2 " %s/%s" uu____470 uu____472
             in
          let maybe_label =
            match g.FStar_Tactics_Types.label with
            | "" -> ""
            | l -> Prims.op_Hat " (" (Prims.op_Hat l ")")  in
          let goal_binders =
            (g.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_binders
             in
          let goal_ty =
            (g.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_typ
             in
          let uu____496 = unshadow goal_binders goal_ty  in
          match uu____496 with
          | (goal_binders1,goal_ty1) ->
              let actual_goal =
                if ps.FStar_Tactics_Types.tac_verb_dbg
                then goal_to_string_verbose g
                else
                  (let uu____510 =
                     FStar_Syntax_Print.binders_to_string ", " goal_binders1
                      in
                   let uu____513 =
                     let uu____515 = FStar_Tactics_Types.goal_env g  in
                     term_to_string uu____515 goal_ty1  in
                   FStar_Util.format3 "%s |- %s : %s\n" uu____510 w uu____513)
                 in
              FStar_Util.format4 "%s%s%s:\n%s\n" kind num maybe_label
                actual_goal
  
let (ps_to_string :
  (Prims.string * FStar_Tactics_Types.proofstate) -> Prims.string) =
  fun uu____529  ->
    match uu____529 with
    | (msg,ps) ->
        let p_imp imp =
          FStar_Syntax_Print.uvar_to_string
            (imp.FStar_TypeChecker_Common.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_head
           in
        let n_active = FStar_List.length ps.FStar_Tactics_Types.goals  in
        let n_smt = FStar_List.length ps.FStar_Tactics_Types.smt_goals  in
        let n = n_active + n_smt  in
        let uu____551 =
          let uu____555 =
            let uu____559 =
              let uu____561 =
                FStar_Util.string_of_int ps.FStar_Tactics_Types.depth  in
              FStar_Util.format2 "State dump @ depth %s (%s):\n" uu____561
                msg
               in
            let uu____564 =
              let uu____568 =
                if
                  ps.FStar_Tactics_Types.entry_range <>
                    FStar_Range.dummyRange
                then
                  let uu____572 =
                    FStar_Range.string_of_def_range
                      ps.FStar_Tactics_Types.entry_range
                     in
                  FStar_Util.format1 "Location: %s\n" uu____572
                else ""  in
              let uu____578 =
                let uu____582 =
                  let uu____584 =
                    FStar_TypeChecker_Env.debug
                      ps.FStar_Tactics_Types.main_context
                      (FStar_Options.Other "Imp")
                     in
                  if uu____584
                  then
                    let uu____589 =
                      FStar_Common.string_of_list p_imp
                        ps.FStar_Tactics_Types.all_implicits
                       in
                    FStar_Util.format1 "Imps: %s\n" uu____589
                  else ""  in
                [uu____582]  in
              uu____568 :: uu____578  in
            uu____559 :: uu____564  in
          let uu____599 =
            let uu____603 =
              FStar_List.mapi
                (fun i  ->
                   fun g  ->
                     goal_to_string "Goal"
                       (FStar_Pervasives_Native.Some ((Prims.int_one + i), n))
                       ps g) ps.FStar_Tactics_Types.goals
               in
            let uu____623 =
              FStar_List.mapi
                (fun i  ->
                   fun g  ->
                     goal_to_string "SMT Goal"
                       (FStar_Pervasives_Native.Some
                          (((Prims.int_one + n_active) + i), n)) ps g)
                ps.FStar_Tactics_Types.smt_goals
               in
            FStar_List.append uu____603 uu____623  in
          FStar_List.append uu____555 uu____599  in
        FStar_String.concat "" uu____551
  
let (goal_to_json : FStar_Tactics_Types.goal -> FStar_Util.json) =
  fun g  ->
    let g_binders =
      (g.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_binders
       in
    let g_type = FStar_Tactics_Types.goal_type g  in
    let uu____662 = unshadow g_binders g_type  in
    match uu____662 with
    | (g_binders1,g_type1) ->
        let j_binders =
          let uu____670 =
            let uu____671 = FStar_Tactics_Types.goal_env g  in
            FStar_TypeChecker_Env.dsenv uu____671  in
          FStar_Syntax_Print.binders_to_json uu____670 g_binders1  in
        let uu____672 =
          let uu____680 =
            let uu____688 =
              let uu____694 =
                let uu____695 =
                  let uu____703 =
                    let uu____709 =
                      let uu____710 =
                        let uu____712 = FStar_Tactics_Types.goal_env g  in
                        let uu____713 = FStar_Tactics_Types.goal_witness g
                           in
                        term_to_string uu____712 uu____713  in
                      FStar_Util.JsonStr uu____710  in
                    ("witness", uu____709)  in
                  let uu____716 =
                    let uu____724 =
                      let uu____730 =
                        let uu____731 =
                          let uu____733 = FStar_Tactics_Types.goal_env g  in
                          term_to_string uu____733 g_type1  in
                        FStar_Util.JsonStr uu____731  in
                      ("type", uu____730)  in
                    [uu____724;
                    ("label",
                      (FStar_Util.JsonStr (g.FStar_Tactics_Types.label)))]
                     in
                  uu____703 :: uu____716  in
                FStar_Util.JsonAssoc uu____695  in
              ("goal", uu____694)  in
            [uu____688]  in
          ("hyps", j_binders) :: uu____680  in
        FStar_Util.JsonAssoc uu____672
  
let (ps_to_json :
  (Prims.string * FStar_Tactics_Types.proofstate) -> FStar_Util.json) =
  fun uu____787  ->
    match uu____787 with
    | (msg,ps) ->
        let uu____797 =
          let uu____805 =
            let uu____813 =
              let uu____821 =
                let uu____829 =
                  let uu____835 =
                    let uu____836 =
                      FStar_List.map goal_to_json
                        ps.FStar_Tactics_Types.goals
                       in
                    FStar_Util.JsonList uu____836  in
                  ("goals", uu____835)  in
                let uu____841 =
                  let uu____849 =
                    let uu____855 =
                      let uu____856 =
                        FStar_List.map goal_to_json
                          ps.FStar_Tactics_Types.smt_goals
                         in
                      FStar_Util.JsonList uu____856  in
                    ("smt-goals", uu____855)  in
                  [uu____849]  in
                uu____829 :: uu____841  in
              ("depth", (FStar_Util.JsonInt (ps.FStar_Tactics_Types.depth)))
                :: uu____821
               in
            ("label", (FStar_Util.JsonStr msg)) :: uu____813  in
          let uu____890 =
            if ps.FStar_Tactics_Types.entry_range <> FStar_Range.dummyRange
            then
              let uu____906 =
                let uu____912 =
                  FStar_Range.json_of_def_range
                    ps.FStar_Tactics_Types.entry_range
                   in
                ("location", uu____912)  in
              [uu____906]
            else []  in
          FStar_List.append uu____805 uu____890  in
        FStar_Util.JsonAssoc uu____797
  
let (do_dump_proofstate :
  FStar_Tactics_Types.proofstate -> Prims.string -> unit) =
  fun ps  ->
    fun msg  ->
      let uu____950 =
        let uu____952 = FStar_Options.silent ()  in
        Prims.op_Negation uu____952  in
      if uu____950
      then
        FStar_Options.with_saved_options
          (fun uu____958  ->
             FStar_Options.set_option "print_effect_args"
               (FStar_Options.Bool true);
             FStar_Util.print_generic "proof-state" ps_to_string ps_to_json
               (msg, ps);
             FStar_Util.flush_stdout ())
      else ()
  