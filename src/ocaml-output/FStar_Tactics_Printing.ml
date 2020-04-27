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
      let s b = FStar_Ident.text_of_id b.FStar_Syntax_Syntax.ppname  in
      let sset bv s1 =
        let uu____74 =
          let uu____77 =
            FStar_Ident.range_of_id bv.FStar_Syntax_Syntax.ppname  in
          FStar_Pervasives_Native.Some uu____77  in
        FStar_Syntax_Syntax.gen_bv s1 uu____74 bv.FStar_Syntax_Syntax.sort
         in
      let fresh_until b f =
        let rec aux i =
          let t1 =
            let uu____112 =
              let uu____114 = FStar_Util.string_of_int i  in
              Prims.op_Hat "'" uu____114  in
            Prims.op_Hat b uu____112  in
          let uu____117 = f t1  in
          if uu____117 then t1 else aux (i + Prims.int_one)  in
        let uu____124 = f b  in if uu____124 then b else aux Prims.int_zero
         in
      let rec go seen subst bs1 bs' t1 =
        match bs1 with
        | [] ->
            let uu____229 = FStar_Syntax_Subst.subst subst t1  in
            ((FStar_List.rev bs'), uu____229)
        | b::bs2 ->
            let b1 =
              let uu____273 = FStar_Syntax_Subst.subst_binders subst [b]  in
              match uu____273 with
              | b1::[] -> b1
              | uu____311 -> failwith "impossible: unshadow subst_binders"
               in
            let uu____319 = b1  in
            (match uu____319 with
             | (bv0,q) ->
                 let nbs =
                   let uu____346 = s bv0  in
                   fresh_until uu____346
                     (fun s1  -> Prims.op_Negation (FStar_List.mem s1 seen))
                    in
                 let bv = sset bv0 nbs  in
                 let b2 = (bv, q)  in
                 let uu____362 =
                   let uu____365 =
                     let uu____368 =
                       let uu____369 =
                         let uu____376 = FStar_Syntax_Syntax.bv_to_name bv
                            in
                         (bv0, uu____376)  in
                       FStar_Syntax_Syntax.NT uu____369  in
                     [uu____368]  in
                   FStar_List.append subst uu____365  in
                 go (nbs :: seen) uu____362 bs2 (b2 :: bs') t1)
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
            let uu____438 = FStar_Options.print_implicits ()  in
            if uu____438
            then
              let uu____442 = FStar_Tactics_Types.goal_env g  in
              let uu____443 = FStar_Tactics_Types.goal_witness g  in
              term_to_string uu____442 uu____443
            else
              (let uu____446 = FStar_Tactics_Types.check_goal_solved' g  in
               match uu____446 with
               | FStar_Pervasives_Native.None  -> "_"
               | FStar_Pervasives_Native.Some t ->
                   let uu____452 = FStar_Tactics_Types.goal_env g  in
                   let uu____453 = FStar_Tactics_Types.goal_witness g  in
                   term_to_string uu____452 uu____453)
             in
          let num =
            match maybe_num with
            | FStar_Pervasives_Native.None  -> ""
            | FStar_Pervasives_Native.Some (i,n) ->
                let uu____476 = FStar_Util.string_of_int i  in
                let uu____478 = FStar_Util.string_of_int n  in
                FStar_Util.format2 " %s/%s" uu____476 uu____478
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
          let uu____502 = unshadow goal_binders goal_ty  in
          match uu____502 with
          | (goal_binders1,goal_ty1) ->
              let actual_goal =
                if ps.FStar_Tactics_Types.tac_verb_dbg
                then goal_to_string_verbose g
                else
                  (let uu____516 =
                     FStar_Syntax_Print.binders_to_string ", " goal_binders1
                      in
                   let uu____519 =
                     let uu____521 = FStar_Tactics_Types.goal_env g  in
                     term_to_string uu____521 goal_ty1  in
                   FStar_Util.format3 "%s |- %s : %s\n" uu____516 w uu____519)
                 in
              FStar_Util.format4 "%s%s%s:\n%s\n" kind num maybe_label
                actual_goal
  
let (ps_to_string :
  (Prims.string * FStar_Tactics_Types.proofstate) -> Prims.string) =
  fun uu____535  ->
    match uu____535 with
    | (msg,ps) ->
        let p_imp imp =
          FStar_Syntax_Print.uvar_to_string
            (imp.FStar_TypeChecker_Common.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_head
           in
        let n_active = FStar_List.length ps.FStar_Tactics_Types.goals  in
        let n_smt = FStar_List.length ps.FStar_Tactics_Types.smt_goals  in
        let n = n_active + n_smt  in
        let uu____557 =
          let uu____561 =
            let uu____565 =
              let uu____567 =
                FStar_Util.string_of_int ps.FStar_Tactics_Types.depth  in
              FStar_Util.format2 "State dump @ depth %s (%s):\n" uu____567
                msg
               in
            let uu____570 =
              let uu____574 =
                if
                  ps.FStar_Tactics_Types.entry_range <>
                    FStar_Range.dummyRange
                then
                  let uu____578 =
                    FStar_Range.string_of_def_range
                      ps.FStar_Tactics_Types.entry_range
                     in
                  FStar_Util.format1 "Location: %s\n" uu____578
                else ""  in
              let uu____584 =
                let uu____588 =
                  let uu____590 =
                    FStar_TypeChecker_Env.debug
                      ps.FStar_Tactics_Types.main_context
                      (FStar_Options.Other "Imp")
                     in
                  if uu____590
                  then
                    let uu____595 =
                      FStar_Common.string_of_list p_imp
                        ps.FStar_Tactics_Types.all_implicits
                       in
                    FStar_Util.format1 "Imps: %s\n" uu____595
                  else ""  in
                [uu____588]  in
              uu____574 :: uu____584  in
            uu____565 :: uu____570  in
          let uu____605 =
            let uu____609 =
              FStar_List.mapi
                (fun i  ->
                   fun g  ->
                     goal_to_string "Goal"
                       (FStar_Pervasives_Native.Some ((Prims.int_one + i), n))
                       ps g) ps.FStar_Tactics_Types.goals
               in
            let uu____629 =
              FStar_List.mapi
                (fun i  ->
                   fun g  ->
                     goal_to_string "SMT Goal"
                       (FStar_Pervasives_Native.Some
                          (((Prims.int_one + n_active) + i), n)) ps g)
                ps.FStar_Tactics_Types.smt_goals
               in
            FStar_List.append uu____609 uu____629  in
          FStar_List.append uu____561 uu____605  in
        FStar_String.concat "" uu____557
  
let (goal_to_json : FStar_Tactics_Types.goal -> FStar_Util.json) =
  fun g  ->
    let g_binders =
      (g.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_binders
       in
    let g_type = FStar_Tactics_Types.goal_type g  in
    let uu____668 = unshadow g_binders g_type  in
    match uu____668 with
    | (g_binders1,g_type1) ->
        let j_binders =
          let uu____676 =
            let uu____677 = FStar_Tactics_Types.goal_env g  in
            FStar_TypeChecker_Env.dsenv uu____677  in
          FStar_Syntax_Print.binders_to_json uu____676 g_binders1  in
        let uu____678 =
          let uu____686 =
            let uu____694 =
              let uu____700 =
                let uu____701 =
                  let uu____709 =
                    let uu____715 =
                      let uu____716 =
                        let uu____718 = FStar_Tactics_Types.goal_env g  in
                        let uu____719 = FStar_Tactics_Types.goal_witness g
                           in
                        term_to_string uu____718 uu____719  in
                      FStar_Util.JsonStr uu____716  in
                    ("witness", uu____715)  in
                  let uu____722 =
                    let uu____730 =
                      let uu____736 =
                        let uu____737 =
                          let uu____739 = FStar_Tactics_Types.goal_env g  in
                          term_to_string uu____739 g_type1  in
                        FStar_Util.JsonStr uu____737  in
                      ("type", uu____736)  in
                    [uu____730;
                    ("label",
                      (FStar_Util.JsonStr (g.FStar_Tactics_Types.label)))]
                     in
                  uu____709 :: uu____722  in
                FStar_Util.JsonAssoc uu____701  in
              ("goal", uu____700)  in
            [uu____694]  in
          ("hyps", j_binders) :: uu____686  in
        FStar_Util.JsonAssoc uu____678
  
let (ps_to_json :
  (Prims.string * FStar_Tactics_Types.proofstate) -> FStar_Util.json) =
  fun uu____793  ->
    match uu____793 with
    | (msg,ps) ->
        let uu____803 =
          let uu____811 =
            let uu____819 =
              let uu____827 =
                let uu____835 =
                  let uu____841 =
                    let uu____842 =
                      FStar_List.map goal_to_json
                        ps.FStar_Tactics_Types.goals
                       in
                    FStar_Util.JsonList uu____842  in
                  ("goals", uu____841)  in
                let uu____847 =
                  let uu____855 =
                    let uu____861 =
                      let uu____862 =
                        FStar_List.map goal_to_json
                          ps.FStar_Tactics_Types.smt_goals
                         in
                      FStar_Util.JsonList uu____862  in
                    ("smt-goals", uu____861)  in
                  [uu____855]  in
                uu____835 :: uu____847  in
              ("depth", (FStar_Util.JsonInt (ps.FStar_Tactics_Types.depth)))
                :: uu____827
               in
            ("label", (FStar_Util.JsonStr msg)) :: uu____819  in
          let uu____896 =
            if ps.FStar_Tactics_Types.entry_range <> FStar_Range.dummyRange
            then
              let uu____912 =
                let uu____918 =
                  FStar_Range.json_of_def_range
                    ps.FStar_Tactics_Types.entry_range
                   in
                ("location", uu____918)  in
              [uu____912]
            else []  in
          FStar_List.append uu____811 uu____896  in
        FStar_Util.JsonAssoc uu____803
  
let (do_dump_proofstate :
  FStar_Tactics_Types.proofstate -> Prims.string -> unit) =
  fun ps  ->
    fun msg  ->
      let uu____956 =
        let uu____958 = FStar_Options.silent ()  in
        Prims.op_Negation uu____958  in
      if uu____956
      then
        FStar_Options.with_saved_options
          (fun uu____964  ->
             FStar_Options.set_option "print_effect_args"
               (FStar_Options.Bool true);
             FStar_Util.print_generic "proof-state" ps_to_string ps_to_json
               (msg, ps);
             FStar_Util.flush_stdout ())
      else ()
  