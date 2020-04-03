open Prims
let (goal_to_string_verbose : FStar_Tactics_Types.goal -> Prims.string) =
  fun g  ->
    let uu____7 =
      FStar_Syntax_Print.ctx_uvar_to_string
        g.FStar_Tactics_Types.goal_ctx_uvar
       in
    let uu____9 =
      let uu____11 = FStar_Tactics_Types.check_goal_solved' g  in
      match uu____11 with
      | FStar_Pervasives_Native.None  -> ""
      | FStar_Pervasives_Native.Some t ->
          let uu____17 = FStar_Syntax_Print.term_to_string t  in
          FStar_Util.format1 "\tGOAL ALREADY SOLVED!: %s" uu____17
       in
    FStar_Util.format2 "%s%s\n" uu____7 uu____9
  
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
            let uu____94 =
              let uu____96 = FStar_Util.string_of_int i  in
              Prims.op_Hat "'" uu____96  in
            Prims.op_Hat b uu____94  in
          let uu____99 = f t1  in
          if uu____99 then t1 else aux (i + Prims.int_one)  in
        let uu____106 = f b  in if uu____106 then b else aux Prims.int_zero
         in
      let rec go seen subst1 bs1 bs' t1 =
        match bs1 with
        | [] ->
            let uu____211 = FStar_Syntax_Subst.subst subst1 t1  in
            ((FStar_List.rev bs'), uu____211)
        | b::bs2 ->
            let b1 =
              let uu____255 = FStar_Syntax_Subst.subst_binders subst1 [b]  in
              match uu____255 with
              | b1::[] -> b1
              | uu____293 -> failwith "impossible: unshadow subst_binders"
               in
            let uu____301 = b1  in
            (match uu____301 with
             | (bv0,q) ->
                 let nbs =
                   fresh_until (s bv0)
                     (fun s1  -> Prims.op_Negation (FStar_List.mem s1 seen))
                    in
                 let bv = sset bv0 nbs  in
                 let b2 = (bv, q)  in
                 let uu____342 =
                   let uu____345 =
                     let uu____348 =
                       let uu____349 =
                         let uu____356 = FStar_Syntax_Syntax.bv_to_name bv
                            in
                         (bv0, uu____356)  in
                       FStar_Syntax_Syntax.NT uu____349  in
                     [uu____348]  in
                   FStar_List.append subst1 uu____345  in
                 go (nbs :: seen) uu____342 bs2 (b2 :: bs') t1)
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
            let uu____418 = FStar_Options.print_implicits ()  in
            if uu____418
            then
              let uu____422 = FStar_Tactics_Types.goal_witness g  in
              FStar_Syntax_Print.term_to_string uu____422
            else
              (let uu____425 = FStar_Tactics_Types.check_goal_solved' g  in
               match uu____425 with
               | FStar_Pervasives_Native.None  -> "_"
               | FStar_Pervasives_Native.Some t ->
                   let uu____431 = FStar_Tactics_Types.goal_witness g  in
                   FStar_Syntax_Print.term_to_string uu____431)
             in
          let num =
            match maybe_num with
            | FStar_Pervasives_Native.None  -> ""
            | FStar_Pervasives_Native.Some (i,n1) ->
                let uu____454 = FStar_Util.string_of_int i  in
                let uu____456 = FStar_Util.string_of_int n1  in
                FStar_Util.format2 " %s/%s" uu____454 uu____456
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
          let uu____480 = unshadow goal_binders goal_ty  in
          match uu____480 with
          | (goal_binders1,goal_ty1) ->
              let actual_goal =
                if ps.FStar_Tactics_Types.tac_verb_dbg
                then goal_to_string_verbose g
                else
                  (let uu____494 =
                     FStar_Syntax_Print.binders_to_string ", " goal_binders1
                      in
                   let uu____497 = FStar_Syntax_Print.term_to_string goal_ty1
                      in
                   FStar_Util.format3 "%s |- %s : %s\n" uu____494 w uu____497)
                 in
              FStar_Util.format4 "%s%s%s:\n%s\n" kind num maybe_label
                actual_goal
  
let (ps_to_string :
  (Prims.string * FStar_Tactics_Types.proofstate) -> Prims.string) =
  fun uu____512  ->
    match uu____512 with
    | (msg,ps) ->
        let p_imp imp =
          FStar_Syntax_Print.uvar_to_string
            (imp.FStar_TypeChecker_Common.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_head
           in
        let n_active = FStar_List.length ps.FStar_Tactics_Types.goals  in
        let n_smt = FStar_List.length ps.FStar_Tactics_Types.smt_goals  in
        let n1 = n_active + n_smt  in
        let uu____534 =
          let uu____538 =
            let uu____542 =
              let uu____544 =
                FStar_Util.string_of_int ps.FStar_Tactics_Types.depth  in
              FStar_Util.format2 "State dump @ depth %s (%s):\n" uu____544
                msg
               in
            let uu____547 =
              let uu____551 =
                if
                  ps.FStar_Tactics_Types.entry_range <>
                    FStar_Range.dummyRange
                then
                  let uu____555 =
                    FStar_Range.string_of_def_range
                      ps.FStar_Tactics_Types.entry_range
                     in
                  FStar_Util.format1 "Location: %s\n" uu____555
                else ""  in
              let uu____561 =
                let uu____565 =
                  let uu____567 =
                    FStar_TypeChecker_Env.debug
                      ps.FStar_Tactics_Types.main_context
                      (FStar_Options.Other "Imp")
                     in
                  if uu____567
                  then
                    let uu____572 =
                      FStar_Common.string_of_list p_imp
                        ps.FStar_Tactics_Types.all_implicits
                       in
                    FStar_Util.format1 "Imps: %s\n" uu____572
                  else ""  in
                [uu____565]  in
              uu____551 :: uu____561  in
            uu____542 :: uu____547  in
          let uu____582 =
            let uu____586 =
              FStar_List.mapi
                (fun i  ->
                   fun g  ->
                     goal_to_string "Goal"
                       (FStar_Pervasives_Native.Some
                          ((Prims.int_one + i), n1)) ps g)
                ps.FStar_Tactics_Types.goals
               in
            let uu____606 =
              FStar_List.mapi
                (fun i  ->
                   fun g  ->
                     goal_to_string "SMT Goal"
                       (FStar_Pervasives_Native.Some
                          (((Prims.int_one + n_active) + i), n1)) ps g)
                ps.FStar_Tactics_Types.smt_goals
               in
            FStar_List.append uu____586 uu____606  in
          FStar_List.append uu____538 uu____582  in
        FStar_String.concat "" uu____534
  
let (goal_to_json : FStar_Tactics_Types.goal -> FStar_Util.json) =
  fun g  ->
    let g_binders =
      (g.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_binders
       in
    let g_type = FStar_Tactics_Types.goal_type g  in
    let uu____645 = unshadow g_binders g_type  in
    match uu____645 with
    | (g_binders1,g_type1) ->
        let j_binders =
          let uu____653 =
            let uu____654 = FStar_Tactics_Types.goal_env g  in
            FStar_TypeChecker_Env.dsenv uu____654  in
          FStar_Syntax_Print.binders_to_json uu____653 g_binders1  in
        let uu____655 =
          let uu____663 =
            let uu____671 =
              let uu____677 =
                let uu____678 =
                  let uu____686 =
                    let uu____692 =
                      let uu____693 =
                        let uu____695 = FStar_Tactics_Types.goal_witness g
                           in
                        FStar_Syntax_Print.term_to_string uu____695  in
                      FStar_Util.JsonStr uu____693  in
                    ("witness", uu____692)  in
                  let uu____698 =
                    let uu____706 =
                      let uu____712 =
                        let uu____713 =
                          FStar_Syntax_Print.term_to_string g_type1  in
                        FStar_Util.JsonStr uu____713  in
                      ("type", uu____712)  in
                    [uu____706;
                    ("label",
                      (FStar_Util.JsonStr (g.FStar_Tactics_Types.label)))]
                     in
                  uu____686 :: uu____698  in
                FStar_Util.JsonAssoc uu____678  in
              ("goal", uu____677)  in
            [uu____671]  in
          ("hyps", j_binders) :: uu____663  in
        FStar_Util.JsonAssoc uu____655
  
let (ps_to_json :
  (Prims.string * FStar_Tactics_Types.proofstate) -> FStar_Util.json) =
  fun uu____768  ->
    match uu____768 with
    | (msg,ps) ->
        let uu____778 =
          let uu____786 =
            let uu____794 =
              let uu____802 =
                let uu____810 =
                  let uu____816 =
                    let uu____817 =
                      FStar_List.map goal_to_json
                        ps.FStar_Tactics_Types.goals
                       in
                    FStar_Util.JsonList uu____817  in
                  ("goals", uu____816)  in
                let uu____822 =
                  let uu____830 =
                    let uu____836 =
                      let uu____837 =
                        FStar_List.map goal_to_json
                          ps.FStar_Tactics_Types.smt_goals
                         in
                      FStar_Util.JsonList uu____837  in
                    ("smt-goals", uu____836)  in
                  [uu____830]  in
                uu____810 :: uu____822  in
              ("depth", (FStar_Util.JsonInt (ps.FStar_Tactics_Types.depth)))
                :: uu____802
               in
            ("label", (FStar_Util.JsonStr msg)) :: uu____794  in
          let uu____871 =
            if ps.FStar_Tactics_Types.entry_range <> FStar_Range.dummyRange
            then
              let uu____887 =
                let uu____893 =
                  FStar_Range.json_of_def_range
                    ps.FStar_Tactics_Types.entry_range
                   in
                ("location", uu____893)  in
              [uu____887]
            else []  in
          FStar_List.append uu____786 uu____871  in
        FStar_Util.JsonAssoc uu____778
  
let (do_dump_proofstate :
  FStar_Tactics_Types.proofstate -> Prims.string -> unit) =
  fun ps  ->
    fun msg  ->
      let uu____931 =
        let uu____933 = FStar_Options.silent ()  in
        Prims.op_Negation uu____933  in
      if uu____931
      then
        FStar_Options.with_saved_options
          (fun uu____939  ->
             FStar_Options.set_option "print_effect_args"
               (FStar_Options.Bool true);
             FStar_Util.print_generic "proof-state" ps_to_string ps_to_json
               (msg, ps);
             FStar_Util.flush_stdout ())
      else ()
  