open Prims
type name = FStar_Syntax_Syntax.bv
type env = FStar_TypeChecker_Env.env
type implicits = FStar_TypeChecker_Env.implicits
let (normalize :
  FStar_TypeChecker_Env.steps ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun s  ->
    fun e  ->
      fun t  ->
        FStar_TypeChecker_Normalize.normalize_with_primitive_steps
          FStar_Reflection_Interpreter.reflection_primops s e t
  
let (bnorm :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  = fun e  -> fun t  -> normalize [] e t 
let (tts :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> Prims.string) =
  FStar_TypeChecker_Normalize.term_to_string 
let (bnorm_goal : FStar_Tactics_Types.goal -> FStar_Tactics_Types.goal) =
  fun g  ->
    let uu____44 =
      let uu____45 = FStar_Tactics_Types.goal_env g  in
      let uu____46 = FStar_Tactics_Types.goal_type g  in
      bnorm uu____45 uu____46  in
    FStar_Tactics_Types.goal_with_type g uu____44
  
type 'a tac =
  {
  tac_f: FStar_Tactics_Types.proofstate -> 'a FStar_Tactics_Result.__result }
let __proj__Mktac__item__tac_f :
  'a .
    'a tac ->
      FStar_Tactics_Types.proofstate -> 'a FStar_Tactics_Result.__result
  = fun projectee  -> match projectee with | { tac_f;_} -> tac_f 
let mk_tac :
  'a .
    (FStar_Tactics_Types.proofstate -> 'a FStar_Tactics_Result.__result) ->
      'a tac
  = fun f  -> { tac_f = f } 
let run :
  'a .
    'a tac ->
      FStar_Tactics_Types.proofstate -> 'a FStar_Tactics_Result.__result
  = fun t  -> fun p  -> t.tac_f p 
let run_safe :
  'a .
    'a tac ->
      FStar_Tactics_Types.proofstate -> 'a FStar_Tactics_Result.__result
  =
  fun t  ->
    fun p  ->
      let uu____160 = FStar_Options.tactics_failhard ()  in
      if uu____160
      then run t p
      else
        (try (fun uu___32_170  -> match () with | () -> run t p) ()
         with
         | FStar_Errors.Err (uu____179,msg) ->
             FStar_Tactics_Result.Failed
               ((FStar_Tactics_Types.TacticFailure msg), p)
         | FStar_Errors.Error (uu____183,msg,uu____185) ->
             FStar_Tactics_Result.Failed
               ((FStar_Tactics_Types.TacticFailure msg), p)
         | e -> FStar_Tactics_Result.Failed (e, p))
  
let (log : FStar_Tactics_Types.proofstate -> (unit -> unit) -> unit) =
  fun ps  ->
    fun f  -> if ps.FStar_Tactics_Types.tac_verb_dbg then f () else ()
  
let ret : 'a . 'a -> 'a tac =
  fun x  -> mk_tac (fun p  -> FStar_Tactics_Result.Success (x, p)) 
let bind : 'a 'b . 'a tac -> ('a -> 'b tac) -> 'b tac =
  fun t1  ->
    fun t2  ->
      mk_tac
        (fun p  ->
           let uu____265 = run t1 p  in
           match uu____265 with
           | FStar_Tactics_Result.Success (a,q) ->
               let uu____272 = t2 a  in run uu____272 q
           | FStar_Tactics_Result.Failed (msg,q) ->
               FStar_Tactics_Result.Failed (msg, q))
  
let (get : FStar_Tactics_Types.proofstate tac) =
  mk_tac (fun p  -> FStar_Tactics_Result.Success (p, p)) 
let (idtac : unit tac) = ret () 
let (get_uvar_solved :
  FStar_Syntax_Syntax.ctx_uvar ->
    FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun uv  ->
    let uu____295 =
      FStar_Syntax_Unionfind.find uv.FStar_Syntax_Syntax.ctx_uvar_head  in
    match uu____295 with
    | FStar_Pervasives_Native.Some t -> FStar_Pervasives_Native.Some t
    | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
  
let (check_goal_solved :
  FStar_Tactics_Types.goal ->
    FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  = fun goal  -> get_uvar_solved goal.FStar_Tactics_Types.goal_ctx_uvar 
let (goal_to_string_verbose : FStar_Tactics_Types.goal -> Prims.string) =
  fun g  ->
    let uu____317 =
      FStar_Syntax_Print.ctx_uvar_to_string
        g.FStar_Tactics_Types.goal_ctx_uvar
       in
    let uu____319 =
      let uu____321 = check_goal_solved g  in
      match uu____321 with
      | FStar_Pervasives_Native.None  -> ""
      | FStar_Pervasives_Native.Some t ->
          let uu____327 = FStar_Syntax_Print.term_to_string t  in
          FStar_Util.format1 "\tGOAL ALREADY SOLVED!: %s" uu____327
       in
    FStar_Util.format2 "%s%s\n" uu____317 uu____319
  
let (unshadow :
  FStar_Reflection_Data.binders ->
    FStar_Syntax_Syntax.term ->
      (FStar_Reflection_Data.binders * FStar_Syntax_Syntax.term))
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
            let uu____404 =
              let uu____406 = FStar_Util.string_of_int i  in
              Prims.op_Hat "'" uu____406  in
            Prims.op_Hat b uu____404  in
          let uu____409 = f t1  in
          if uu____409 then t1 else aux (i + Prims.int_one)  in
        let uu____416 = f b  in if uu____416 then b else aux Prims.int_zero
         in
      let rec go seen subst1 bs1 bs' t1 =
        match bs1 with
        | [] ->
            let uu____521 = FStar_Syntax_Subst.subst subst1 t1  in
            ((FStar_List.rev bs'), uu____521)
        | b::bs2 ->
            let b1 =
              let uu____565 = FStar_Syntax_Subst.subst_binders subst1 [b]  in
              match uu____565 with
              | b1::[] -> b1
              | uu____603 -> failwith "impossible: unshadow subst_binders"
               in
            let uu____611 = b1  in
            (match uu____611 with
             | (bv0,q) ->
                 let nbs =
                   fresh_until (s bv0)
                     (fun s1  -> Prims.op_Negation (FStar_List.mem s1 seen))
                    in
                 let bv = sset bv0 nbs  in
                 let b2 = (bv, q)  in
                 let uu____652 =
                   let uu____655 =
                     let uu____658 =
                       let uu____659 =
                         let uu____666 = FStar_Syntax_Syntax.bv_to_name bv
                            in
                         (bv0, uu____666)  in
                       FStar_Syntax_Syntax.NT uu____659  in
                     [uu____658]  in
                   FStar_List.append subst1 uu____655  in
                 go (nbs :: seen) uu____652 bs2 (b2 :: bs') t1)
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
            let uu____728 = FStar_Options.print_implicits ()  in
            if uu____728
            then
              let uu____732 = FStar_Tactics_Types.goal_env g  in
              let uu____733 = FStar_Tactics_Types.goal_witness g  in
              tts uu____732 uu____733
            else
              (let uu____736 =
                 get_uvar_solved g.FStar_Tactics_Types.goal_ctx_uvar  in
               match uu____736 with
               | FStar_Pervasives_Native.None  -> "_"
               | FStar_Pervasives_Native.Some t ->
                   let uu____742 = FStar_Tactics_Types.goal_env g  in
                   let uu____743 = FStar_Tactics_Types.goal_witness g  in
                   tts uu____742 uu____743)
             in
          let num =
            match maybe_num with
            | FStar_Pervasives_Native.None  -> ""
            | FStar_Pervasives_Native.Some (i,n1) ->
                let uu____766 = FStar_Util.string_of_int i  in
                let uu____768 = FStar_Util.string_of_int n1  in
                FStar_Util.format2 " %s/%s" uu____766 uu____768
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
          let uu____792 = unshadow goal_binders goal_ty  in
          match uu____792 with
          | (goal_binders1,goal_ty1) ->
              let actual_goal =
                if ps.FStar_Tactics_Types.tac_verb_dbg
                then goal_to_string_verbose g
                else
                  (let uu____806 =
                     FStar_Syntax_Print.binders_to_string ", " goal_binders1
                      in
                   let uu____809 =
                     let uu____811 = FStar_Tactics_Types.goal_env g  in
                     tts uu____811 goal_ty1  in
                   FStar_Util.format3 "%s |- %s : %s\n" uu____806 w uu____809)
                 in
              FStar_Util.format4 "%s%s%s:\n%s\n" kind num maybe_label
                actual_goal
  
let (tacprint : Prims.string -> unit) =
  fun s  -> FStar_Util.print1 "TAC>> %s\n" s 
let (tacprint1 : Prims.string -> Prims.string -> unit) =
  fun s  ->
    fun x  ->
      let uu____838 = FStar_Util.format1 s x  in
      FStar_Util.print1 "TAC>> %s\n" uu____838
  
let (tacprint2 : Prims.string -> Prims.string -> Prims.string -> unit) =
  fun s  ->
    fun x  ->
      fun y  ->
        let uu____863 = FStar_Util.format2 s x y  in
        FStar_Util.print1 "TAC>> %s\n" uu____863
  
let (tacprint3 :
  Prims.string -> Prims.string -> Prims.string -> Prims.string -> unit) =
  fun s  ->
    fun x  ->
      fun y  ->
        fun z  ->
          let uu____895 = FStar_Util.format3 s x y z  in
          FStar_Util.print1 "TAC>> %s\n" uu____895
  
let (get_phi :
  FStar_Tactics_Types.goal ->
    FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun g  ->
    let uu____908 =
      let uu____909 = FStar_Tactics_Types.goal_env g  in
      let uu____910 = FStar_Tactics_Types.goal_type g  in
      FStar_TypeChecker_Normalize.unfold_whnf uu____909 uu____910  in
    FStar_Syntax_Util.un_squash uu____908
  
let (is_irrelevant : FStar_Tactics_Types.goal -> Prims.bool) =
  fun g  -> let uu____919 = get_phi g  in FStar_Option.isSome uu____919 
let (print : Prims.string -> unit tac) = fun msg  -> tacprint msg; ret () 
let (debugging : unit -> Prims.bool tac) =
  fun uu____943  ->
    bind get
      (fun ps  ->
         let uu____951 =
           FStar_TypeChecker_Env.debug ps.FStar_Tactics_Types.main_context
             (FStar_Options.Other "Tac")
            in
         ret uu____951)
  
let (ps_to_string :
  (Prims.string * FStar_Tactics_Types.proofstate) -> Prims.string) =
  fun uu____966  ->
    match uu____966 with
    | (msg,ps) ->
        let p_imp imp =
          FStar_Syntax_Print.uvar_to_string
            (imp.FStar_TypeChecker_Common.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_head
           in
        let n_active = FStar_List.length ps.FStar_Tactics_Types.goals  in
        let n_smt = FStar_List.length ps.FStar_Tactics_Types.smt_goals  in
        let n1 = n_active + n_smt  in
        let uu____988 =
          let uu____992 =
            let uu____996 =
              let uu____998 =
                FStar_Util.string_of_int ps.FStar_Tactics_Types.depth  in
              FStar_Util.format2 "State dump @ depth %s (%s):\n" uu____998
                msg
               in
            let uu____1001 =
              let uu____1005 =
                if
                  ps.FStar_Tactics_Types.entry_range <>
                    FStar_Range.dummyRange
                then
                  let uu____1009 =
                    FStar_Range.string_of_def_range
                      ps.FStar_Tactics_Types.entry_range
                     in
                  FStar_Util.format1 "Location: %s\n" uu____1009
                else ""  in
              let uu____1015 =
                let uu____1019 =
                  let uu____1021 =
                    FStar_TypeChecker_Env.debug
                      ps.FStar_Tactics_Types.main_context
                      (FStar_Options.Other "Imp")
                     in
                  if uu____1021
                  then
                    let uu____1026 =
                      FStar_Common.string_of_list p_imp
                        ps.FStar_Tactics_Types.all_implicits
                       in
                    FStar_Util.format1 "Imps: %s\n" uu____1026
                  else ""  in
                [uu____1019]  in
              uu____1005 :: uu____1015  in
            uu____996 :: uu____1001  in
          let uu____1036 =
            let uu____1040 =
              FStar_List.mapi
                (fun i  ->
                   fun g  ->
                     goal_to_string "Goal"
                       (FStar_Pervasives_Native.Some
                          ((Prims.int_one + i), n1)) ps g)
                ps.FStar_Tactics_Types.goals
               in
            let uu____1060 =
              FStar_List.mapi
                (fun i  ->
                   fun g  ->
                     goal_to_string "SMT Goal"
                       (FStar_Pervasives_Native.Some
                          (((Prims.int_one + n_active) + i), n1)) ps g)
                ps.FStar_Tactics_Types.smt_goals
               in
            FStar_List.append uu____1040 uu____1060  in
          FStar_List.append uu____992 uu____1036  in
        FStar_String.concat "" uu____988
  
let (goal_to_json : FStar_Tactics_Types.goal -> FStar_Util.json) =
  fun g  ->
    let g_binders =
      (g.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_binders
       in
    let g_type = FStar_Tactics_Types.goal_type g  in
    let uu____1099 = unshadow g_binders g_type  in
    match uu____1099 with
    | (g_binders1,g_type1) ->
        let j_binders =
          let uu____1107 =
            let uu____1108 = FStar_Tactics_Types.goal_env g  in
            FStar_TypeChecker_Env.dsenv uu____1108  in
          FStar_Syntax_Print.binders_to_json uu____1107 g_binders1  in
        let uu____1109 =
          let uu____1117 =
            let uu____1125 =
              let uu____1131 =
                let uu____1132 =
                  let uu____1140 =
                    let uu____1146 =
                      let uu____1147 =
                        let uu____1149 = FStar_Tactics_Types.goal_env g  in
                        let uu____1150 = FStar_Tactics_Types.goal_witness g
                           in
                        tts uu____1149 uu____1150  in
                      FStar_Util.JsonStr uu____1147  in
                    ("witness", uu____1146)  in
                  let uu____1153 =
                    let uu____1161 =
                      let uu____1167 =
                        let uu____1168 =
                          let uu____1170 = FStar_Tactics_Types.goal_env g  in
                          tts uu____1170 g_type1  in
                        FStar_Util.JsonStr uu____1168  in
                      ("type", uu____1167)  in
                    [uu____1161;
                    ("label",
                      (FStar_Util.JsonStr (g.FStar_Tactics_Types.label)))]
                     in
                  uu____1140 :: uu____1153  in
                FStar_Util.JsonAssoc uu____1132  in
              ("goal", uu____1131)  in
            [uu____1125]  in
          ("hyps", j_binders) :: uu____1117  in
        FStar_Util.JsonAssoc uu____1109
  
let (ps_to_json :
  (Prims.string * FStar_Tactics_Types.proofstate) -> FStar_Util.json) =
  fun uu____1224  ->
    match uu____1224 with
    | (msg,ps) ->
        let uu____1234 =
          let uu____1242 =
            let uu____1250 =
              let uu____1258 =
                let uu____1266 =
                  let uu____1272 =
                    let uu____1273 =
                      FStar_List.map goal_to_json
                        ps.FStar_Tactics_Types.goals
                       in
                    FStar_Util.JsonList uu____1273  in
                  ("goals", uu____1272)  in
                let uu____1278 =
                  let uu____1286 =
                    let uu____1292 =
                      let uu____1293 =
                        FStar_List.map goal_to_json
                          ps.FStar_Tactics_Types.smt_goals
                         in
                      FStar_Util.JsonList uu____1293  in
                    ("smt-goals", uu____1292)  in
                  [uu____1286]  in
                uu____1266 :: uu____1278  in
              ("depth", (FStar_Util.JsonInt (ps.FStar_Tactics_Types.depth)))
                :: uu____1258
               in
            ("label", (FStar_Util.JsonStr msg)) :: uu____1250  in
          let uu____1327 =
            if ps.FStar_Tactics_Types.entry_range <> FStar_Range.dummyRange
            then
              let uu____1343 =
                let uu____1349 =
                  FStar_Range.json_of_def_range
                    ps.FStar_Tactics_Types.entry_range
                   in
                ("location", uu____1349)  in
              [uu____1343]
            else []  in
          FStar_List.append uu____1242 uu____1327  in
        FStar_Util.JsonAssoc uu____1234
  
let (do_dump_proofstate :
  FStar_Tactics_Types.proofstate -> Prims.string -> unit) =
  fun ps  ->
    fun msg  ->
      FStar_Options.with_saved_options
        (fun uu____1390  ->
           FStar_Options.set_option "print_effect_args"
             (FStar_Options.Bool true);
           FStar_Util.print_generic "proof-state" ps_to_string ps_to_json
             (msg, ps);
           FStar_Util.flush_stdout ())
  
let (dump : Prims.string -> unit tac) =
  fun msg  ->
    mk_tac
      (fun ps  ->
         let psc = ps.FStar_Tactics_Types.psc  in
         let subst1 = FStar_TypeChecker_Cfg.psc_subst psc  in
         (let uu____1422 = FStar_Tactics_Types.subst_proof_state subst1 ps
             in
          do_dump_proofstate uu____1422 msg);
         FStar_Tactics_Result.Success ((), ps))
  
let mlog : 'a . (unit -> unit) -> (unit -> 'a tac) -> 'a tac =
  fun f  -> fun cont  -> bind get (fun ps  -> log ps f; cont ()) 
let traise : 'a . Prims.exn -> 'a tac =
  fun e  -> mk_tac (fun ps  -> FStar_Tactics_Result.Failed (e, ps)) 
let fail : 'a . Prims.string -> 'a tac =
  fun msg  ->
    mk_tac
      (fun ps  ->
         (let uu____1495 =
            FStar_TypeChecker_Env.debug ps.FStar_Tactics_Types.main_context
              (FStar_Options.Other "TacFail")
             in
          if uu____1495
          then do_dump_proofstate ps (Prims.op_Hat "TACTIC FAILING: " msg)
          else ());
         FStar_Tactics_Result.Failed
           ((FStar_Tactics_Types.TacticFailure msg), ps))
  
let fail1 : 'Auu____1509 . Prims.string -> Prims.string -> 'Auu____1509 tac =
  fun msg  ->
    fun x  -> let uu____1526 = FStar_Util.format1 msg x  in fail uu____1526
  
let fail2 :
  'Auu____1537 .
    Prims.string -> Prims.string -> Prims.string -> 'Auu____1537 tac
  =
  fun msg  ->
    fun x  ->
      fun y  ->
        let uu____1561 = FStar_Util.format2 msg x y  in fail uu____1561
  
let fail3 :
  'Auu____1574 .
    Prims.string ->
      Prims.string -> Prims.string -> Prims.string -> 'Auu____1574 tac
  =
  fun msg  ->
    fun x  ->
      fun y  ->
        fun z  ->
          let uu____1605 = FStar_Util.format3 msg x y z  in fail uu____1605
  
let fail4 :
  'Auu____1620 .
    Prims.string ->
      Prims.string ->
        Prims.string -> Prims.string -> Prims.string -> 'Auu____1620 tac
  =
  fun msg  ->
    fun x  ->
      fun y  ->
        fun z  ->
          fun w  ->
            let uu____1658 = FStar_Util.format4 msg x y z w  in
            fail uu____1658
  
let catch : 'a . 'a tac -> (Prims.exn,'a) FStar_Util.either tac =
  fun t  ->
    mk_tac
      (fun ps  ->
         let tx = FStar_Syntax_Unionfind.new_transaction ()  in
         let uu____1693 = run t ps  in
         match uu____1693 with
         | FStar_Tactics_Result.Success (a,q) ->
             (FStar_Syntax_Unionfind.commit tx;
              FStar_Tactics_Result.Success ((FStar_Util.Inr a), q))
         | FStar_Tactics_Result.Failed (m,q) ->
             (FStar_Syntax_Unionfind.rollback tx;
              (let ps1 =
                 let uu___231_1717 = ps  in
                 {
                   FStar_Tactics_Types.main_context =
                     (uu___231_1717.FStar_Tactics_Types.main_context);
                   FStar_Tactics_Types.all_implicits =
                     (uu___231_1717.FStar_Tactics_Types.all_implicits);
                   FStar_Tactics_Types.goals =
                     (uu___231_1717.FStar_Tactics_Types.goals);
                   FStar_Tactics_Types.smt_goals =
                     (uu___231_1717.FStar_Tactics_Types.smt_goals);
                   FStar_Tactics_Types.depth =
                     (uu___231_1717.FStar_Tactics_Types.depth);
                   FStar_Tactics_Types.__dump =
                     (uu___231_1717.FStar_Tactics_Types.__dump);
                   FStar_Tactics_Types.psc =
                     (uu___231_1717.FStar_Tactics_Types.psc);
                   FStar_Tactics_Types.entry_range =
                     (uu___231_1717.FStar_Tactics_Types.entry_range);
                   FStar_Tactics_Types.guard_policy =
                     (uu___231_1717.FStar_Tactics_Types.guard_policy);
                   FStar_Tactics_Types.freshness =
                     (q.FStar_Tactics_Types.freshness);
                   FStar_Tactics_Types.tac_verb_dbg =
                     (uu___231_1717.FStar_Tactics_Types.tac_verb_dbg);
                   FStar_Tactics_Types.local_state =
                     (uu___231_1717.FStar_Tactics_Types.local_state)
                 }  in
               FStar_Tactics_Result.Success ((FStar_Util.Inl m), ps1))))
  
let recover : 'a . 'a tac -> (Prims.exn,'a) FStar_Util.either tac =
  fun t  ->
    mk_tac
      (fun ps  ->
         let uu____1756 = run t ps  in
         match uu____1756 with
         | FStar_Tactics_Result.Success (a,q) ->
             FStar_Tactics_Result.Success ((FStar_Util.Inr a), q)
         | FStar_Tactics_Result.Failed (m,q) ->
             FStar_Tactics_Result.Success ((FStar_Util.Inl m), q))
  
let trytac : 'a . 'a tac -> 'a FStar_Pervasives_Native.option tac =
  fun t  ->
    let uu____1804 = catch t  in
    bind uu____1804
      (fun r  ->
         match r with
         | FStar_Util.Inr v1 -> ret (FStar_Pervasives_Native.Some v1)
         | FStar_Util.Inl uu____1831 -> ret FStar_Pervasives_Native.None)
  
let trytac_exn : 'a . 'a tac -> 'a FStar_Pervasives_Native.option tac =
  fun t  ->
    mk_tac
      (fun ps  ->
         try
           (fun uu___257_1863  ->
              match () with
              | () -> let uu____1868 = trytac t  in run uu____1868 ps) ()
         with
         | FStar_Errors.Err (uu____1884,msg) ->
             (log ps
                (fun uu____1890  ->
                   FStar_Util.print1 "trytac_exn error: (%s)" msg);
              FStar_Tactics_Result.Success (FStar_Pervasives_Native.None, ps))
         | FStar_Errors.Error (uu____1896,msg,uu____1898) ->
             (log ps
                (fun uu____1903  ->
                   FStar_Util.print1 "trytac_exn error: (%s)" msg);
              FStar_Tactics_Result.Success (FStar_Pervasives_Native.None, ps)))
  
let wrap_err : 'a . Prims.string -> 'a tac -> 'a tac =
  fun pref  ->
    fun t  ->
      mk_tac
        (fun ps  ->
           let uu____1940 = run t ps  in
           match uu____1940 with
           | FStar_Tactics_Result.Success (a,q) ->
               FStar_Tactics_Result.Success (a, q)
           | FStar_Tactics_Result.Failed
               (FStar_Tactics_Types.TacticFailure msg,q) ->
               FStar_Tactics_Result.Failed
                 ((FStar_Tactics_Types.TacticFailure
                     (Prims.op_Hat pref (Prims.op_Hat ": " msg))), q)
           | FStar_Tactics_Result.Failed (e,q) ->
               FStar_Tactics_Result.Failed (e, q))
  
let (set : FStar_Tactics_Types.proofstate -> unit tac) =
  fun p  -> mk_tac (fun uu____1964  -> FStar_Tactics_Result.Success ((), p)) 
let (add_implicits : implicits -> unit tac) =
  fun i  ->
    bind get
      (fun p  ->
         set
           (let uu___292_1979 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___292_1979.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.all_implicits =
                (FStar_List.append i p.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___292_1979.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (uu___292_1979.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___292_1979.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___292_1979.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___292_1979.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___292_1979.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___292_1979.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___292_1979.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___292_1979.FStar_Tactics_Types.tac_verb_dbg);
              FStar_Tactics_Types.local_state =
                (uu___292_1979.FStar_Tactics_Types.local_state)
            }))
  
let (__do_unify :
  env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.bool tac)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        (let uu____2003 =
           FStar_TypeChecker_Env.debug env (FStar_Options.Other "1346")  in
         if uu____2003
         then
           let uu____2007 = FStar_Syntax_Print.term_to_string t1  in
           let uu____2009 = FStar_Syntax_Print.term_to_string t2  in
           FStar_Util.print2 "%%%%%%%%do_unify %s =? %s\n" uu____2007
             uu____2009
         else ());
        (try
           (fun uu___300_2020  ->
              match () with
              | () ->
                  let res = FStar_TypeChecker_Rel.teq_nosmt env t1 t2  in
                  ((let uu____2028 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "1346")
                       in
                    if uu____2028
                    then
                      let uu____2032 =
                        FStar_Common.string_of_option
                          (FStar_TypeChecker_Rel.guard_to_string env) res
                         in
                      let uu____2034 = FStar_Syntax_Print.term_to_string t1
                         in
                      let uu____2036 = FStar_Syntax_Print.term_to_string t2
                         in
                      FStar_Util.print3
                        "%%%%%%%%do_unify (RESULT %s) %s =? %s\n" uu____2032
                        uu____2034 uu____2036
                    else ());
                   (match res with
                    | FStar_Pervasives_Native.None  -> ret false
                    | FStar_Pervasives_Native.Some g ->
                        let uu____2047 =
                          add_implicits g.FStar_TypeChecker_Common.implicits
                           in
                        bind uu____2047 (fun uu____2052  -> ret true)))) ()
         with
         | FStar_Errors.Err (uu____2062,msg) ->
             mlog
               (fun uu____2068  ->
                  FStar_Util.print1 ">> do_unify error, (%s)\n" msg)
               (fun uu____2071  -> ret false)
         | FStar_Errors.Error (uu____2074,msg,r) ->
             mlog
               (fun uu____2082  ->
                  let uu____2083 = FStar_Range.string_of_range r  in
                  FStar_Util.print2 ">> do_unify error, (%s) at (%s)\n" msg
                    uu____2083) (fun uu____2087  -> ret false))
  
let (compress_implicits : unit tac) =
  bind get
    (fun ps  ->
       let imps = ps.FStar_Tactics_Types.all_implicits  in
       let g =
         let uu___326_2101 = FStar_TypeChecker_Env.trivial_guard  in
         {
           FStar_TypeChecker_Common.guard_f =
             (uu___326_2101.FStar_TypeChecker_Common.guard_f);
           FStar_TypeChecker_Common.deferred =
             (uu___326_2101.FStar_TypeChecker_Common.deferred);
           FStar_TypeChecker_Common.univ_ineqs =
             (uu___326_2101.FStar_TypeChecker_Common.univ_ineqs);
           FStar_TypeChecker_Common.implicits = imps
         }  in
       let g1 =
         FStar_TypeChecker_Rel.resolve_implicits_tac
           ps.FStar_Tactics_Types.main_context g
          in
       let ps' =
         let uu___330_2104 = ps  in
         {
           FStar_Tactics_Types.main_context =
             (uu___330_2104.FStar_Tactics_Types.main_context);
           FStar_Tactics_Types.all_implicits =
             (g1.FStar_TypeChecker_Common.implicits);
           FStar_Tactics_Types.goals =
             (uu___330_2104.FStar_Tactics_Types.goals);
           FStar_Tactics_Types.smt_goals =
             (uu___330_2104.FStar_Tactics_Types.smt_goals);
           FStar_Tactics_Types.depth =
             (uu___330_2104.FStar_Tactics_Types.depth);
           FStar_Tactics_Types.__dump =
             (uu___330_2104.FStar_Tactics_Types.__dump);
           FStar_Tactics_Types.psc = (uu___330_2104.FStar_Tactics_Types.psc);
           FStar_Tactics_Types.entry_range =
             (uu___330_2104.FStar_Tactics_Types.entry_range);
           FStar_Tactics_Types.guard_policy =
             (uu___330_2104.FStar_Tactics_Types.guard_policy);
           FStar_Tactics_Types.freshness =
             (uu___330_2104.FStar_Tactics_Types.freshness);
           FStar_Tactics_Types.tac_verb_dbg =
             (uu___330_2104.FStar_Tactics_Types.tac_verb_dbg);
           FStar_Tactics_Types.local_state =
             (uu___330_2104.FStar_Tactics_Types.local_state)
         }  in
       set ps')
  
let (do_unify :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.bool tac)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        bind idtac
          (fun uu____2131  ->
             (let uu____2133 =
                FStar_TypeChecker_Env.debug env (FStar_Options.Other "1346")
                 in
              if uu____2133
              then
                (FStar_Options.push ();
                 (let uu____2138 =
                    FStar_Options.set_options
                      "--debug_level Rel --debug_level RelCheck"
                     in
                  ()))
              else ());
             (let uu____2142 = __do_unify env t1 t2  in
              bind uu____2142
                (fun r  ->
                   (let uu____2153 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "1346")
                       in
                    if uu____2153 then FStar_Options.pop () else ());
                   ret r)))
  
let (do_match :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.bool tac)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uvs1 = FStar_Syntax_Free.uvars_uncached t1  in
        let uu____2185 = do_unify env t1 t2  in
        bind uu____2185
          (fun r  ->
             if r
             then
               let uvs2 = FStar_Syntax_Free.uvars_uncached t1  in
               let uu____2203 =
                 let uu____2205 = FStar_Util.set_eq uvs1 uvs2  in
                 Prims.op_Negation uu____2205  in
               (if uu____2203 then ret false else ret true)
             else ret false)
  
let (remove_solved_goals : unit tac) =
  bind get
    (fun ps  ->
       let ps' =
         let uu___353_2228 = ps  in
         let uu____2229 =
           FStar_List.filter
             (fun g  ->
                let uu____2235 = check_goal_solved g  in
                FStar_Option.isNone uu____2235) ps.FStar_Tactics_Types.goals
            in
         {
           FStar_Tactics_Types.main_context =
             (uu___353_2228.FStar_Tactics_Types.main_context);
           FStar_Tactics_Types.all_implicits =
             (uu___353_2228.FStar_Tactics_Types.all_implicits);
           FStar_Tactics_Types.goals = uu____2229;
           FStar_Tactics_Types.smt_goals =
             (uu___353_2228.FStar_Tactics_Types.smt_goals);
           FStar_Tactics_Types.depth =
             (uu___353_2228.FStar_Tactics_Types.depth);
           FStar_Tactics_Types.__dump =
             (uu___353_2228.FStar_Tactics_Types.__dump);
           FStar_Tactics_Types.psc = (uu___353_2228.FStar_Tactics_Types.psc);
           FStar_Tactics_Types.entry_range =
             (uu___353_2228.FStar_Tactics_Types.entry_range);
           FStar_Tactics_Types.guard_policy =
             (uu___353_2228.FStar_Tactics_Types.guard_policy);
           FStar_Tactics_Types.freshness =
             (uu___353_2228.FStar_Tactics_Types.freshness);
           FStar_Tactics_Types.tac_verb_dbg =
             (uu___353_2228.FStar_Tactics_Types.tac_verb_dbg);
           FStar_Tactics_Types.local_state =
             (uu___353_2228.FStar_Tactics_Types.local_state)
         }  in
       set ps')
  
let (set_solution :
  FStar_Tactics_Types.goal -> FStar_Syntax_Syntax.term -> unit tac) =
  fun goal  ->
    fun solution  ->
      let uu____2253 =
        FStar_Syntax_Unionfind.find
          (goal.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_head
         in
      match uu____2253 with
      | FStar_Pervasives_Native.Some uu____2258 ->
          let uu____2259 =
            let uu____2261 = goal_to_string_verbose goal  in
            FStar_Util.format1 "Goal %s is already solved" uu____2261  in
          fail uu____2259
      | FStar_Pervasives_Native.None  ->
          (FStar_Syntax_Unionfind.change
             (goal.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_head
             solution;
           ret ())
  
let (trysolve :
  FStar_Tactics_Types.goal -> FStar_Syntax_Syntax.term -> Prims.bool tac) =
  fun goal  ->
    fun solution  ->
      let uu____2282 = FStar_Tactics_Types.goal_env goal  in
      let uu____2283 = FStar_Tactics_Types.goal_witness goal  in
      do_unify uu____2282 solution uu____2283
  
let (__dismiss : unit tac) =
  bind get
    (fun p  ->
       let uu____2290 =
         let uu___366_2291 = p  in
         let uu____2292 = FStar_List.tl p.FStar_Tactics_Types.goals  in
         {
           FStar_Tactics_Types.main_context =
             (uu___366_2291.FStar_Tactics_Types.main_context);
           FStar_Tactics_Types.all_implicits =
             (uu___366_2291.FStar_Tactics_Types.all_implicits);
           FStar_Tactics_Types.goals = uu____2292;
           FStar_Tactics_Types.smt_goals =
             (uu___366_2291.FStar_Tactics_Types.smt_goals);
           FStar_Tactics_Types.depth =
             (uu___366_2291.FStar_Tactics_Types.depth);
           FStar_Tactics_Types.__dump =
             (uu___366_2291.FStar_Tactics_Types.__dump);
           FStar_Tactics_Types.psc = (uu___366_2291.FStar_Tactics_Types.psc);
           FStar_Tactics_Types.entry_range =
             (uu___366_2291.FStar_Tactics_Types.entry_range);
           FStar_Tactics_Types.guard_policy =
             (uu___366_2291.FStar_Tactics_Types.guard_policy);
           FStar_Tactics_Types.freshness =
             (uu___366_2291.FStar_Tactics_Types.freshness);
           FStar_Tactics_Types.tac_verb_dbg =
             (uu___366_2291.FStar_Tactics_Types.tac_verb_dbg);
           FStar_Tactics_Types.local_state =
             (uu___366_2291.FStar_Tactics_Types.local_state)
         }  in
       set uu____2290)
  
let (solve :
  FStar_Tactics_Types.goal -> FStar_Syntax_Syntax.term -> unit tac) =
  fun goal  ->
    fun solution  ->
      let e = FStar_Tactics_Types.goal_env goal  in
      mlog
        (fun uu____2314  ->
           let uu____2315 =
             let uu____2317 = FStar_Tactics_Types.goal_witness goal  in
             FStar_Syntax_Print.term_to_string uu____2317  in
           let uu____2318 = FStar_Syntax_Print.term_to_string solution  in
           FStar_Util.print2 "solve %s := %s\n" uu____2315 uu____2318)
        (fun uu____2323  ->
           let uu____2324 = trysolve goal solution  in
           bind uu____2324
             (fun b  ->
                if b
                then bind __dismiss (fun uu____2336  -> remove_solved_goals)
                else
                  (let uu____2339 =
                     let uu____2341 =
                       let uu____2343 = FStar_Tactics_Types.goal_env goal  in
                       tts uu____2343 solution  in
                     let uu____2344 =
                       let uu____2346 = FStar_Tactics_Types.goal_env goal  in
                       let uu____2347 = FStar_Tactics_Types.goal_witness goal
                          in
                       tts uu____2346 uu____2347  in
                     let uu____2348 =
                       let uu____2350 = FStar_Tactics_Types.goal_env goal  in
                       let uu____2351 = FStar_Tactics_Types.goal_type goal
                          in
                       tts uu____2350 uu____2351  in
                     FStar_Util.format3 "%s does not solve %s : %s"
                       uu____2341 uu____2344 uu____2348
                      in
                   fail uu____2339)))
  
let (solve' :
  FStar_Tactics_Types.goal -> FStar_Syntax_Syntax.term -> unit tac) =
  fun goal  ->
    fun solution  ->
      let uu____2368 = set_solution goal solution  in
      bind uu____2368
        (fun uu____2372  ->
           bind __dismiss (fun uu____2374  -> remove_solved_goals))
  
let (set_goals : FStar_Tactics_Types.goal Prims.list -> unit tac) =
  fun gs  ->
    bind get
      (fun ps  ->
         set
           (let uu___382_2393 = ps  in
            {
              FStar_Tactics_Types.main_context =
                (uu___382_2393.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.all_implicits =
                (uu___382_2393.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals = gs;
              FStar_Tactics_Types.smt_goals =
                (uu___382_2393.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___382_2393.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___382_2393.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___382_2393.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___382_2393.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___382_2393.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___382_2393.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___382_2393.FStar_Tactics_Types.tac_verb_dbg);
              FStar_Tactics_Types.local_state =
                (uu___382_2393.FStar_Tactics_Types.local_state)
            }))
  
let (set_smt_goals : FStar_Tactics_Types.goal Prims.list -> unit tac) =
  fun gs  ->
    bind get
      (fun ps  ->
         set
           (let uu___386_2412 = ps  in
            {
              FStar_Tactics_Types.main_context =
                (uu___386_2412.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.all_implicits =
                (uu___386_2412.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___386_2412.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals = gs;
              FStar_Tactics_Types.depth =
                (uu___386_2412.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___386_2412.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___386_2412.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___386_2412.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___386_2412.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___386_2412.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___386_2412.FStar_Tactics_Types.tac_verb_dbg);
              FStar_Tactics_Types.local_state =
                (uu___386_2412.FStar_Tactics_Types.local_state)
            }))
  
let (dismiss_all : unit tac) = set_goals [] 
let (nwarn : Prims.int FStar_ST.ref) = FStar_Util.mk_ref Prims.int_zero 
let (check_valid_goal : FStar_Tactics_Types.goal -> unit) =
  fun g  ->
    let uu____2428 = FStar_Options.defensive ()  in
    if uu____2428
    then
      let b = true  in
      let env = FStar_Tactics_Types.goal_env g  in
      let b1 =
        b &&
          (let uu____2438 = FStar_Tactics_Types.goal_witness g  in
           FStar_TypeChecker_Env.closed env uu____2438)
         in
      let b2 =
        b1 &&
          (let uu____2442 = FStar_Tactics_Types.goal_type g  in
           FStar_TypeChecker_Env.closed env uu____2442)
         in
      let rec aux b3 e =
        let uu____2457 = FStar_TypeChecker_Env.pop_bv e  in
        match uu____2457 with
        | FStar_Pervasives_Native.None  -> b3
        | FStar_Pervasives_Native.Some (bv,e1) ->
            let b4 =
              b3 &&
                (FStar_TypeChecker_Env.closed e1 bv.FStar_Syntax_Syntax.sort)
               in
            aux b4 e1
         in
      let uu____2477 =
        (let uu____2481 = aux b2 env  in Prims.op_Negation uu____2481) &&
          (let uu____2484 = FStar_ST.op_Bang nwarn  in
           uu____2484 < (Prims.of_int (5)))
         in
      (if uu____2477
       then
         ((let uu____2510 =
             let uu____2511 = FStar_Tactics_Types.goal_type g  in
             uu____2511.FStar_Syntax_Syntax.pos  in
           let uu____2514 =
             let uu____2520 =
               let uu____2522 = goal_to_string_verbose g  in
               FStar_Util.format1
                 "The following goal is ill-formed. Keeping calm and carrying on...\n<%s>\n\n"
                 uu____2522
                in
             (FStar_Errors.Warning_IllFormedGoal, uu____2520)  in
           FStar_Errors.log_issue uu____2510 uu____2514);
          (let uu____2526 =
             let uu____2528 = FStar_ST.op_Bang nwarn  in
             uu____2528 + Prims.int_one  in
           FStar_ST.op_Colon_Equals nwarn uu____2526))
       else ())
    else ()
  
let (add_goals : FStar_Tactics_Types.goal Prims.list -> unit tac) =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___408_2597 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___408_2597.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.all_implicits =
                (uu___408_2597.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (FStar_List.append gs p.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (uu___408_2597.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___408_2597.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___408_2597.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___408_2597.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___408_2597.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___408_2597.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___408_2597.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___408_2597.FStar_Tactics_Types.tac_verb_dbg);
              FStar_Tactics_Types.local_state =
                (uu___408_2597.FStar_Tactics_Types.local_state)
            }))
  
let (add_smt_goals : FStar_Tactics_Types.goal Prims.list -> unit tac) =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___413_2618 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___413_2618.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.all_implicits =
                (uu___413_2618.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___413_2618.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (FStar_List.append gs p.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___413_2618.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___413_2618.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___413_2618.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___413_2618.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___413_2618.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___413_2618.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___413_2618.FStar_Tactics_Types.tac_verb_dbg);
              FStar_Tactics_Types.local_state =
                (uu___413_2618.FStar_Tactics_Types.local_state)
            }))
  
let (push_goals : FStar_Tactics_Types.goal Prims.list -> unit tac) =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___418_2639 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___418_2639.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.all_implicits =
                (uu___418_2639.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (FStar_List.append p.FStar_Tactics_Types.goals gs);
              FStar_Tactics_Types.smt_goals =
                (uu___418_2639.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___418_2639.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___418_2639.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___418_2639.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___418_2639.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___418_2639.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___418_2639.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___418_2639.FStar_Tactics_Types.tac_verb_dbg);
              FStar_Tactics_Types.local_state =
                (uu___418_2639.FStar_Tactics_Types.local_state)
            }))
  
let (push_smt_goals : FStar_Tactics_Types.goal Prims.list -> unit tac) =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___423_2660 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___423_2660.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.all_implicits =
                (uu___423_2660.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___423_2660.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (FStar_List.append p.FStar_Tactics_Types.smt_goals gs);
              FStar_Tactics_Types.depth =
                (uu___423_2660.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___423_2660.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___423_2660.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___423_2660.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___423_2660.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___423_2660.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___423_2660.FStar_Tactics_Types.tac_verb_dbg);
              FStar_Tactics_Types.local_state =
                (uu___423_2660.FStar_Tactics_Types.local_state)
            }))
  
let (replace_cur : FStar_Tactics_Types.goal -> unit tac) =
  fun g  -> bind __dismiss (fun uu____2672  -> add_goals [g]) 
let (new_uvar :
  Prims.string ->
    env ->
      FStar_Reflection_Data.typ ->
        (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.ctx_uvar) tac)
  =
  fun reason  ->
    fun env  ->
      fun typ  ->
        let uu____2703 =
          FStar_TypeChecker_Env.new_implicit_var_aux reason
            typ.FStar_Syntax_Syntax.pos env typ
            FStar_Syntax_Syntax.Allow_untyped FStar_Pervasives_Native.None
           in
        match uu____2703 with
        | (u,ctx_uvar,g_u) ->
            let uu____2741 =
              add_implicits g_u.FStar_TypeChecker_Common.implicits  in
            bind uu____2741
              (fun uu____2750  ->
                 let uu____2751 =
                   let uu____2756 =
                     let uu____2757 = FStar_List.hd ctx_uvar  in
                     FStar_Pervasives_Native.fst uu____2757  in
                   (u, uu____2756)  in
                 ret uu____2751)
  
let (is_true : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____2778 = FStar_Syntax_Util.un_squash t1  in
    match uu____2778 with
    | FStar_Pervasives_Native.Some t' ->
        let t'1 = FStar_Syntax_Util.unascribe t'  in
        let uu____2790 =
          let uu____2791 = FStar_Syntax_Subst.compress t'1  in
          uu____2791.FStar_Syntax_Syntax.n  in
        (match uu____2790 with
         | FStar_Syntax_Syntax.Tm_fvar fv ->
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.true_lid
         | uu____2796 -> false)
    | uu____2798 -> false
  
let (is_false : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____2811 = FStar_Syntax_Util.un_squash t  in
    match uu____2811 with
    | FStar_Pervasives_Native.Some t' ->
        let uu____2822 =
          let uu____2823 = FStar_Syntax_Subst.compress t'  in
          uu____2823.FStar_Syntax_Syntax.n  in
        (match uu____2822 with
         | FStar_Syntax_Syntax.Tm_fvar fv ->
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.false_lid
         | uu____2828 -> false)
    | uu____2830 -> false
  
let (cur_goal : unit -> FStar_Tactics_Types.goal tac) =
  fun uu____2843  ->
    bind get
      (fun p  ->
         match p.FStar_Tactics_Types.goals with
         | [] -> fail "No more goals (1)"
         | hd1::tl1 ->
             let uu____2855 =
               FStar_Syntax_Unionfind.find
                 (hd1.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_head
                in
             (match uu____2855 with
              | FStar_Pervasives_Native.None  -> ret hd1
              | FStar_Pervasives_Native.Some t ->
                  ((let uu____2862 = goal_to_string_verbose hd1  in
                    let uu____2864 = FStar_Syntax_Print.term_to_string t  in
                    FStar_Util.print2
                      "!!!!!!!!!!!! GOAL IS ALREADY SOLVED! %s\nsol is %s\n"
                      uu____2862 uu____2864);
                   ret hd1)))
  
let (tadmit_t : FStar_Syntax_Syntax.term -> unit tac) =
  fun t  ->
    let uu____2877 =
      bind get
        (fun ps  ->
           let uu____2883 = cur_goal ()  in
           bind uu____2883
             (fun g  ->
                (let uu____2890 =
                   let uu____2891 = FStar_Tactics_Types.goal_type g  in
                   uu____2891.FStar_Syntax_Syntax.pos  in
                 let uu____2894 =
                   let uu____2900 =
                     let uu____2902 =
                       goal_to_string "" FStar_Pervasives_Native.None ps g
                        in
                     FStar_Util.format1 "Tactics admitted goal <%s>\n\n"
                       uu____2902
                      in
                   (FStar_Errors.Warning_TacAdmit, uu____2900)  in
                 FStar_Errors.log_issue uu____2890 uu____2894);
                solve' g t))
       in
    FStar_All.pipe_left (wrap_err "tadmit_t") uu____2877
  
let (fresh : unit -> FStar_BigInt.t tac) =
  fun uu____2925  ->
    bind get
      (fun ps  ->
         let n1 = ps.FStar_Tactics_Types.freshness  in
         let ps1 =
           let uu___468_2936 = ps  in
           {
             FStar_Tactics_Types.main_context =
               (uu___468_2936.FStar_Tactics_Types.main_context);
             FStar_Tactics_Types.all_implicits =
               (uu___468_2936.FStar_Tactics_Types.all_implicits);
             FStar_Tactics_Types.goals =
               (uu___468_2936.FStar_Tactics_Types.goals);
             FStar_Tactics_Types.smt_goals =
               (uu___468_2936.FStar_Tactics_Types.smt_goals);
             FStar_Tactics_Types.depth =
               (uu___468_2936.FStar_Tactics_Types.depth);
             FStar_Tactics_Types.__dump =
               (uu___468_2936.FStar_Tactics_Types.__dump);
             FStar_Tactics_Types.psc =
               (uu___468_2936.FStar_Tactics_Types.psc);
             FStar_Tactics_Types.entry_range =
               (uu___468_2936.FStar_Tactics_Types.entry_range);
             FStar_Tactics_Types.guard_policy =
               (uu___468_2936.FStar_Tactics_Types.guard_policy);
             FStar_Tactics_Types.freshness = (n1 + Prims.int_one);
             FStar_Tactics_Types.tac_verb_dbg =
               (uu___468_2936.FStar_Tactics_Types.tac_verb_dbg);
             FStar_Tactics_Types.local_state =
               (uu___468_2936.FStar_Tactics_Types.local_state)
           }  in
         let uu____2938 = set ps1  in
         bind uu____2938
           (fun uu____2943  ->
              let uu____2944 = FStar_BigInt.of_int_fs n1  in ret uu____2944))
  
let (curms : unit -> FStar_BigInt.t tac) =
  fun uu____2952  ->
    let uu____2955 =
      let uu____2956 = FStar_Util.now_ms ()  in
      FStar_All.pipe_right uu____2956 FStar_BigInt.of_int_fs  in
    ret uu____2955
  
let (mk_irrelevant_goal :
  Prims.string ->
    env ->
      FStar_Reflection_Data.typ ->
        FStar_Options.optionstate ->
          Prims.string -> FStar_Tactics_Types.goal tac)
  =
  fun reason  ->
    fun env  ->
      fun phi  ->
        fun opts  ->
          fun label1  ->
            let typ =
              let uu____2996 = env.FStar_TypeChecker_Env.universe_of env phi
                 in
              FStar_Syntax_Util.mk_squash uu____2996 phi  in
            let uu____2997 = new_uvar reason env typ  in
            bind uu____2997
              (fun uu____3012  ->
                 match uu____3012 with
                 | (uu____3019,ctx_uvar) ->
                     let goal =
                       FStar_Tactics_Types.mk_goal env ctx_uvar opts false
                         label1
                        in
                     ret goal)
  
let (__tc :
  env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term * FStar_Reflection_Data.typ *
        FStar_TypeChecker_Common.guard_t) tac)
  =
  fun e  ->
    fun t  ->
      bind get
        (fun ps  ->
           mlog
             (fun uu____3066  ->
                let uu____3067 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.print1 "Tac> __tc(%s)\n" uu____3067)
             (fun uu____3072  ->
                let e1 =
                  let uu___487_3074 = e  in
                  {
                    FStar_TypeChecker_Env.solver =
                      (uu___487_3074.FStar_TypeChecker_Env.solver);
                    FStar_TypeChecker_Env.range =
                      (uu___487_3074.FStar_TypeChecker_Env.range);
                    FStar_TypeChecker_Env.curmodule =
                      (uu___487_3074.FStar_TypeChecker_Env.curmodule);
                    FStar_TypeChecker_Env.gamma =
                      (uu___487_3074.FStar_TypeChecker_Env.gamma);
                    FStar_TypeChecker_Env.gamma_sig =
                      (uu___487_3074.FStar_TypeChecker_Env.gamma_sig);
                    FStar_TypeChecker_Env.gamma_cache =
                      (uu___487_3074.FStar_TypeChecker_Env.gamma_cache);
                    FStar_TypeChecker_Env.modules =
                      (uu___487_3074.FStar_TypeChecker_Env.modules);
                    FStar_TypeChecker_Env.expected_typ =
                      (uu___487_3074.FStar_TypeChecker_Env.expected_typ);
                    FStar_TypeChecker_Env.sigtab =
                      (uu___487_3074.FStar_TypeChecker_Env.sigtab);
                    FStar_TypeChecker_Env.attrtab =
                      (uu___487_3074.FStar_TypeChecker_Env.attrtab);
                    FStar_TypeChecker_Env.instantiate_imp =
                      (uu___487_3074.FStar_TypeChecker_Env.instantiate_imp);
                    FStar_TypeChecker_Env.effects =
                      (uu___487_3074.FStar_TypeChecker_Env.effects);
                    FStar_TypeChecker_Env.generalize =
                      (uu___487_3074.FStar_TypeChecker_Env.generalize);
                    FStar_TypeChecker_Env.letrecs =
                      (uu___487_3074.FStar_TypeChecker_Env.letrecs);
                    FStar_TypeChecker_Env.top_level =
                      (uu___487_3074.FStar_TypeChecker_Env.top_level);
                    FStar_TypeChecker_Env.check_uvars =
                      (uu___487_3074.FStar_TypeChecker_Env.check_uvars);
                    FStar_TypeChecker_Env.use_eq =
                      (uu___487_3074.FStar_TypeChecker_Env.use_eq);
                    FStar_TypeChecker_Env.use_eq_strict =
                      (uu___487_3074.FStar_TypeChecker_Env.use_eq_strict);
                    FStar_TypeChecker_Env.is_iface =
                      (uu___487_3074.FStar_TypeChecker_Env.is_iface);
                    FStar_TypeChecker_Env.admit =
                      (uu___487_3074.FStar_TypeChecker_Env.admit);
                    FStar_TypeChecker_Env.lax =
                      (uu___487_3074.FStar_TypeChecker_Env.lax);
                    FStar_TypeChecker_Env.lax_universes =
                      (uu___487_3074.FStar_TypeChecker_Env.lax_universes);
                    FStar_TypeChecker_Env.phase1 =
                      (uu___487_3074.FStar_TypeChecker_Env.phase1);
                    FStar_TypeChecker_Env.failhard =
                      (uu___487_3074.FStar_TypeChecker_Env.failhard);
                    FStar_TypeChecker_Env.nosynth =
                      (uu___487_3074.FStar_TypeChecker_Env.nosynth);
                    FStar_TypeChecker_Env.uvar_subtyping = false;
                    FStar_TypeChecker_Env.tc_term =
                      (uu___487_3074.FStar_TypeChecker_Env.tc_term);
                    FStar_TypeChecker_Env.type_of =
                      (uu___487_3074.FStar_TypeChecker_Env.type_of);
                    FStar_TypeChecker_Env.universe_of =
                      (uu___487_3074.FStar_TypeChecker_Env.universe_of);
                    FStar_TypeChecker_Env.check_type_of =
                      (uu___487_3074.FStar_TypeChecker_Env.check_type_of);
                    FStar_TypeChecker_Env.use_bv_sorts =
                      (uu___487_3074.FStar_TypeChecker_Env.use_bv_sorts);
                    FStar_TypeChecker_Env.qtbl_name_and_index =
                      (uu___487_3074.FStar_TypeChecker_Env.qtbl_name_and_index);
                    FStar_TypeChecker_Env.normalized_eff_names =
                      (uu___487_3074.FStar_TypeChecker_Env.normalized_eff_names);
                    FStar_TypeChecker_Env.fv_delta_depths =
                      (uu___487_3074.FStar_TypeChecker_Env.fv_delta_depths);
                    FStar_TypeChecker_Env.proof_ns =
                      (uu___487_3074.FStar_TypeChecker_Env.proof_ns);
                    FStar_TypeChecker_Env.synth_hook =
                      (uu___487_3074.FStar_TypeChecker_Env.synth_hook);
                    FStar_TypeChecker_Env.try_solve_implicits_hook =
                      (uu___487_3074.FStar_TypeChecker_Env.try_solve_implicits_hook);
                    FStar_TypeChecker_Env.splice =
                      (uu___487_3074.FStar_TypeChecker_Env.splice);
                    FStar_TypeChecker_Env.mpreprocess =
                      (uu___487_3074.FStar_TypeChecker_Env.mpreprocess);
                    FStar_TypeChecker_Env.postprocess =
                      (uu___487_3074.FStar_TypeChecker_Env.postprocess);
                    FStar_TypeChecker_Env.is_native_tactic =
                      (uu___487_3074.FStar_TypeChecker_Env.is_native_tactic);
                    FStar_TypeChecker_Env.identifier_info =
                      (uu___487_3074.FStar_TypeChecker_Env.identifier_info);
                    FStar_TypeChecker_Env.tc_hooks =
                      (uu___487_3074.FStar_TypeChecker_Env.tc_hooks);
                    FStar_TypeChecker_Env.dsenv =
                      (uu___487_3074.FStar_TypeChecker_Env.dsenv);
                    FStar_TypeChecker_Env.nbe =
                      (uu___487_3074.FStar_TypeChecker_Env.nbe);
                    FStar_TypeChecker_Env.strict_args_tab =
                      (uu___487_3074.FStar_TypeChecker_Env.strict_args_tab);
                    FStar_TypeChecker_Env.erasable_types_tab =
                      (uu___487_3074.FStar_TypeChecker_Env.erasable_types_tab)
                  }  in
                try
                  (fun uu___491_3086  ->
                     match () with
                     | () ->
                         let uu____3095 =
                           FStar_TypeChecker_TcTerm.type_of_tot_term e1 t  in
                         ret uu____3095) ()
                with
                | FStar_Errors.Err (uu____3122,msg) ->
                    let uu____3126 = tts e1 t  in
                    let uu____3128 =
                      let uu____3130 = FStar_TypeChecker_Env.all_binders e1
                         in
                      FStar_All.pipe_right uu____3130
                        (FStar_Syntax_Print.binders_to_string ", ")
                       in
                    fail3 "Cannot type %s in context (%s). Error = (%s)"
                      uu____3126 uu____3128 msg
                | FStar_Errors.Error (uu____3140,msg,uu____3142) ->
                    let uu____3145 = tts e1 t  in
                    let uu____3147 =
                      let uu____3149 = FStar_TypeChecker_Env.all_binders e1
                         in
                      FStar_All.pipe_right uu____3149
                        (FStar_Syntax_Print.binders_to_string ", ")
                       in
                    fail3 "Cannot type %s in context (%s). Error = (%s)"
                      uu____3145 uu____3147 msg))
  
let (__tc_ghost :
  env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term * FStar_Reflection_Data.typ *
        FStar_TypeChecker_Common.guard_t) tac)
  =
  fun e  ->
    fun t  ->
      bind get
        (fun ps  ->
           mlog
             (fun uu____3202  ->
                let uu____3203 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.print1 "Tac> __tc_ghost(%s)\n" uu____3203)
             (fun uu____3208  ->
                let e1 =
                  let uu___508_3210 = e  in
                  {
                    FStar_TypeChecker_Env.solver =
                      (uu___508_3210.FStar_TypeChecker_Env.solver);
                    FStar_TypeChecker_Env.range =
                      (uu___508_3210.FStar_TypeChecker_Env.range);
                    FStar_TypeChecker_Env.curmodule =
                      (uu___508_3210.FStar_TypeChecker_Env.curmodule);
                    FStar_TypeChecker_Env.gamma =
                      (uu___508_3210.FStar_TypeChecker_Env.gamma);
                    FStar_TypeChecker_Env.gamma_sig =
                      (uu___508_3210.FStar_TypeChecker_Env.gamma_sig);
                    FStar_TypeChecker_Env.gamma_cache =
                      (uu___508_3210.FStar_TypeChecker_Env.gamma_cache);
                    FStar_TypeChecker_Env.modules =
                      (uu___508_3210.FStar_TypeChecker_Env.modules);
                    FStar_TypeChecker_Env.expected_typ =
                      (uu___508_3210.FStar_TypeChecker_Env.expected_typ);
                    FStar_TypeChecker_Env.sigtab =
                      (uu___508_3210.FStar_TypeChecker_Env.sigtab);
                    FStar_TypeChecker_Env.attrtab =
                      (uu___508_3210.FStar_TypeChecker_Env.attrtab);
                    FStar_TypeChecker_Env.instantiate_imp =
                      (uu___508_3210.FStar_TypeChecker_Env.instantiate_imp);
                    FStar_TypeChecker_Env.effects =
                      (uu___508_3210.FStar_TypeChecker_Env.effects);
                    FStar_TypeChecker_Env.generalize =
                      (uu___508_3210.FStar_TypeChecker_Env.generalize);
                    FStar_TypeChecker_Env.letrecs =
                      (uu___508_3210.FStar_TypeChecker_Env.letrecs);
                    FStar_TypeChecker_Env.top_level =
                      (uu___508_3210.FStar_TypeChecker_Env.top_level);
                    FStar_TypeChecker_Env.check_uvars =
                      (uu___508_3210.FStar_TypeChecker_Env.check_uvars);
                    FStar_TypeChecker_Env.use_eq =
                      (uu___508_3210.FStar_TypeChecker_Env.use_eq);
                    FStar_TypeChecker_Env.use_eq_strict =
                      (uu___508_3210.FStar_TypeChecker_Env.use_eq_strict);
                    FStar_TypeChecker_Env.is_iface =
                      (uu___508_3210.FStar_TypeChecker_Env.is_iface);
                    FStar_TypeChecker_Env.admit =
                      (uu___508_3210.FStar_TypeChecker_Env.admit);
                    FStar_TypeChecker_Env.lax =
                      (uu___508_3210.FStar_TypeChecker_Env.lax);
                    FStar_TypeChecker_Env.lax_universes =
                      (uu___508_3210.FStar_TypeChecker_Env.lax_universes);
                    FStar_TypeChecker_Env.phase1 =
                      (uu___508_3210.FStar_TypeChecker_Env.phase1);
                    FStar_TypeChecker_Env.failhard =
                      (uu___508_3210.FStar_TypeChecker_Env.failhard);
                    FStar_TypeChecker_Env.nosynth =
                      (uu___508_3210.FStar_TypeChecker_Env.nosynth);
                    FStar_TypeChecker_Env.uvar_subtyping = false;
                    FStar_TypeChecker_Env.tc_term =
                      (uu___508_3210.FStar_TypeChecker_Env.tc_term);
                    FStar_TypeChecker_Env.type_of =
                      (uu___508_3210.FStar_TypeChecker_Env.type_of);
                    FStar_TypeChecker_Env.universe_of =
                      (uu___508_3210.FStar_TypeChecker_Env.universe_of);
                    FStar_TypeChecker_Env.check_type_of =
                      (uu___508_3210.FStar_TypeChecker_Env.check_type_of);
                    FStar_TypeChecker_Env.use_bv_sorts =
                      (uu___508_3210.FStar_TypeChecker_Env.use_bv_sorts);
                    FStar_TypeChecker_Env.qtbl_name_and_index =
                      (uu___508_3210.FStar_TypeChecker_Env.qtbl_name_and_index);
                    FStar_TypeChecker_Env.normalized_eff_names =
                      (uu___508_3210.FStar_TypeChecker_Env.normalized_eff_names);
                    FStar_TypeChecker_Env.fv_delta_depths =
                      (uu___508_3210.FStar_TypeChecker_Env.fv_delta_depths);
                    FStar_TypeChecker_Env.proof_ns =
                      (uu___508_3210.FStar_TypeChecker_Env.proof_ns);
                    FStar_TypeChecker_Env.synth_hook =
                      (uu___508_3210.FStar_TypeChecker_Env.synth_hook);
                    FStar_TypeChecker_Env.try_solve_implicits_hook =
                      (uu___508_3210.FStar_TypeChecker_Env.try_solve_implicits_hook);
                    FStar_TypeChecker_Env.splice =
                      (uu___508_3210.FStar_TypeChecker_Env.splice);
                    FStar_TypeChecker_Env.mpreprocess =
                      (uu___508_3210.FStar_TypeChecker_Env.mpreprocess);
                    FStar_TypeChecker_Env.postprocess =
                      (uu___508_3210.FStar_TypeChecker_Env.postprocess);
                    FStar_TypeChecker_Env.is_native_tactic =
                      (uu___508_3210.FStar_TypeChecker_Env.is_native_tactic);
                    FStar_TypeChecker_Env.identifier_info =
                      (uu___508_3210.FStar_TypeChecker_Env.identifier_info);
                    FStar_TypeChecker_Env.tc_hooks =
                      (uu___508_3210.FStar_TypeChecker_Env.tc_hooks);
                    FStar_TypeChecker_Env.dsenv =
                      (uu___508_3210.FStar_TypeChecker_Env.dsenv);
                    FStar_TypeChecker_Env.nbe =
                      (uu___508_3210.FStar_TypeChecker_Env.nbe);
                    FStar_TypeChecker_Env.strict_args_tab =
                      (uu___508_3210.FStar_TypeChecker_Env.strict_args_tab);
                    FStar_TypeChecker_Env.erasable_types_tab =
                      (uu___508_3210.FStar_TypeChecker_Env.erasable_types_tab)
                  }  in
                try
                  (fun uu___512_3225  ->
                     match () with
                     | () ->
                         let uu____3234 =
                           FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term e1 t
                            in
                         (match uu____3234 with
                          | (t1,lc,g) ->
                              ret
                                (t1, (lc.FStar_TypeChecker_Common.res_typ),
                                  g))) ()
                with
                | FStar_Errors.Err (uu____3272,msg) ->
                    let uu____3276 = tts e1 t  in
                    let uu____3278 =
                      let uu____3280 = FStar_TypeChecker_Env.all_binders e1
                         in
                      FStar_All.pipe_right uu____3280
                        (FStar_Syntax_Print.binders_to_string ", ")
                       in
                    fail3 "Cannot type %s in context (%s). Error = (%s)"
                      uu____3276 uu____3278 msg
                | FStar_Errors.Error (uu____3290,msg,uu____3292) ->
                    let uu____3295 = tts e1 t  in
                    let uu____3297 =
                      let uu____3299 = FStar_TypeChecker_Env.all_binders e1
                         in
                      FStar_All.pipe_right uu____3299
                        (FStar_Syntax_Print.binders_to_string ", ")
                       in
                    fail3 "Cannot type %s in context (%s). Error = (%s)"
                      uu____3295 uu____3297 msg))
  
let (__tc_lax :
  env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term * FStar_TypeChecker_Common.lcomp *
        FStar_TypeChecker_Common.guard_t) tac)
  =
  fun e  ->
    fun t  ->
      bind get
        (fun ps  ->
           mlog
             (fun uu____3352  ->
                let uu____3353 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.print1 "Tac> __tc_lax(%s)\n" uu____3353)
             (fun uu____3359  ->
                let e1 =
                  let uu___533_3361 = e  in
                  {
                    FStar_TypeChecker_Env.solver =
                      (uu___533_3361.FStar_TypeChecker_Env.solver);
                    FStar_TypeChecker_Env.range =
                      (uu___533_3361.FStar_TypeChecker_Env.range);
                    FStar_TypeChecker_Env.curmodule =
                      (uu___533_3361.FStar_TypeChecker_Env.curmodule);
                    FStar_TypeChecker_Env.gamma =
                      (uu___533_3361.FStar_TypeChecker_Env.gamma);
                    FStar_TypeChecker_Env.gamma_sig =
                      (uu___533_3361.FStar_TypeChecker_Env.gamma_sig);
                    FStar_TypeChecker_Env.gamma_cache =
                      (uu___533_3361.FStar_TypeChecker_Env.gamma_cache);
                    FStar_TypeChecker_Env.modules =
                      (uu___533_3361.FStar_TypeChecker_Env.modules);
                    FStar_TypeChecker_Env.expected_typ =
                      (uu___533_3361.FStar_TypeChecker_Env.expected_typ);
                    FStar_TypeChecker_Env.sigtab =
                      (uu___533_3361.FStar_TypeChecker_Env.sigtab);
                    FStar_TypeChecker_Env.attrtab =
                      (uu___533_3361.FStar_TypeChecker_Env.attrtab);
                    FStar_TypeChecker_Env.instantiate_imp =
                      (uu___533_3361.FStar_TypeChecker_Env.instantiate_imp);
                    FStar_TypeChecker_Env.effects =
                      (uu___533_3361.FStar_TypeChecker_Env.effects);
                    FStar_TypeChecker_Env.generalize =
                      (uu___533_3361.FStar_TypeChecker_Env.generalize);
                    FStar_TypeChecker_Env.letrecs =
                      (uu___533_3361.FStar_TypeChecker_Env.letrecs);
                    FStar_TypeChecker_Env.top_level =
                      (uu___533_3361.FStar_TypeChecker_Env.top_level);
                    FStar_TypeChecker_Env.check_uvars =
                      (uu___533_3361.FStar_TypeChecker_Env.check_uvars);
                    FStar_TypeChecker_Env.use_eq =
                      (uu___533_3361.FStar_TypeChecker_Env.use_eq);
                    FStar_TypeChecker_Env.use_eq_strict =
                      (uu___533_3361.FStar_TypeChecker_Env.use_eq_strict);
                    FStar_TypeChecker_Env.is_iface =
                      (uu___533_3361.FStar_TypeChecker_Env.is_iface);
                    FStar_TypeChecker_Env.admit =
                      (uu___533_3361.FStar_TypeChecker_Env.admit);
                    FStar_TypeChecker_Env.lax =
                      (uu___533_3361.FStar_TypeChecker_Env.lax);
                    FStar_TypeChecker_Env.lax_universes =
                      (uu___533_3361.FStar_TypeChecker_Env.lax_universes);
                    FStar_TypeChecker_Env.phase1 =
                      (uu___533_3361.FStar_TypeChecker_Env.phase1);
                    FStar_TypeChecker_Env.failhard =
                      (uu___533_3361.FStar_TypeChecker_Env.failhard);
                    FStar_TypeChecker_Env.nosynth =
                      (uu___533_3361.FStar_TypeChecker_Env.nosynth);
                    FStar_TypeChecker_Env.uvar_subtyping = false;
                    FStar_TypeChecker_Env.tc_term =
                      (uu___533_3361.FStar_TypeChecker_Env.tc_term);
                    FStar_TypeChecker_Env.type_of =
                      (uu___533_3361.FStar_TypeChecker_Env.type_of);
                    FStar_TypeChecker_Env.universe_of =
                      (uu___533_3361.FStar_TypeChecker_Env.universe_of);
                    FStar_TypeChecker_Env.check_type_of =
                      (uu___533_3361.FStar_TypeChecker_Env.check_type_of);
                    FStar_TypeChecker_Env.use_bv_sorts =
                      (uu___533_3361.FStar_TypeChecker_Env.use_bv_sorts);
                    FStar_TypeChecker_Env.qtbl_name_and_index =
                      (uu___533_3361.FStar_TypeChecker_Env.qtbl_name_and_index);
                    FStar_TypeChecker_Env.normalized_eff_names =
                      (uu___533_3361.FStar_TypeChecker_Env.normalized_eff_names);
                    FStar_TypeChecker_Env.fv_delta_depths =
                      (uu___533_3361.FStar_TypeChecker_Env.fv_delta_depths);
                    FStar_TypeChecker_Env.proof_ns =
                      (uu___533_3361.FStar_TypeChecker_Env.proof_ns);
                    FStar_TypeChecker_Env.synth_hook =
                      (uu___533_3361.FStar_TypeChecker_Env.synth_hook);
                    FStar_TypeChecker_Env.try_solve_implicits_hook =
                      (uu___533_3361.FStar_TypeChecker_Env.try_solve_implicits_hook);
                    FStar_TypeChecker_Env.splice =
                      (uu___533_3361.FStar_TypeChecker_Env.splice);
                    FStar_TypeChecker_Env.mpreprocess =
                      (uu___533_3361.FStar_TypeChecker_Env.mpreprocess);
                    FStar_TypeChecker_Env.postprocess =
                      (uu___533_3361.FStar_TypeChecker_Env.postprocess);
                    FStar_TypeChecker_Env.is_native_tactic =
                      (uu___533_3361.FStar_TypeChecker_Env.is_native_tactic);
                    FStar_TypeChecker_Env.identifier_info =
                      (uu___533_3361.FStar_TypeChecker_Env.identifier_info);
                    FStar_TypeChecker_Env.tc_hooks =
                      (uu___533_3361.FStar_TypeChecker_Env.tc_hooks);
                    FStar_TypeChecker_Env.dsenv =
                      (uu___533_3361.FStar_TypeChecker_Env.dsenv);
                    FStar_TypeChecker_Env.nbe =
                      (uu___533_3361.FStar_TypeChecker_Env.nbe);
                    FStar_TypeChecker_Env.strict_args_tab =
                      (uu___533_3361.FStar_TypeChecker_Env.strict_args_tab);
                    FStar_TypeChecker_Env.erasable_types_tab =
                      (uu___533_3361.FStar_TypeChecker_Env.erasable_types_tab)
                  }  in
                let e2 =
                  let uu___536_3364 = e1  in
                  {
                    FStar_TypeChecker_Env.solver =
                      (uu___536_3364.FStar_TypeChecker_Env.solver);
                    FStar_TypeChecker_Env.range =
                      (uu___536_3364.FStar_TypeChecker_Env.range);
                    FStar_TypeChecker_Env.curmodule =
                      (uu___536_3364.FStar_TypeChecker_Env.curmodule);
                    FStar_TypeChecker_Env.gamma =
                      (uu___536_3364.FStar_TypeChecker_Env.gamma);
                    FStar_TypeChecker_Env.gamma_sig =
                      (uu___536_3364.FStar_TypeChecker_Env.gamma_sig);
                    FStar_TypeChecker_Env.gamma_cache =
                      (uu___536_3364.FStar_TypeChecker_Env.gamma_cache);
                    FStar_TypeChecker_Env.modules =
                      (uu___536_3364.FStar_TypeChecker_Env.modules);
                    FStar_TypeChecker_Env.expected_typ =
                      (uu___536_3364.FStar_TypeChecker_Env.expected_typ);
                    FStar_TypeChecker_Env.sigtab =
                      (uu___536_3364.FStar_TypeChecker_Env.sigtab);
                    FStar_TypeChecker_Env.attrtab =
                      (uu___536_3364.FStar_TypeChecker_Env.attrtab);
                    FStar_TypeChecker_Env.instantiate_imp =
                      (uu___536_3364.FStar_TypeChecker_Env.instantiate_imp);
                    FStar_TypeChecker_Env.effects =
                      (uu___536_3364.FStar_TypeChecker_Env.effects);
                    FStar_TypeChecker_Env.generalize =
                      (uu___536_3364.FStar_TypeChecker_Env.generalize);
                    FStar_TypeChecker_Env.letrecs =
                      (uu___536_3364.FStar_TypeChecker_Env.letrecs);
                    FStar_TypeChecker_Env.top_level =
                      (uu___536_3364.FStar_TypeChecker_Env.top_level);
                    FStar_TypeChecker_Env.check_uvars =
                      (uu___536_3364.FStar_TypeChecker_Env.check_uvars);
                    FStar_TypeChecker_Env.use_eq =
                      (uu___536_3364.FStar_TypeChecker_Env.use_eq);
                    FStar_TypeChecker_Env.use_eq_strict =
                      (uu___536_3364.FStar_TypeChecker_Env.use_eq_strict);
                    FStar_TypeChecker_Env.is_iface =
                      (uu___536_3364.FStar_TypeChecker_Env.is_iface);
                    FStar_TypeChecker_Env.admit =
                      (uu___536_3364.FStar_TypeChecker_Env.admit);
                    FStar_TypeChecker_Env.lax = true;
                    FStar_TypeChecker_Env.lax_universes =
                      (uu___536_3364.FStar_TypeChecker_Env.lax_universes);
                    FStar_TypeChecker_Env.phase1 =
                      (uu___536_3364.FStar_TypeChecker_Env.phase1);
                    FStar_TypeChecker_Env.failhard =
                      (uu___536_3364.FStar_TypeChecker_Env.failhard);
                    FStar_TypeChecker_Env.nosynth =
                      (uu___536_3364.FStar_TypeChecker_Env.nosynth);
                    FStar_TypeChecker_Env.uvar_subtyping =
                      (uu___536_3364.FStar_TypeChecker_Env.uvar_subtyping);
                    FStar_TypeChecker_Env.tc_term =
                      (uu___536_3364.FStar_TypeChecker_Env.tc_term);
                    FStar_TypeChecker_Env.type_of =
                      (uu___536_3364.FStar_TypeChecker_Env.type_of);
                    FStar_TypeChecker_Env.universe_of =
                      (uu___536_3364.FStar_TypeChecker_Env.universe_of);
                    FStar_TypeChecker_Env.check_type_of =
                      (uu___536_3364.FStar_TypeChecker_Env.check_type_of);
                    FStar_TypeChecker_Env.use_bv_sorts =
                      (uu___536_3364.FStar_TypeChecker_Env.use_bv_sorts);
                    FStar_TypeChecker_Env.qtbl_name_and_index =
                      (uu___536_3364.FStar_TypeChecker_Env.qtbl_name_and_index);
                    FStar_TypeChecker_Env.normalized_eff_names =
                      (uu___536_3364.FStar_TypeChecker_Env.normalized_eff_names);
                    FStar_TypeChecker_Env.fv_delta_depths =
                      (uu___536_3364.FStar_TypeChecker_Env.fv_delta_depths);
                    FStar_TypeChecker_Env.proof_ns =
                      (uu___536_3364.FStar_TypeChecker_Env.proof_ns);
                    FStar_TypeChecker_Env.synth_hook =
                      (uu___536_3364.FStar_TypeChecker_Env.synth_hook);
                    FStar_TypeChecker_Env.try_solve_implicits_hook =
                      (uu___536_3364.FStar_TypeChecker_Env.try_solve_implicits_hook);
                    FStar_TypeChecker_Env.splice =
                      (uu___536_3364.FStar_TypeChecker_Env.splice);
                    FStar_TypeChecker_Env.mpreprocess =
                      (uu___536_3364.FStar_TypeChecker_Env.mpreprocess);
                    FStar_TypeChecker_Env.postprocess =
                      (uu___536_3364.FStar_TypeChecker_Env.postprocess);
                    FStar_TypeChecker_Env.is_native_tactic =
                      (uu___536_3364.FStar_TypeChecker_Env.is_native_tactic);
                    FStar_TypeChecker_Env.identifier_info =
                      (uu___536_3364.FStar_TypeChecker_Env.identifier_info);
                    FStar_TypeChecker_Env.tc_hooks =
                      (uu___536_3364.FStar_TypeChecker_Env.tc_hooks);
                    FStar_TypeChecker_Env.dsenv =
                      (uu___536_3364.FStar_TypeChecker_Env.dsenv);
                    FStar_TypeChecker_Env.nbe =
                      (uu___536_3364.FStar_TypeChecker_Env.nbe);
                    FStar_TypeChecker_Env.strict_args_tab =
                      (uu___536_3364.FStar_TypeChecker_Env.strict_args_tab);
                    FStar_TypeChecker_Env.erasable_types_tab =
                      (uu___536_3364.FStar_TypeChecker_Env.erasable_types_tab)
                  }  in
                try
                  (fun uu___540_3376  ->
                     match () with
                     | () ->
                         let uu____3385 =
                           FStar_TypeChecker_TcTerm.tc_term e2 t  in
                         ret uu____3385) ()
                with
                | FStar_Errors.Err (uu____3412,msg) ->
                    let uu____3416 = tts e2 t  in
                    let uu____3418 =
                      let uu____3420 = FStar_TypeChecker_Env.all_binders e2
                         in
                      FStar_All.pipe_right uu____3420
                        (FStar_Syntax_Print.binders_to_string ", ")
                       in
                    fail3 "Cannot type %s in context (%s). Error = (%s)"
                      uu____3416 uu____3418 msg
                | FStar_Errors.Error (uu____3430,msg,uu____3432) ->
                    let uu____3435 = tts e2 t  in
                    let uu____3437 =
                      let uu____3439 = FStar_TypeChecker_Env.all_binders e2
                         in
                      FStar_All.pipe_right uu____3439
                        (FStar_Syntax_Print.binders_to_string ", ")
                       in
                    fail3 "Cannot type %s in context (%s). Error = (%s)"
                      uu____3435 uu____3437 msg))
  
let (istrivial : env -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun e  ->
    fun t  ->
      let steps =
        [FStar_TypeChecker_Env.Reify;
        FStar_TypeChecker_Env.UnfoldUntil FStar_Syntax_Syntax.delta_constant;
        FStar_TypeChecker_Env.Primops;
        FStar_TypeChecker_Env.Simplify;
        FStar_TypeChecker_Env.UnfoldTac;
        FStar_TypeChecker_Env.Unmeta]  in
      let t1 = normalize steps e t  in is_true t1
  
let (get_guard_policy : unit -> FStar_Tactics_Types.guard_policy tac) =
  fun uu____3473  ->
    bind get (fun ps  -> ret ps.FStar_Tactics_Types.guard_policy)
  
let (set_guard_policy : FStar_Tactics_Types.guard_policy -> unit tac) =
  fun pol  ->
    bind get
      (fun ps  ->
         set
           (let uu___561_3492 = ps  in
            {
              FStar_Tactics_Types.main_context =
                (uu___561_3492.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.all_implicits =
                (uu___561_3492.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___561_3492.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (uu___561_3492.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___561_3492.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___561_3492.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___561_3492.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___561_3492.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy = pol;
              FStar_Tactics_Types.freshness =
                (uu___561_3492.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___561_3492.FStar_Tactics_Types.tac_verb_dbg);
              FStar_Tactics_Types.local_state =
                (uu___561_3492.FStar_Tactics_Types.local_state)
            }))
  
let with_policy : 'a . FStar_Tactics_Types.guard_policy -> 'a tac -> 'a tac =
  fun pol  ->
    fun t  ->
      let uu____3517 = get_guard_policy ()  in
      bind uu____3517
        (fun old_pol  ->
           let uu____3523 = set_guard_policy pol  in
           bind uu____3523
             (fun uu____3527  ->
                bind t
                  (fun r  ->
                     let uu____3531 = set_guard_policy old_pol  in
                     bind uu____3531 (fun uu____3535  -> ret r))))
  
let (getopts : FStar_Options.optionstate tac) =
  let uu____3539 = let uu____3544 = cur_goal ()  in trytac uu____3544  in
  bind uu____3539
    (fun uu___0_3551  ->
       match uu___0_3551 with
       | FStar_Pervasives_Native.Some g -> ret g.FStar_Tactics_Types.opts
       | FStar_Pervasives_Native.None  ->
           let uu____3557 = FStar_Options.peek ()  in ret uu____3557)
  
let (proc_guard :
  Prims.string -> env -> FStar_TypeChecker_Common.guard_t -> unit tac) =
  fun reason  ->
    fun e  ->
      fun g  ->
        mlog
          (fun uu____3582  ->
             let uu____3583 = FStar_TypeChecker_Rel.guard_to_string e g  in
             FStar_Util.print2 "Processing guard (%s:%s)\n" reason uu____3583)
          (fun uu____3588  ->
             let uu____3589 =
               add_implicits g.FStar_TypeChecker_Common.implicits  in
             bind uu____3589
               (fun uu____3593  ->
                  bind getopts
                    (fun opts  ->
                       let uu____3597 =
                         let uu____3598 =
                           FStar_TypeChecker_Rel.simplify_guard e g  in
                         uu____3598.FStar_TypeChecker_Common.guard_f  in
                       match uu____3597 with
                       | FStar_TypeChecker_Common.Trivial  -> ret ()
                       | FStar_TypeChecker_Common.NonTrivial f ->
                           let uu____3602 = istrivial e f  in
                           if uu____3602
                           then ret ()
                           else
                             bind get
                               (fun ps  ->
                                  match ps.FStar_Tactics_Types.guard_policy
                                  with
                                  | FStar_Tactics_Types.Drop  ->
                                      ((let uu____3615 =
                                          let uu____3621 =
                                            let uu____3623 =
                                              FStar_TypeChecker_Rel.guard_to_string
                                                e g
                                               in
                                            FStar_Util.format1
                                              "Tactics admitted guard <%s>\n\n"
                                              uu____3623
                                             in
                                          (FStar_Errors.Warning_TacAdmit,
                                            uu____3621)
                                           in
                                        FStar_Errors.log_issue
                                          e.FStar_TypeChecker_Env.range
                                          uu____3615);
                                       ret ())
                                  | FStar_Tactics_Types.Goal  ->
                                      mlog
                                        (fun uu____3629  ->
                                           let uu____3630 =
                                             FStar_TypeChecker_Rel.guard_to_string
                                               e g
                                              in
                                           FStar_Util.print2
                                             "Making guard (%s:%s) into a goal\n"
                                             reason uu____3630)
                                        (fun uu____3635  ->
                                           let uu____3636 =
                                             mk_irrelevant_goal reason e f
                                               opts ""
                                              in
                                           bind uu____3636
                                             (fun goal  ->
                                                let goal1 =
                                                  let uu___590_3644 = goal
                                                     in
                                                  {
                                                    FStar_Tactics_Types.goal_main_env
                                                      =
                                                      (uu___590_3644.FStar_Tactics_Types.goal_main_env);
                                                    FStar_Tactics_Types.goal_ctx_uvar
                                                      =
                                                      (uu___590_3644.FStar_Tactics_Types.goal_ctx_uvar);
                                                    FStar_Tactics_Types.opts
                                                      =
                                                      (uu___590_3644.FStar_Tactics_Types.opts);
                                                    FStar_Tactics_Types.is_guard
                                                      = true;
                                                    FStar_Tactics_Types.label
                                                      =
                                                      (uu___590_3644.FStar_Tactics_Types.label)
                                                  }  in
                                                push_goals [goal1]))
                                  | FStar_Tactics_Types.SMT  ->
                                      mlog
                                        (fun uu____3648  ->
                                           let uu____3649 =
                                             FStar_TypeChecker_Rel.guard_to_string
                                               e g
                                              in
                                           FStar_Util.print2
                                             "Sending guard (%s:%s) to SMT goal\n"
                                             reason uu____3649)
                                        (fun uu____3654  ->
                                           let uu____3655 =
                                             mk_irrelevant_goal reason e f
                                               opts ""
                                              in
                                           bind uu____3655
                                             (fun goal  ->
                                                let goal1 =
                                                  let uu___597_3663 = goal
                                                     in
                                                  {
                                                    FStar_Tactics_Types.goal_main_env
                                                      =
                                                      (uu___597_3663.FStar_Tactics_Types.goal_main_env);
                                                    FStar_Tactics_Types.goal_ctx_uvar
                                                      =
                                                      (uu___597_3663.FStar_Tactics_Types.goal_ctx_uvar);
                                                    FStar_Tactics_Types.opts
                                                      =
                                                      (uu___597_3663.FStar_Tactics_Types.opts);
                                                    FStar_Tactics_Types.is_guard
                                                      = true;
                                                    FStar_Tactics_Types.label
                                                      =
                                                      (uu___597_3663.FStar_Tactics_Types.label)
                                                  }  in
                                                push_smt_goals [goal1]))
                                  | FStar_Tactics_Types.Force  ->
                                      mlog
                                        (fun uu____3667  ->
                                           let uu____3668 =
                                             FStar_TypeChecker_Rel.guard_to_string
                                               e g
                                              in
                                           FStar_Util.print2
                                             "Forcing guard (%s:%s)\n" reason
                                             uu____3668)
                                        (fun uu____3672  ->
                                           try
                                             (fun uu___604_3677  ->
                                                match () with
                                                | () ->
                                                    let uu____3680 =
                                                      let uu____3682 =
                                                        let uu____3684 =
                                                          FStar_TypeChecker_Rel.discharge_guard_no_smt
                                                            e g
                                                           in
                                                        FStar_All.pipe_left
                                                          FStar_TypeChecker_Env.is_trivial
                                                          uu____3684
                                                         in
                                                      Prims.op_Negation
                                                        uu____3682
                                                       in
                                                    if uu____3680
                                                    then
                                                      mlog
                                                        (fun uu____3691  ->
                                                           let uu____3692 =
                                                             FStar_TypeChecker_Rel.guard_to_string
                                                               e g
                                                              in
                                                           FStar_Util.print1
                                                             "guard = %s\n"
                                                             uu____3692)
                                                        (fun uu____3696  ->
                                                           fail1
                                                             "Forcing the guard failed (%s)"
                                                             reason)
                                                    else ret ()) ()
                                           with
                                           | uu___603_3701 ->
                                               mlog
                                                 (fun uu____3706  ->
                                                    let uu____3707 =
                                                      FStar_TypeChecker_Rel.guard_to_string
                                                        e g
                                                       in
                                                    FStar_Util.print1
                                                      "guard = %s\n"
                                                      uu____3707)
                                                 (fun uu____3711  ->
                                                    fail1
                                                      "Forcing the guard failed (%s)"
                                                      reason))))))
  
let (tcc : env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.comp tac) =
  fun e  ->
    fun t  ->
      let uu____3728 =
        let uu____3731 = __tc_lax e t  in
        bind uu____3731
          (fun uu____3751  ->
             match uu____3751 with
             | (uu____3760,lc,uu____3762) ->
                 let uu____3763 =
                   let uu____3764 = FStar_TypeChecker_Common.lcomp_comp lc
                      in
                   FStar_All.pipe_right uu____3764
                     FStar_Pervasives_Native.fst
                    in
                 ret uu____3763)
         in
      FStar_All.pipe_left (wrap_err "tcc") uu____3728
  
let (tc : env -> FStar_Syntax_Syntax.term -> FStar_Reflection_Data.typ tac) =
  fun e  ->
    fun t  ->
      let uu____3793 =
        let uu____3798 = tcc e t  in
        bind uu____3798 (fun c  -> ret (FStar_Syntax_Util.comp_result c))  in
      FStar_All.pipe_left (wrap_err "tc") uu____3793
  
let (add_irrelevant_goal :
  Prims.string ->
    env ->
      FStar_Reflection_Data.typ ->
        FStar_Options.optionstate -> Prims.string -> unit tac)
  =
  fun reason  ->
    fun env  ->
      fun phi  ->
        fun opts  ->
          fun label1  ->
            let uu____3850 = mk_irrelevant_goal reason env phi opts label1
               in
            bind uu____3850 (fun goal  -> add_goals [goal])
  
let (trivial : unit -> unit tac) =
  fun uu____3862  ->
    let uu____3865 = cur_goal ()  in
    bind uu____3865
      (fun goal  ->
         let uu____3871 =
           let uu____3873 = FStar_Tactics_Types.goal_env goal  in
           let uu____3874 = FStar_Tactics_Types.goal_type goal  in
           istrivial uu____3873 uu____3874  in
         if uu____3871
         then solve' goal FStar_Syntax_Util.exp_unit
         else
           (let uu____3880 =
              let uu____3882 = FStar_Tactics_Types.goal_env goal  in
              let uu____3883 = FStar_Tactics_Types.goal_type goal  in
              tts uu____3882 uu____3883  in
            fail1 "Not a trivial goal: %s" uu____3880))
  
let divide : 'a 'b . FStar_BigInt.t -> 'a tac -> 'b tac -> ('a * 'b) tac =
  fun n1  ->
    fun l  ->
      fun r  ->
        bind get
          (fun p  ->
             let uu____3934 =
               try
                 (fun uu___663_3957  ->
                    match () with
                    | () ->
                        let uu____3968 =
                          let uu____3977 = FStar_BigInt.to_int_fs n1  in
                          FStar_List.splitAt uu____3977
                            p.FStar_Tactics_Types.goals
                           in
                        ret uu____3968) ()
               with | uu___662_3988 -> fail "divide: not enough goals"  in
             bind uu____3934
               (fun uu____4025  ->
                  match uu____4025 with
                  | (lgs,rgs) ->
                      let lp =
                        let uu___645_4051 = p  in
                        {
                          FStar_Tactics_Types.main_context =
                            (uu___645_4051.FStar_Tactics_Types.main_context);
                          FStar_Tactics_Types.all_implicits =
                            (uu___645_4051.FStar_Tactics_Types.all_implicits);
                          FStar_Tactics_Types.goals = lgs;
                          FStar_Tactics_Types.smt_goals = [];
                          FStar_Tactics_Types.depth =
                            (uu___645_4051.FStar_Tactics_Types.depth);
                          FStar_Tactics_Types.__dump =
                            (uu___645_4051.FStar_Tactics_Types.__dump);
                          FStar_Tactics_Types.psc =
                            (uu___645_4051.FStar_Tactics_Types.psc);
                          FStar_Tactics_Types.entry_range =
                            (uu___645_4051.FStar_Tactics_Types.entry_range);
                          FStar_Tactics_Types.guard_policy =
                            (uu___645_4051.FStar_Tactics_Types.guard_policy);
                          FStar_Tactics_Types.freshness =
                            (uu___645_4051.FStar_Tactics_Types.freshness);
                          FStar_Tactics_Types.tac_verb_dbg =
                            (uu___645_4051.FStar_Tactics_Types.tac_verb_dbg);
                          FStar_Tactics_Types.local_state =
                            (uu___645_4051.FStar_Tactics_Types.local_state)
                        }  in
                      let uu____4052 = set lp  in
                      bind uu____4052
                        (fun uu____4060  ->
                           bind l
                             (fun a  ->
                                bind get
                                  (fun lp'  ->
                                     let rp =
                                       let uu___651_4076 = lp'  in
                                       {
                                         FStar_Tactics_Types.main_context =
                                           (uu___651_4076.FStar_Tactics_Types.main_context);
                                         FStar_Tactics_Types.all_implicits =
                                           (uu___651_4076.FStar_Tactics_Types.all_implicits);
                                         FStar_Tactics_Types.goals = rgs;
                                         FStar_Tactics_Types.smt_goals = [];
                                         FStar_Tactics_Types.depth =
                                           (uu___651_4076.FStar_Tactics_Types.depth);
                                         FStar_Tactics_Types.__dump =
                                           (uu___651_4076.FStar_Tactics_Types.__dump);
                                         FStar_Tactics_Types.psc =
                                           (uu___651_4076.FStar_Tactics_Types.psc);
                                         FStar_Tactics_Types.entry_range =
                                           (uu___651_4076.FStar_Tactics_Types.entry_range);
                                         FStar_Tactics_Types.guard_policy =
                                           (uu___651_4076.FStar_Tactics_Types.guard_policy);
                                         FStar_Tactics_Types.freshness =
                                           (uu___651_4076.FStar_Tactics_Types.freshness);
                                         FStar_Tactics_Types.tac_verb_dbg =
                                           (uu___651_4076.FStar_Tactics_Types.tac_verb_dbg);
                                         FStar_Tactics_Types.local_state =
                                           (uu___651_4076.FStar_Tactics_Types.local_state)
                                       }  in
                                     let uu____4077 = set rp  in
                                     bind uu____4077
                                       (fun uu____4085  ->
                                          bind r
                                            (fun b  ->
                                               bind get
                                                 (fun rp'  ->
                                                    let p' =
                                                      let uu___657_4101 = rp'
                                                         in
                                                      {
                                                        FStar_Tactics_Types.main_context
                                                          =
                                                          (uu___657_4101.FStar_Tactics_Types.main_context);
                                                        FStar_Tactics_Types.all_implicits
                                                          =
                                                          (uu___657_4101.FStar_Tactics_Types.all_implicits);
                                                        FStar_Tactics_Types.goals
                                                          =
                                                          (FStar_List.append
                                                             lp'.FStar_Tactics_Types.goals
                                                             rp'.FStar_Tactics_Types.goals);
                                                        FStar_Tactics_Types.smt_goals
                                                          =
                                                          (FStar_List.append
                                                             lp'.FStar_Tactics_Types.smt_goals
                                                             (FStar_List.append
                                                                rp'.FStar_Tactics_Types.smt_goals
                                                                p.FStar_Tactics_Types.smt_goals));
                                                        FStar_Tactics_Types.depth
                                                          =
                                                          (uu___657_4101.FStar_Tactics_Types.depth);
                                                        FStar_Tactics_Types.__dump
                                                          =
                                                          (uu___657_4101.FStar_Tactics_Types.__dump);
                                                        FStar_Tactics_Types.psc
                                                          =
                                                          (uu___657_4101.FStar_Tactics_Types.psc);
                                                        FStar_Tactics_Types.entry_range
                                                          =
                                                          (uu___657_4101.FStar_Tactics_Types.entry_range);
                                                        FStar_Tactics_Types.guard_policy
                                                          =
                                                          (uu___657_4101.FStar_Tactics_Types.guard_policy);
                                                        FStar_Tactics_Types.freshness
                                                          =
                                                          (uu___657_4101.FStar_Tactics_Types.freshness);
                                                        FStar_Tactics_Types.tac_verb_dbg
                                                          =
                                                          (uu___657_4101.FStar_Tactics_Types.tac_verb_dbg);
                                                        FStar_Tactics_Types.local_state
                                                          =
                                                          (uu___657_4101.FStar_Tactics_Types.local_state)
                                                      }  in
                                                    let uu____4102 = set p'
                                                       in
                                                    bind uu____4102
                                                      (fun uu____4110  ->
                                                         bind
                                                           remove_solved_goals
                                                           (fun uu____4116 
                                                              -> ret (a, b)))))))))))
  
let focus : 'a . 'a tac -> 'a tac =
  fun f  ->
    let uu____4138 = divide FStar_BigInt.one f idtac  in
    bind uu____4138
      (fun uu____4151  -> match uu____4151 with | (a,()) -> ret a)
  
let rec map : 'a . 'a tac -> 'a Prims.list tac =
  fun tau  ->
    bind get
      (fun p  ->
         match p.FStar_Tactics_Types.goals with
         | [] -> ret []
         | uu____4189::uu____4190 ->
             let uu____4193 =
               let uu____4202 = map tau  in
               divide FStar_BigInt.one tau uu____4202  in
             bind uu____4193
               (fun uu____4220  ->
                  match uu____4220 with | (h,t) -> ret (h :: t)))
  
let (seq : unit tac -> unit tac -> unit tac) =
  fun t1  ->
    fun t2  ->
      let uu____4262 =
        bind t1
          (fun uu____4267  ->
             let uu____4268 = map t2  in
             bind uu____4268 (fun uu____4276  -> ret ()))
         in
      focus uu____4262
  
let (intro : unit -> FStar_Syntax_Syntax.binder tac) =
  fun uu____4286  ->
    let uu____4289 =
      let uu____4292 = cur_goal ()  in
      bind uu____4292
        (fun goal  ->
           let uu____4301 =
             let uu____4308 = FStar_Tactics_Types.goal_type goal  in
             FStar_Syntax_Util.arrow_one uu____4308  in
           match uu____4301 with
           | FStar_Pervasives_Native.Some (b,c) ->
               let uu____4317 =
                 let uu____4319 = FStar_Syntax_Util.is_total_comp c  in
                 Prims.op_Negation uu____4319  in
               if uu____4317
               then fail "Codomain is effectful"
               else
                 (let env' =
                    let uu____4328 = FStar_Tactics_Types.goal_env goal  in
                    FStar_TypeChecker_Env.push_binders uu____4328 [b]  in
                  let typ' = FStar_Syntax_Util.comp_result c  in
                  let uu____4344 = new_uvar "intro" env' typ'  in
                  bind uu____4344
                    (fun uu____4361  ->
                       match uu____4361 with
                       | (body,ctx_uvar) ->
                           let sol =
                             FStar_Syntax_Util.abs [b] body
                               (FStar_Pervasives_Native.Some
                                  (FStar_Syntax_Util.residual_comp_of_comp c))
                              in
                           let uu____4385 = set_solution goal sol  in
                           bind uu____4385
                             (fun uu____4391  ->
                                let g =
                                  FStar_Tactics_Types.mk_goal env' ctx_uvar
                                    goal.FStar_Tactics_Types.opts
                                    goal.FStar_Tactics_Types.is_guard
                                    goal.FStar_Tactics_Types.label
                                   in
                                let uu____4393 =
                                  let uu____4396 = bnorm_goal g  in
                                  replace_cur uu____4396  in
                                bind uu____4393 (fun uu____4398  -> ret b))))
           | FStar_Pervasives_Native.None  ->
               let uu____4403 =
                 let uu____4405 = FStar_Tactics_Types.goal_env goal  in
                 let uu____4406 = FStar_Tactics_Types.goal_type goal  in
                 tts uu____4405 uu____4406  in
               fail1 "goal is not an arrow (%s)" uu____4403)
       in
    FStar_All.pipe_left (wrap_err "intro") uu____4289
  
let (intro_rec :
  unit -> (FStar_Syntax_Syntax.binder * FStar_Syntax_Syntax.binder) tac) =
  fun uu____4424  ->
    let uu____4431 = cur_goal ()  in
    bind uu____4431
      (fun goal  ->
         FStar_Util.print_string
           "WARNING (intro_rec): calling this is known to cause normalizer loops\n";
         FStar_Util.print_string
           "WARNING (intro_rec): proceed at your own risk...\n";
         (let uu____4450 =
            let uu____4457 = FStar_Tactics_Types.goal_type goal  in
            FStar_Syntax_Util.arrow_one uu____4457  in
          match uu____4450 with
          | FStar_Pervasives_Native.Some (b,c) ->
              let uu____4470 =
                let uu____4472 = FStar_Syntax_Util.is_total_comp c  in
                Prims.op_Negation uu____4472  in
              if uu____4470
              then fail "Codomain is effectful"
              else
                (let bv =
                   let uu____4489 = FStar_Tactics_Types.goal_type goal  in
                   FStar_Syntax_Syntax.gen_bv "__recf"
                     FStar_Pervasives_Native.None uu____4489
                    in
                 let bs =
                   let uu____4500 = FStar_Syntax_Syntax.mk_binder bv  in
                   [uu____4500; b]  in
                 let env' =
                   let uu____4526 = FStar_Tactics_Types.goal_env goal  in
                   FStar_TypeChecker_Env.push_binders uu____4526 bs  in
                 let uu____4527 =
                   new_uvar "intro_rec" env'
                     (FStar_Syntax_Util.comp_result c)
                    in
                 bind uu____4527
                   (fun uu____4553  ->
                      match uu____4553 with
                      | (u,ctx_uvar_u) ->
                          let lb =
                            let uu____4567 =
                              FStar_Tactics_Types.goal_type goal  in
                            let uu____4570 =
                              FStar_Syntax_Util.abs [b] u
                                FStar_Pervasives_Native.None
                               in
                            FStar_Syntax_Util.mk_letbinding
                              (FStar_Util.Inl bv) [] uu____4567
                              FStar_Parser_Const.effect_Tot_lid uu____4570 []
                              FStar_Range.dummyRange
                             in
                          let body = FStar_Syntax_Syntax.bv_to_name bv  in
                          let uu____4588 =
                            FStar_Syntax_Subst.close_let_rec [lb] body  in
                          (match uu____4588 with
                           | (lbs,body1) ->
                               let tm =
                                 let uu____4610 =
                                   let uu____4611 =
                                     FStar_Tactics_Types.goal_witness goal
                                      in
                                   uu____4611.FStar_Syntax_Syntax.pos  in
                                 FStar_Syntax_Syntax.mk
                                   (FStar_Syntax_Syntax.Tm_let
                                      ((true, lbs), body1))
                                   FStar_Pervasives_Native.None uu____4610
                                  in
                               let uu____4627 = set_solution goal tm  in
                               bind uu____4627
                                 (fun uu____4636  ->
                                    let uu____4637 =
                                      let uu____4640 =
                                        bnorm_goal
                                          (let uu___728_4643 = goal  in
                                           {
                                             FStar_Tactics_Types.goal_main_env
                                               =
                                               (uu___728_4643.FStar_Tactics_Types.goal_main_env);
                                             FStar_Tactics_Types.goal_ctx_uvar
                                               = ctx_uvar_u;
                                             FStar_Tactics_Types.opts =
                                               (uu___728_4643.FStar_Tactics_Types.opts);
                                             FStar_Tactics_Types.is_guard =
                                               (uu___728_4643.FStar_Tactics_Types.is_guard);
                                             FStar_Tactics_Types.label =
                                               (uu___728_4643.FStar_Tactics_Types.label)
                                           })
                                         in
                                      replace_cur uu____4640  in
                                    bind uu____4637
                                      (fun uu____4650  ->
                                         let uu____4651 =
                                           let uu____4656 =
                                             FStar_Syntax_Syntax.mk_binder bv
                                              in
                                           (uu____4656, b)  in
                                         ret uu____4651)))))
          | FStar_Pervasives_Native.None  ->
              let uu____4665 =
                let uu____4667 = FStar_Tactics_Types.goal_env goal  in
                let uu____4668 = FStar_Tactics_Types.goal_type goal  in
                tts uu____4667 uu____4668  in
              fail1 "intro_rec: goal is not an arrow (%s)" uu____4665))
  
let (norm : FStar_Syntax_Embeddings.norm_step Prims.list -> unit tac) =
  fun s  ->
    let uu____4688 = cur_goal ()  in
    bind uu____4688
      (fun goal  ->
         mlog
           (fun uu____4695  ->
              let uu____4696 =
                let uu____4698 = FStar_Tactics_Types.goal_witness goal  in
                FStar_Syntax_Print.term_to_string uu____4698  in
              FStar_Util.print1 "norm: witness = %s\n" uu____4696)
           (fun uu____4704  ->
              let steps =
                let uu____4708 = FStar_TypeChecker_Normalize.tr_norm_steps s
                   in
                FStar_List.append
                  [FStar_TypeChecker_Env.Reify;
                  FStar_TypeChecker_Env.UnfoldTac] uu____4708
                 in
              let t =
                let uu____4712 = FStar_Tactics_Types.goal_env goal  in
                let uu____4713 = FStar_Tactics_Types.goal_type goal  in
                normalize steps uu____4712 uu____4713  in
              let uu____4714 = FStar_Tactics_Types.goal_with_type goal t  in
              replace_cur uu____4714))
  
let (norm_term_env :
  env ->
    FStar_Syntax_Embeddings.norm_step Prims.list ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term tac)
  =
  fun e  ->
    fun s  ->
      fun t  ->
        let uu____4739 =
          bind get
            (fun ps  ->
               let opts =
                 match ps.FStar_Tactics_Types.goals with
                 | g::uu____4747 -> g.FStar_Tactics_Types.opts
                 | uu____4750 -> FStar_Options.peek ()  in
               mlog
                 (fun uu____4755  ->
                    let uu____4756 = FStar_Syntax_Print.term_to_string t  in
                    FStar_Util.print1 "norm_term_env: t = %s\n" uu____4756)
                 (fun uu____4761  ->
                    let uu____4762 = __tc_lax e t  in
                    bind uu____4762
                      (fun uu____4783  ->
                         match uu____4783 with
                         | (t1,uu____4793,uu____4794) ->
                             let steps =
                               let uu____4798 =
                                 FStar_TypeChecker_Normalize.tr_norm_steps s
                                  in
                               FStar_List.append
                                 [FStar_TypeChecker_Env.Reify;
                                 FStar_TypeChecker_Env.UnfoldTac] uu____4798
                                in
                             let t2 =
                               normalize steps
                                 ps.FStar_Tactics_Types.main_context t1
                                in
                             mlog
                               (fun uu____4804  ->
                                  let uu____4805 =
                                    FStar_Syntax_Print.term_to_string t2  in
                                  FStar_Util.print1
                                    "norm_term_env: t' = %s\n" uu____4805)
                               (fun uu____4809  -> ret t2))))
           in
        FStar_All.pipe_left (wrap_err "norm_term") uu____4739
  
let (refine_intro : unit -> unit tac) =
  fun uu____4822  ->
    let uu____4825 =
      let uu____4828 = cur_goal ()  in
      bind uu____4828
        (fun g  ->
           let uu____4835 =
             let uu____4846 = FStar_Tactics_Types.goal_env g  in
             let uu____4847 = FStar_Tactics_Types.goal_type g  in
             FStar_TypeChecker_Rel.base_and_refinement uu____4846 uu____4847
              in
           match uu____4835 with
           | (uu____4850,FStar_Pervasives_Native.None ) ->
               fail "not a refinement"
           | (t,FStar_Pervasives_Native.Some (bv,phi)) ->
               let g1 = FStar_Tactics_Types.goal_with_type g t  in
               let uu____4876 =
                 let uu____4881 =
                   let uu____4886 =
                     let uu____4887 = FStar_Syntax_Syntax.mk_binder bv  in
                     [uu____4887]  in
                   FStar_Syntax_Subst.open_term uu____4886 phi  in
                 match uu____4881 with
                 | (bvs,phi1) ->
                     let uu____4912 =
                       let uu____4913 = FStar_List.hd bvs  in
                       FStar_Pervasives_Native.fst uu____4913  in
                     (uu____4912, phi1)
                  in
               (match uu____4876 with
                | (bv1,phi1) ->
                    let uu____4932 =
                      let uu____4935 = FStar_Tactics_Types.goal_env g  in
                      let uu____4936 =
                        let uu____4937 =
                          let uu____4940 =
                            let uu____4941 =
                              let uu____4948 =
                                FStar_Tactics_Types.goal_witness g  in
                              (bv1, uu____4948)  in
                            FStar_Syntax_Syntax.NT uu____4941  in
                          [uu____4940]  in
                        FStar_Syntax_Subst.subst uu____4937 phi1  in
                      mk_irrelevant_goal "refine_intro refinement" uu____4935
                        uu____4936 g.FStar_Tactics_Types.opts
                        g.FStar_Tactics_Types.label
                       in
                    bind uu____4932
                      (fun g2  ->
                         bind __dismiss
                           (fun uu____4957  -> add_goals [g1; g2]))))
       in
    FStar_All.pipe_left (wrap_err "refine_intro") uu____4825
  
let (__exact_now : Prims.bool -> FStar_Syntax_Syntax.term -> unit tac) =
  fun set_expected_typ1  ->
    fun t  ->
      let uu____4980 = cur_goal ()  in
      bind uu____4980
        (fun goal  ->
           let env =
             if set_expected_typ1
             then
               let uu____4989 = FStar_Tactics_Types.goal_env goal  in
               let uu____4990 = FStar_Tactics_Types.goal_type goal  in
               FStar_TypeChecker_Env.set_expected_typ uu____4989 uu____4990
             else FStar_Tactics_Types.goal_env goal  in
           let uu____4993 = __tc env t  in
           bind uu____4993
             (fun uu____5012  ->
                match uu____5012 with
                | (t1,typ,guard) ->
                    mlog
                      (fun uu____5027  ->
                         let uu____5028 =
                           FStar_Syntax_Print.term_to_string typ  in
                         let uu____5030 =
                           let uu____5032 = FStar_Tactics_Types.goal_env goal
                              in
                           FStar_TypeChecker_Rel.guard_to_string uu____5032
                             guard
                            in
                         FStar_Util.print2
                           "__exact_now: got type %s\n__exact_now: and guard %s\n"
                           uu____5028 uu____5030)
                      (fun uu____5036  ->
                         let uu____5037 =
                           let uu____5040 = FStar_Tactics_Types.goal_env goal
                              in
                           proc_guard "__exact typing" uu____5040 guard  in
                         bind uu____5037
                           (fun uu____5043  ->
                              mlog
                                (fun uu____5047  ->
                                   let uu____5048 =
                                     FStar_Syntax_Print.term_to_string typ
                                      in
                                   let uu____5050 =
                                     let uu____5052 =
                                       FStar_Tactics_Types.goal_type goal  in
                                     FStar_Syntax_Print.term_to_string
                                       uu____5052
                                      in
                                   FStar_Util.print2
                                     "__exact_now: unifying %s and %s\n"
                                     uu____5048 uu____5050)
                                (fun uu____5056  ->
                                   let uu____5057 =
                                     let uu____5061 =
                                       FStar_Tactics_Types.goal_env goal  in
                                     let uu____5062 =
                                       FStar_Tactics_Types.goal_type goal  in
                                     do_unify uu____5061 typ uu____5062  in
                                   bind uu____5057
                                     (fun b  ->
                                        if b
                                        then solve goal t1
                                        else
                                          (let uu____5072 =
                                             let uu____5079 =
                                               let uu____5085 =
                                                 FStar_Tactics_Types.goal_env
                                                   goal
                                                  in
                                               tts uu____5085  in
                                             let uu____5086 =
                                               FStar_Tactics_Types.goal_type
                                                 goal
                                                in
                                             FStar_TypeChecker_Err.print_discrepancy
                                               uu____5079 typ uu____5086
                                              in
                                           match uu____5072 with
                                           | (typ1,goalt) ->
                                               let uu____5095 =
                                                 let uu____5097 =
                                                   FStar_Tactics_Types.goal_env
                                                     goal
                                                    in
                                                 tts uu____5097 t1  in
                                               let uu____5098 =
                                                 let uu____5100 =
                                                   FStar_Tactics_Types.goal_env
                                                     goal
                                                    in
                                                 let uu____5101 =
                                                   FStar_Tactics_Types.goal_witness
                                                     goal
                                                    in
                                                 tts uu____5100 uu____5101
                                                  in
                                               fail4
                                                 "%s : %s does not exactly solve the goal %s (witness = %s)"
                                                 uu____5095 typ1 goalt
                                                 uu____5098)))))))
  
let (t_exact :
  Prims.bool -> Prims.bool -> FStar_Syntax_Syntax.term -> unit tac) =
  fun try_refine  ->
    fun set_expected_typ1  ->
      fun tm  ->
        let uu____5127 =
          mlog
            (fun uu____5132  ->
               let uu____5133 = FStar_Syntax_Print.term_to_string tm  in
               FStar_Util.print1 "t_exact: tm = %s\n" uu____5133)
            (fun uu____5138  ->
               let uu____5139 =
                 let uu____5146 = __exact_now set_expected_typ1 tm  in
                 catch uu____5146  in
               bind uu____5139
                 (fun uu___2_5155  ->
                    match uu___2_5155 with
                    | FStar_Util.Inr r -> ret ()
                    | FStar_Util.Inl e when Prims.op_Negation try_refine ->
                        traise e
                    | FStar_Util.Inl e ->
                        mlog
                          (fun uu____5166  ->
                             FStar_Util.print_string
                               "__exact_now failed, trying refine...\n")
                          (fun uu____5170  ->
                             let uu____5171 =
                               let uu____5178 =
                                 let uu____5181 =
                                   norm [FStar_Syntax_Embeddings.Delta]  in
                                 bind uu____5181
                                   (fun uu____5186  ->
                                      let uu____5187 = refine_intro ()  in
                                      bind uu____5187
                                        (fun uu____5191  ->
                                           __exact_now set_expected_typ1 tm))
                                  in
                               catch uu____5178  in
                             bind uu____5171
                               (fun uu___1_5198  ->
                                  match uu___1_5198 with
                                  | FStar_Util.Inr r ->
                                      mlog
                                        (fun uu____5207  ->
                                           FStar_Util.print_string
                                             "__exact_now: failed after refining too\n")
                                        (fun uu____5210  -> ret ())
                                  | FStar_Util.Inl uu____5211 ->
                                      mlog
                                        (fun uu____5213  ->
                                           FStar_Util.print_string
                                             "__exact_now: was not a refinement\n")
                                        (fun uu____5216  -> traise e)))))
           in
        FStar_All.pipe_left (wrap_err "exact") uu____5127
  
let rec mapM : 'a 'b . ('a -> 'b tac) -> 'a Prims.list -> 'b Prims.list tac =
  fun f  ->
    fun l  ->
      match l with
      | [] -> ret []
      | x::xs ->
          let uu____5268 = f x  in
          bind uu____5268
            (fun y  ->
               let uu____5276 = mapM f xs  in
               bind uu____5276 (fun ys  -> ret (y :: ys)))
  
let rec (__try_unify_by_application :
  Prims.bool ->
    (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.aqual *
      FStar_Syntax_Syntax.ctx_uvar) Prims.list ->
      env ->
        FStar_Syntax_Syntax.term ->
          FStar_Syntax_Syntax.term ->
            (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.aqual *
              FStar_Syntax_Syntax.ctx_uvar) Prims.list tac)
  =
  fun only_match  ->
    fun acc  ->
      fun e  ->
        fun ty1  ->
          fun ty2  ->
            let f = if only_match then do_match else do_unify  in
            let uu____5386 = f e ty2 ty1  in
            bind uu____5386
              (fun uu___3_5400  ->
                 if uu___3_5400
                 then ret acc
                 else
                   (let uu____5420 = FStar_Syntax_Util.arrow_one ty1  in
                    match uu____5420 with
                    | FStar_Pervasives_Native.None  ->
                        let uu____5441 =
                          FStar_Syntax_Print.term_to_string ty1  in
                        let uu____5443 =
                          FStar_Syntax_Print.term_to_string ty2  in
                        fail2 "Could not instantiate, %s to %s" uu____5441
                          uu____5443
                    | FStar_Pervasives_Native.Some (b,c) ->
                        let uu____5460 =
                          let uu____5462 = FStar_Syntax_Util.is_total_comp c
                             in
                          Prims.op_Negation uu____5462  in
                        if uu____5460
                        then fail "Codomain is effectful"
                        else
                          (let uu____5486 =
                             new_uvar "apply arg" e
                               (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                              in
                           bind uu____5486
                             (fun uu____5513  ->
                                match uu____5513 with
                                | (uvt,uv) ->
                                    let typ = FStar_Syntax_Util.comp_result c
                                       in
                                    let typ' =
                                      FStar_Syntax_Subst.subst
                                        [FStar_Syntax_Syntax.NT
                                           ((FStar_Pervasives_Native.fst b),
                                             uvt)] typ
                                       in
                                    __try_unify_by_application only_match
                                      ((uvt, (FStar_Pervasives_Native.snd b),
                                         uv) :: acc) e typ' ty2))))
  
let (try_unify_by_application :
  Prims.bool ->
    env ->
      FStar_Syntax_Syntax.term ->
        FStar_Syntax_Syntax.term ->
          (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.aqual *
            FStar_Syntax_Syntax.ctx_uvar) Prims.list tac)
  =
  fun only_match  ->
    fun e  ->
      fun ty1  ->
        fun ty2  -> __try_unify_by_application only_match [] e ty1 ty2
  
let (t_apply :
  Prims.bool -> Prims.bool -> FStar_Syntax_Syntax.term -> unit tac) =
  fun uopt  ->
    fun only_match  ->
      fun tm  ->
        let uu____5619 =
          mlog
            (fun uu____5624  ->
               let uu____5625 = FStar_Syntax_Print.term_to_string tm  in
               FStar_Util.print1 "t_apply: tm = %s\n" uu____5625)
            (fun uu____5630  ->
               let uu____5631 = cur_goal ()  in
               bind uu____5631
                 (fun goal  ->
                    let e = FStar_Tactics_Types.goal_env goal  in
                    let uu____5639 = __tc e tm  in
                    bind uu____5639
                      (fun uu____5660  ->
                         match uu____5660 with
                         | (tm1,typ,guard) ->
                             let typ1 = bnorm e typ  in
                             let uu____5673 =
                               let uu____5684 =
                                 FStar_Tactics_Types.goal_type goal  in
                               try_unify_by_application only_match e typ1
                                 uu____5684
                                in
                             bind uu____5673
                               (fun uvs  ->
                                  mlog
                                    (fun uu____5705  ->
                                       let uu____5706 =
                                         FStar_Common.string_of_list
                                           (fun uu____5718  ->
                                              match uu____5718 with
                                              | (t,uu____5727,uu____5728) ->
                                                  FStar_Syntax_Print.term_to_string
                                                    t) uvs
                                          in
                                       FStar_Util.print1
                                         "t_apply: found args = %s\n"
                                         uu____5706)
                                    (fun uu____5736  ->
                                       let fix_qual q =
                                         match q with
                                         | FStar_Pervasives_Native.Some
                                             (FStar_Syntax_Syntax.Meta
                                             uu____5751) ->
                                             FStar_Pervasives_Native.Some
                                               (FStar_Syntax_Syntax.Implicit
                                                  false)
                                         | uu____5755 -> q  in
                                       let w =
                                         FStar_List.fold_right
                                           (fun uu____5778  ->
                                              fun w  ->
                                                match uu____5778 with
                                                | (uvt,q,uu____5796) ->
                                                    FStar_Syntax_Util.mk_app
                                                      w [(uvt, (fix_qual q))])
                                           uvs tm1
                                          in
                                       let uvset =
                                         let uu____5828 =
                                           FStar_Syntax_Free.new_uv_set ()
                                            in
                                         FStar_List.fold_right
                                           (fun uu____5845  ->
                                              fun s  ->
                                                match uu____5845 with
                                                | (uu____5857,uu____5858,uv)
                                                    ->
                                                    let uu____5860 =
                                                      FStar_Syntax_Free.uvars
                                                        uv.FStar_Syntax_Syntax.ctx_uvar_typ
                                                       in
                                                    FStar_Util.set_union s
                                                      uu____5860) uvs
                                           uu____5828
                                          in
                                       let free_in_some_goal uv =
                                         FStar_Util.set_mem uv uvset  in
                                       let uu____5870 = solve' goal w  in
                                       bind uu____5870
                                         (fun uu____5875  ->
                                            let uu____5876 =
                                              mapM
                                                (fun uu____5893  ->
                                                   match uu____5893 with
                                                   | (uvt,q,uv) ->
                                                       let uu____5905 =
                                                         FStar_Syntax_Unionfind.find
                                                           uv.FStar_Syntax_Syntax.ctx_uvar_head
                                                          in
                                                       (match uu____5905 with
                                                        | FStar_Pervasives_Native.Some
                                                            uu____5910 ->
                                                            ret ()
                                                        | FStar_Pervasives_Native.None
                                                             ->
                                                            let uu____5911 =
                                                              uopt &&
                                                                (free_in_some_goal
                                                                   uv)
                                                               in
                                                            if uu____5911
                                                            then ret ()
                                                            else
                                                              (let uu____5918
                                                                 =
                                                                 let uu____5921
                                                                   =
                                                                   bnorm_goal
                                                                    (let uu___898_5924
                                                                    = goal
                                                                     in
                                                                    {
                                                                    FStar_Tactics_Types.goal_main_env
                                                                    =
                                                                    (uu___898_5924.FStar_Tactics_Types.goal_main_env);
                                                                    FStar_Tactics_Types.goal_ctx_uvar
                                                                    = uv;
                                                                    FStar_Tactics_Types.opts
                                                                    =
                                                                    (uu___898_5924.FStar_Tactics_Types.opts);
                                                                    FStar_Tactics_Types.is_guard
                                                                    = false;
                                                                    FStar_Tactics_Types.label
                                                                    =
                                                                    (uu___898_5924.FStar_Tactics_Types.label)
                                                                    })
                                                                    in
                                                                 [uu____5921]
                                                                  in
                                                               add_goals
                                                                 uu____5918)))
                                                uvs
                                               in
                                            bind uu____5876
                                              (fun uu____5929  ->
                                                 proc_guard "apply guard" e
                                                   guard)))))))
           in
        FStar_All.pipe_left (wrap_err "apply") uu____5619
  
let (lemma_or_sq :
  FStar_Syntax_Syntax.comp ->
    (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.option)
  =
  fun c  ->
    let ct = FStar_Syntax_Util.comp_to_comp_typ_nouniv c  in
    let uu____5957 =
      FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
        FStar_Parser_Const.effect_Lemma_lid
       in
    if uu____5957
    then
      let uu____5966 =
        match ct.FStar_Syntax_Syntax.effect_args with
        | pre::post::uu____5981 ->
            ((FStar_Pervasives_Native.fst pre),
              (FStar_Pervasives_Native.fst post))
        | uu____6034 -> failwith "apply_lemma: impossible: not a lemma"  in
      match uu____5966 with
      | (pre,post) ->
          let post1 =
            let uu____6067 =
              let uu____6078 =
                FStar_Syntax_Syntax.as_arg FStar_Syntax_Util.exp_unit  in
              [uu____6078]  in
            FStar_Syntax_Util.mk_app post uu____6067  in
          FStar_Pervasives_Native.Some (pre, post1)
    else
      (let uu____6109 =
         FStar_Syntax_Util.is_pure_effect ct.FStar_Syntax_Syntax.effect_name
          in
       if uu____6109
       then
         let uu____6118 =
           FStar_Syntax_Util.un_squash ct.FStar_Syntax_Syntax.result_typ  in
         FStar_Util.map_opt uu____6118
           (fun post  -> (FStar_Syntax_Util.t_true, post))
       else FStar_Pervasives_Native.None)
  
let rec fold_left :
  'a 'b . ('a -> 'b -> 'b tac) -> 'b -> 'a Prims.list -> 'b tac =
  fun f  ->
    fun e  ->
      fun xs  ->
        match xs with
        | [] -> ret e
        | x::xs1 ->
            let uu____6197 = f x e  in
            bind uu____6197 (fun e'  -> fold_left f e' xs1)
  
let (apply_lemma : FStar_Syntax_Syntax.term -> unit tac) =
  fun tm  ->
    let uu____6212 =
      let uu____6215 =
        bind get
          (fun ps  ->
             mlog
               (fun uu____6222  ->
                  let uu____6223 = FStar_Syntax_Print.term_to_string tm  in
                  FStar_Util.print1 "apply_lemma: tm = %s\n" uu____6223)
               (fun uu____6229  ->
                  let is_unit_t t =
                    let uu____6237 =
                      let uu____6238 = FStar_Syntax_Subst.compress t  in
                      uu____6238.FStar_Syntax_Syntax.n  in
                    match uu____6237 with
                    | FStar_Syntax_Syntax.Tm_fvar fv when
                        FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.unit_lid
                        -> true
                    | uu____6244 -> false  in
                  let uu____6246 = cur_goal ()  in
                  bind uu____6246
                    (fun goal  ->
                       let uu____6252 =
                         let uu____6261 = FStar_Tactics_Types.goal_env goal
                            in
                         __tc uu____6261 tm  in
                       bind uu____6252
                         (fun uu____6276  ->
                            match uu____6276 with
                            | (tm1,t,guard) ->
                                let uu____6288 =
                                  FStar_Syntax_Util.arrow_formals_comp t  in
                                (match uu____6288 with
                                 | (bs,comp) ->
                                     let uu____6321 = lemma_or_sq comp  in
                                     (match uu____6321 with
                                      | FStar_Pervasives_Native.None  ->
                                          fail
                                            "not a lemma or squashed function"
                                      | FStar_Pervasives_Native.Some
                                          (pre,post) ->
                                          let uu____6341 =
                                            fold_left
                                              (fun uu____6403  ->
                                                 fun uu____6404  ->
                                                   match (uu____6403,
                                                           uu____6404)
                                                   with
                                                   | ((b,aq),(uvs,imps,subst1))
                                                       ->
                                                       let b_t =
                                                         FStar_Syntax_Subst.subst
                                                           subst1
                                                           b.FStar_Syntax_Syntax.sort
                                                          in
                                                       let uu____6555 =
                                                         is_unit_t b_t  in
                                                       if uu____6555
                                                       then
                                                         FStar_All.pipe_left
                                                           ret
                                                           (((FStar_Syntax_Util.exp_unit,
                                                               aq) :: uvs),
                                                             imps,
                                                             ((FStar_Syntax_Syntax.NT
                                                                 (b,
                                                                   FStar_Syntax_Util.exp_unit))
                                                             :: subst1))
                                                       else
                                                         (let uu____6678 =
                                                            let uu____6685 =
                                                              FStar_Tactics_Types.goal_env
                                                                goal
                                                               in
                                                            new_uvar
                                                              "apply_lemma"
                                                              uu____6685 b_t
                                                             in
                                                          bind uu____6678
                                                            (fun uu____6716 
                                                               ->
                                                               match uu____6716
                                                               with
                                                               | (t1,u) ->
                                                                   FStar_All.pipe_left
                                                                    ret
                                                                    (((t1,
                                                                    aq) ::
                                                                    uvs),
                                                                    ((t1, u)
                                                                    :: imps),
                                                                    ((FStar_Syntax_Syntax.NT
                                                                    (b, t1))
                                                                    ::
                                                                    subst1)))))
                                              ([], [], []) bs
                                             in
                                          bind uu____6341
                                            (fun uu____6902  ->
                                               match uu____6902 with
                                               | (uvs,implicits,subst1) ->
                                                   let implicits1 =
                                                     FStar_List.rev implicits
                                                      in
                                                   let uvs1 =
                                                     FStar_List.rev uvs  in
                                                   let pre1 =
                                                     FStar_Syntax_Subst.subst
                                                       subst1 pre
                                                      in
                                                   let post1 =
                                                     FStar_Syntax_Subst.subst
                                                       subst1 post
                                                      in
                                                   let uu____6990 =
                                                     let uu____6994 =
                                                       FStar_Tactics_Types.goal_env
                                                         goal
                                                        in
                                                     let uu____6995 =
                                                       FStar_Syntax_Util.mk_squash
                                                         FStar_Syntax_Syntax.U_zero
                                                         post1
                                                        in
                                                     let uu____6996 =
                                                       FStar_Tactics_Types.goal_type
                                                         goal
                                                        in
                                                     do_unify uu____6994
                                                       uu____6995 uu____6996
                                                      in
                                                   bind uu____6990
                                                     (fun b  ->
                                                        if
                                                          Prims.op_Negation b
                                                        then
                                                          let uu____7008 =
                                                            let uu____7015 =
                                                              let uu____7021
                                                                =
                                                                FStar_Tactics_Types.goal_env
                                                                  goal
                                                                 in
                                                              tts uu____7021
                                                               in
                                                            let uu____7022 =
                                                              FStar_Syntax_Util.mk_squash
                                                                FStar_Syntax_Syntax.U_zero
                                                                post1
                                                               in
                                                            let uu____7023 =
                                                              FStar_Tactics_Types.goal_type
                                                                goal
                                                               in
                                                            FStar_TypeChecker_Err.print_discrepancy
                                                              uu____7015
                                                              uu____7022
                                                              uu____7023
                                                             in
                                                          match uu____7008
                                                          with
                                                          | (post2,goalt) ->
                                                              let uu____7032
                                                                =
                                                                let uu____7034
                                                                  =
                                                                  FStar_Tactics_Types.goal_env
                                                                    goal
                                                                   in
                                                                tts
                                                                  uu____7034
                                                                  tm1
                                                                 in
                                                              fail3
                                                                "Cannot instantiate lemma %s (with postcondition: %s) to match goal (%s)"
                                                                uu____7032
                                                                post2 goalt
                                                        else
                                                          (let uu____7038 =
                                                             solve' goal
                                                               FStar_Syntax_Util.exp_unit
                                                              in
                                                           bind uu____7038
                                                             (fun uu____7046 
                                                                ->
                                                                let is_free_uvar
                                                                  uv t1 =
                                                                  let free_uvars
                                                                    =
                                                                    let uu____7072
                                                                    =
                                                                    let uu____7075
                                                                    =
                                                                    FStar_Syntax_Free.uvars
                                                                    t1  in
                                                                    FStar_Util.set_elements
                                                                    uu____7075
                                                                     in
                                                                    FStar_List.map
                                                                    (fun x 
                                                                    ->
                                                                    x.FStar_Syntax_Syntax.ctx_uvar_head)
                                                                    uu____7072
                                                                     in
                                                                  FStar_List.existsML
                                                                    (
                                                                    fun u  ->
                                                                    FStar_Syntax_Unionfind.equiv
                                                                    u uv)
                                                                    free_uvars
                                                                   in
                                                                let appears
                                                                  uv goals =
                                                                  FStar_List.existsML
                                                                    (
                                                                    fun g' 
                                                                    ->
                                                                    let uu____7111
                                                                    =
                                                                    FStar_Tactics_Types.goal_type
                                                                    g'  in
                                                                    is_free_uvar
                                                                    uv
                                                                    uu____7111)
                                                                    goals
                                                                   in
                                                                let checkone
                                                                  t1 goals =
                                                                  let uu____7128
                                                                    =
                                                                    FStar_Syntax_Util.head_and_args
                                                                    t1  in
                                                                  match uu____7128
                                                                  with
                                                                  | (hd1,uu____7147)
                                                                    ->
                                                                    (match 
                                                                    hd1.FStar_Syntax_Syntax.n
                                                                    with
                                                                    | 
                                                                    FStar_Syntax_Syntax.Tm_uvar
                                                                    (uv,uu____7174)
                                                                    ->
                                                                    appears
                                                                    uv.FStar_Syntax_Syntax.ctx_uvar_head
                                                                    goals
                                                                    | 
                                                                    uu____7191
                                                                    -> false)
                                                                   in
                                                                let uu____7193
                                                                  =
                                                                  FStar_All.pipe_right
                                                                    implicits1
                                                                    (
                                                                    mapM
                                                                    (fun imp 
                                                                    ->
                                                                    let t1 =
                                                                    FStar_Util.now
                                                                    ()  in
                                                                    let uu____7236
                                                                    = imp  in
                                                                    match uu____7236
                                                                    with
                                                                    | 
                                                                    (term,ctx_uvar)
                                                                    ->
                                                                    let uu____7247
                                                                    =
                                                                    FStar_Syntax_Util.head_and_args
                                                                    term  in
                                                                    (match uu____7247
                                                                    with
                                                                    | 
                                                                    (hd1,uu____7269)
                                                                    ->
                                                                    let uu____7294
                                                                    =
                                                                    let uu____7295
                                                                    =
                                                                    FStar_Syntax_Subst.compress
                                                                    hd1  in
                                                                    uu____7295.FStar_Syntax_Syntax.n
                                                                     in
                                                                    (match uu____7294
                                                                    with
                                                                    | 
                                                                    FStar_Syntax_Syntax.Tm_uvar
                                                                    (ctx_uvar1,uu____7303)
                                                                    ->
                                                                    let goal1
                                                                    =
                                                                    bnorm_goal
                                                                    (let uu___1016_7323
                                                                    = goal
                                                                     in
                                                                    {
                                                                    FStar_Tactics_Types.goal_main_env
                                                                    =
                                                                    (uu___1016_7323.FStar_Tactics_Types.goal_main_env);
                                                                    FStar_Tactics_Types.goal_ctx_uvar
                                                                    =
                                                                    ctx_uvar1;
                                                                    FStar_Tactics_Types.opts
                                                                    =
                                                                    (uu___1016_7323.FStar_Tactics_Types.opts);
                                                                    FStar_Tactics_Types.is_guard
                                                                    =
                                                                    (uu___1016_7323.FStar_Tactics_Types.is_guard);
                                                                    FStar_Tactics_Types.label
                                                                    =
                                                                    (uu___1016_7323.FStar_Tactics_Types.label)
                                                                    })  in
                                                                    ret
                                                                    [goal1]
                                                                    | 
                                                                    uu____7326
                                                                    ->
                                                                    mlog
                                                                    (fun
                                                                    uu____7332
                                                                     ->
                                                                    let uu____7333
                                                                    =
                                                                    FStar_Syntax_Print.uvar_to_string
                                                                    ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_head
                                                                     in
                                                                    let uu____7335
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    term  in
                                                                    FStar_Util.print2
                                                                    "apply_lemma: arg %s unified to (%s)\n"
                                                                    uu____7333
                                                                    uu____7335)
                                                                    (fun
                                                                    uu____7342
                                                                     ->
                                                                    let env =
                                                                    let uu___1021_7344
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    goal  in
                                                                    {
                                                                    FStar_TypeChecker_Env.solver
                                                                    =
                                                                    (uu___1021_7344.FStar_TypeChecker_Env.solver);
                                                                    FStar_TypeChecker_Env.range
                                                                    =
                                                                    (uu___1021_7344.FStar_TypeChecker_Env.range);
                                                                    FStar_TypeChecker_Env.curmodule
                                                                    =
                                                                    (uu___1021_7344.FStar_TypeChecker_Env.curmodule);
                                                                    FStar_TypeChecker_Env.gamma
                                                                    =
                                                                    (ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_gamma);
                                                                    FStar_TypeChecker_Env.gamma_sig
                                                                    =
                                                                    (uu___1021_7344.FStar_TypeChecker_Env.gamma_sig);
                                                                    FStar_TypeChecker_Env.gamma_cache
                                                                    =
                                                                    (uu___1021_7344.FStar_TypeChecker_Env.gamma_cache);
                                                                    FStar_TypeChecker_Env.modules
                                                                    =
                                                                    (uu___1021_7344.FStar_TypeChecker_Env.modules);
                                                                    FStar_TypeChecker_Env.expected_typ
                                                                    =
                                                                    (uu___1021_7344.FStar_TypeChecker_Env.expected_typ);
                                                                    FStar_TypeChecker_Env.sigtab
                                                                    =
                                                                    (uu___1021_7344.FStar_TypeChecker_Env.sigtab);
                                                                    FStar_TypeChecker_Env.attrtab
                                                                    =
                                                                    (uu___1021_7344.FStar_TypeChecker_Env.attrtab);
                                                                    FStar_TypeChecker_Env.instantiate_imp
                                                                    =
                                                                    (uu___1021_7344.FStar_TypeChecker_Env.instantiate_imp);
                                                                    FStar_TypeChecker_Env.effects
                                                                    =
                                                                    (uu___1021_7344.FStar_TypeChecker_Env.effects);
                                                                    FStar_TypeChecker_Env.generalize
                                                                    =
                                                                    (uu___1021_7344.FStar_TypeChecker_Env.generalize);
                                                                    FStar_TypeChecker_Env.letrecs
                                                                    =
                                                                    (uu___1021_7344.FStar_TypeChecker_Env.letrecs);
                                                                    FStar_TypeChecker_Env.top_level
                                                                    =
                                                                    (uu___1021_7344.FStar_TypeChecker_Env.top_level);
                                                                    FStar_TypeChecker_Env.check_uvars
                                                                    =
                                                                    (uu___1021_7344.FStar_TypeChecker_Env.check_uvars);
                                                                    FStar_TypeChecker_Env.use_eq
                                                                    =
                                                                    (uu___1021_7344.FStar_TypeChecker_Env.use_eq);
                                                                    FStar_TypeChecker_Env.use_eq_strict
                                                                    =
                                                                    (uu___1021_7344.FStar_TypeChecker_Env.use_eq_strict);
                                                                    FStar_TypeChecker_Env.is_iface
                                                                    =
                                                                    (uu___1021_7344.FStar_TypeChecker_Env.is_iface);
                                                                    FStar_TypeChecker_Env.admit
                                                                    =
                                                                    (uu___1021_7344.FStar_TypeChecker_Env.admit);
                                                                    FStar_TypeChecker_Env.lax
                                                                    =
                                                                    (uu___1021_7344.FStar_TypeChecker_Env.lax);
                                                                    FStar_TypeChecker_Env.lax_universes
                                                                    =
                                                                    (uu___1021_7344.FStar_TypeChecker_Env.lax_universes);
                                                                    FStar_TypeChecker_Env.phase1
                                                                    =
                                                                    (uu___1021_7344.FStar_TypeChecker_Env.phase1);
                                                                    FStar_TypeChecker_Env.failhard
                                                                    =
                                                                    (uu___1021_7344.FStar_TypeChecker_Env.failhard);
                                                                    FStar_TypeChecker_Env.nosynth
                                                                    =
                                                                    (uu___1021_7344.FStar_TypeChecker_Env.nosynth);
                                                                    FStar_TypeChecker_Env.uvar_subtyping
                                                                    =
                                                                    (uu___1021_7344.FStar_TypeChecker_Env.uvar_subtyping);
                                                                    FStar_TypeChecker_Env.tc_term
                                                                    =
                                                                    (uu___1021_7344.FStar_TypeChecker_Env.tc_term);
                                                                    FStar_TypeChecker_Env.type_of
                                                                    =
                                                                    (uu___1021_7344.FStar_TypeChecker_Env.type_of);
                                                                    FStar_TypeChecker_Env.universe_of
                                                                    =
                                                                    (uu___1021_7344.FStar_TypeChecker_Env.universe_of);
                                                                    FStar_TypeChecker_Env.check_type_of
                                                                    =
                                                                    (uu___1021_7344.FStar_TypeChecker_Env.check_type_of);
                                                                    FStar_TypeChecker_Env.use_bv_sorts
                                                                    =
                                                                    (uu___1021_7344.FStar_TypeChecker_Env.use_bv_sorts);
                                                                    FStar_TypeChecker_Env.qtbl_name_and_index
                                                                    =
                                                                    (uu___1021_7344.FStar_TypeChecker_Env.qtbl_name_and_index);
                                                                    FStar_TypeChecker_Env.normalized_eff_names
                                                                    =
                                                                    (uu___1021_7344.FStar_TypeChecker_Env.normalized_eff_names);
                                                                    FStar_TypeChecker_Env.fv_delta_depths
                                                                    =
                                                                    (uu___1021_7344.FStar_TypeChecker_Env.fv_delta_depths);
                                                                    FStar_TypeChecker_Env.proof_ns
                                                                    =
                                                                    (uu___1021_7344.FStar_TypeChecker_Env.proof_ns);
                                                                    FStar_TypeChecker_Env.synth_hook
                                                                    =
                                                                    (uu___1021_7344.FStar_TypeChecker_Env.synth_hook);
                                                                    FStar_TypeChecker_Env.try_solve_implicits_hook
                                                                    =
                                                                    (uu___1021_7344.FStar_TypeChecker_Env.try_solve_implicits_hook);
                                                                    FStar_TypeChecker_Env.splice
                                                                    =
                                                                    (uu___1021_7344.FStar_TypeChecker_Env.splice);
                                                                    FStar_TypeChecker_Env.mpreprocess
                                                                    =
                                                                    (uu___1021_7344.FStar_TypeChecker_Env.mpreprocess);
                                                                    FStar_TypeChecker_Env.postprocess
                                                                    =
                                                                    (uu___1021_7344.FStar_TypeChecker_Env.postprocess);
                                                                    FStar_TypeChecker_Env.is_native_tactic
                                                                    =
                                                                    (uu___1021_7344.FStar_TypeChecker_Env.is_native_tactic);
                                                                    FStar_TypeChecker_Env.identifier_info
                                                                    =
                                                                    (uu___1021_7344.FStar_TypeChecker_Env.identifier_info);
                                                                    FStar_TypeChecker_Env.tc_hooks
                                                                    =
                                                                    (uu___1021_7344.FStar_TypeChecker_Env.tc_hooks);
                                                                    FStar_TypeChecker_Env.dsenv
                                                                    =
                                                                    (uu___1021_7344.FStar_TypeChecker_Env.dsenv);
                                                                    FStar_TypeChecker_Env.nbe
                                                                    =
                                                                    (uu___1021_7344.FStar_TypeChecker_Env.nbe);
                                                                    FStar_TypeChecker_Env.strict_args_tab
                                                                    =
                                                                    (uu___1021_7344.FStar_TypeChecker_Env.strict_args_tab);
                                                                    FStar_TypeChecker_Env.erasable_types_tab
                                                                    =
                                                                    (uu___1021_7344.FStar_TypeChecker_Env.erasable_types_tab)
                                                                    }  in
                                                                    let g_typ
                                                                    =
                                                                    FStar_TypeChecker_TcTerm.check_type_of_well_typed_term'
                                                                    true env
                                                                    term
                                                                    ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_typ
                                                                     in
                                                                    let uu____7347
                                                                    =
                                                                    let uu____7350
                                                                    =
                                                                    if
                                                                    ps.FStar_Tactics_Types.tac_verb_dbg
                                                                    then
                                                                    let uu____7354
                                                                    =
                                                                    FStar_Syntax_Print.ctx_uvar_to_string
                                                                    ctx_uvar
                                                                     in
                                                                    let uu____7356
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    term  in
                                                                    FStar_Util.format2
                                                                    "apply_lemma solved arg %s to %s\n"
                                                                    uu____7354
                                                                    uu____7356
                                                                    else
                                                                    "apply_lemma solved arg"
                                                                     in
                                                                    let uu____7362
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    goal  in
                                                                    proc_guard
                                                                    uu____7350
                                                                    uu____7362
                                                                    g_typ  in
                                                                    bind
                                                                    uu____7347
                                                                    (fun
                                                                    uu____7366
                                                                     ->
                                                                    ret []))))))
                                                                   in
                                                                bind
                                                                  uu____7193
                                                                  (fun
                                                                    sub_goals
                                                                     ->
                                                                    let sub_goals1
                                                                    =
                                                                    FStar_List.flatten
                                                                    sub_goals
                                                                     in
                                                                    let rec filter'
                                                                    f xs =
                                                                    match xs
                                                                    with
                                                                    | 
                                                                    [] -> []
                                                                    | 
                                                                    x::xs1 ->
                                                                    let uu____7430
                                                                    = f x xs1
                                                                     in
                                                                    if
                                                                    uu____7430
                                                                    then
                                                                    let uu____7435
                                                                    =
                                                                    filter' f
                                                                    xs1  in x
                                                                    ::
                                                                    uu____7435
                                                                    else
                                                                    filter' f
                                                                    xs1  in
                                                                    let sub_goals2
                                                                    =
                                                                    filter'
                                                                    (fun g 
                                                                    ->
                                                                    fun goals
                                                                     ->
                                                                    let uu____7450
                                                                    =
                                                                    let uu____7452
                                                                    =
                                                                    FStar_Tactics_Types.goal_witness
                                                                    g  in
                                                                    checkone
                                                                    uu____7452
                                                                    goals  in
                                                                    Prims.op_Negation
                                                                    uu____7450)
                                                                    sub_goals1
                                                                     in
                                                                    let uu____7453
                                                                    =
                                                                    let uu____7456
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    goal  in
                                                                    proc_guard
                                                                    "apply_lemma guard"
                                                                    uu____7456
                                                                    guard  in
                                                                    bind
                                                                    uu____7453
                                                                    (fun
                                                                    uu____7460
                                                                     ->
                                                                    let uu____7461
                                                                    =
                                                                    let uu____7464
                                                                    =
                                                                    let uu____7466
                                                                    =
                                                                    let uu____7468
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    goal  in
                                                                    let uu____7469
                                                                    =
                                                                    FStar_Syntax_Util.mk_squash
                                                                    FStar_Syntax_Syntax.U_zero
                                                                    pre1  in
                                                                    istrivial
                                                                    uu____7468
                                                                    uu____7469
                                                                     in
                                                                    Prims.op_Negation
                                                                    uu____7466
                                                                     in
                                                                    if
                                                                    uu____7464
                                                                    then
                                                                    let uu____7473
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    goal  in
                                                                    add_irrelevant_goal
                                                                    "apply_lemma precondition"
                                                                    uu____7473
                                                                    pre1
                                                                    goal.FStar_Tactics_Types.opts
                                                                    goal.FStar_Tactics_Types.label
                                                                    else
                                                                    ret ()
                                                                     in
                                                                    bind
                                                                    uu____7461
                                                                    (fun
                                                                    uu____7478
                                                                     ->
                                                                    add_goals
                                                                    sub_goals2)))))))))))))
         in
      focus uu____6215  in
    FStar_All.pipe_left (wrap_err "apply_lemma") uu____6212
  
let (destruct_eq' :
  FStar_Reflection_Data.typ ->
    (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.option)
  =
  fun typ  ->
    let uu____7502 = FStar_Syntax_Util.destruct_typ_as_formula typ  in
    match uu____7502 with
    | FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn
        (l,uu____7512::(e1,FStar_Pervasives_Native.None )::(e2,FStar_Pervasives_Native.None
                                                            )::[]))
        when
        (FStar_Ident.lid_equals l FStar_Parser_Const.eq2_lid) ||
          (FStar_Ident.lid_equals l FStar_Parser_Const.c_eq2_lid)
        -> FStar_Pervasives_Native.Some (e1, e2)
    | FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn
        (l,uu____7572::uu____7573::(e1,uu____7575)::(e2,uu____7577)::[]))
        when FStar_Ident.lid_equals l FStar_Parser_Const.eq3_lid ->
        FStar_Pervasives_Native.Some (e1, e2)
    | uu____7654 ->
        let uu____7657 = FStar_Syntax_Util.unb2t typ  in
        (match uu____7657 with
         | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
         | FStar_Pervasives_Native.Some t ->
             let uu____7671 = FStar_Syntax_Util.head_and_args t  in
             (match uu____7671 with
              | (hd1,args) ->
                  let uu____7720 =
                    let uu____7735 =
                      let uu____7736 = FStar_Syntax_Subst.compress hd1  in
                      uu____7736.FStar_Syntax_Syntax.n  in
                    (uu____7735, args)  in
                  (match uu____7720 with
                   | (FStar_Syntax_Syntax.Tm_fvar
                      fv,(uu____7756,FStar_Pervasives_Native.Some
                          (FStar_Syntax_Syntax.Implicit uu____7757))::
                      (e1,FStar_Pervasives_Native.None )::(e2,FStar_Pervasives_Native.None
                                                           )::[])
                       when
                       FStar_Syntax_Syntax.fv_eq_lid fv
                         FStar_Parser_Const.op_Eq
                       -> FStar_Pervasives_Native.Some (e1, e2)
                   | uu____7825 -> FStar_Pervasives_Native.None)))
  
let (destruct_eq :
  FStar_Reflection_Data.typ ->
    (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.option)
  =
  fun typ  ->
    let uu____7862 = destruct_eq' typ  in
    match uu____7862 with
    | FStar_Pervasives_Native.Some t -> FStar_Pervasives_Native.Some t
    | FStar_Pervasives_Native.None  ->
        let uu____7892 = FStar_Syntax_Util.un_squash typ  in
        (match uu____7892 with
         | FStar_Pervasives_Native.Some typ1 -> destruct_eq' typ1
         | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None)
  
let (split_env :
  FStar_Syntax_Syntax.bv ->
    env ->
      (env * FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.bv Prims.list)
        FStar_Pervasives_Native.option)
  =
  fun bvar  ->
    fun e  ->
      let rec aux e1 =
        let uu____7961 = FStar_TypeChecker_Env.pop_bv e1  in
        match uu____7961 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (bv',e') ->
            if FStar_Syntax_Syntax.bv_eq bvar bv'
            then FStar_Pervasives_Native.Some (e', bv', [])
            else
              (let uu____8019 = aux e'  in
               FStar_Util.map_opt uu____8019
                 (fun uu____8050  ->
                    match uu____8050 with
                    | (e'',bv,bvs) -> (e'', bv, (bv' :: bvs))))
         in
      let uu____8076 = aux e  in
      FStar_Util.map_opt uu____8076
        (fun uu____8107  ->
           match uu____8107 with
           | (e',bv,bvs) -> (e', bv, (FStar_List.rev bvs)))
  
let (push_bvs :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.bv Prims.list -> FStar_TypeChecker_Env.env)
  =
  fun e  ->
    fun bvs  ->
      FStar_List.fold_left
        (fun e1  -> fun b  -> FStar_TypeChecker_Env.push_bv e1 b) e bvs
  
let (subst_goal :
  FStar_Syntax_Syntax.bv ->
    FStar_Syntax_Syntax.bv ->
      FStar_Syntax_Syntax.subst_elt Prims.list ->
        FStar_Tactics_Types.goal ->
          FStar_Tactics_Types.goal FStar_Pervasives_Native.option)
  =
  fun b1  ->
    fun b2  ->
      fun s  ->
        fun g  ->
          let uu____8181 =
            let uu____8192 = FStar_Tactics_Types.goal_env g  in
            split_env b1 uu____8192  in
          FStar_Util.map_opt uu____8181
            (fun uu____8210  ->
               match uu____8210 with
               | (e0,b11,bvs) ->
                   let s1 bv =
                     let uu___1129_8232 = bv  in
                     let uu____8233 =
                       FStar_Syntax_Subst.subst s bv.FStar_Syntax_Syntax.sort
                        in
                     {
                       FStar_Syntax_Syntax.ppname =
                         (uu___1129_8232.FStar_Syntax_Syntax.ppname);
                       FStar_Syntax_Syntax.index =
                         (uu___1129_8232.FStar_Syntax_Syntax.index);
                       FStar_Syntax_Syntax.sort = uu____8233
                     }  in
                   let bvs1 = FStar_List.map s1 bvs  in
                   let new_env = push_bvs e0 (b2 :: bvs1)  in
                   let new_goal =
                     let uu___1133_8241 = g.FStar_Tactics_Types.goal_ctx_uvar
                        in
                     let uu____8242 =
                       FStar_TypeChecker_Env.all_binders new_env  in
                     let uu____8251 =
                       let uu____8254 = FStar_Tactics_Types.goal_type g  in
                       FStar_Syntax_Subst.subst s uu____8254  in
                     {
                       FStar_Syntax_Syntax.ctx_uvar_head =
                         (uu___1133_8241.FStar_Syntax_Syntax.ctx_uvar_head);
                       FStar_Syntax_Syntax.ctx_uvar_gamma =
                         (new_env.FStar_TypeChecker_Env.gamma);
                       FStar_Syntax_Syntax.ctx_uvar_binders = uu____8242;
                       FStar_Syntax_Syntax.ctx_uvar_typ = uu____8251;
                       FStar_Syntax_Syntax.ctx_uvar_reason =
                         (uu___1133_8241.FStar_Syntax_Syntax.ctx_uvar_reason);
                       FStar_Syntax_Syntax.ctx_uvar_should_check =
                         (uu___1133_8241.FStar_Syntax_Syntax.ctx_uvar_should_check);
                       FStar_Syntax_Syntax.ctx_uvar_range =
                         (uu___1133_8241.FStar_Syntax_Syntax.ctx_uvar_range);
                       FStar_Syntax_Syntax.ctx_uvar_meta =
                         (uu___1133_8241.FStar_Syntax_Syntax.ctx_uvar_meta)
                     }  in
                   let uu___1136_8255 = g  in
                   {
                     FStar_Tactics_Types.goal_main_env =
                       (uu___1136_8255.FStar_Tactics_Types.goal_main_env);
                     FStar_Tactics_Types.goal_ctx_uvar = new_goal;
                     FStar_Tactics_Types.opts =
                       (uu___1136_8255.FStar_Tactics_Types.opts);
                     FStar_Tactics_Types.is_guard =
                       (uu___1136_8255.FStar_Tactics_Types.is_guard);
                     FStar_Tactics_Types.label =
                       (uu___1136_8255.FStar_Tactics_Types.label)
                   })
  
let (rewrite : FStar_Syntax_Syntax.binder -> unit tac) =
  fun h  ->
    let uu____8266 =
      let uu____8269 = cur_goal ()  in
      bind uu____8269
        (fun goal  ->
           let uu____8277 = h  in
           match uu____8277 with
           | (bv,uu____8281) ->
               mlog
                 (fun uu____8289  ->
                    let uu____8290 = FStar_Syntax_Print.bv_to_string bv  in
                    let uu____8292 =
                      FStar_Syntax_Print.term_to_string
                        bv.FStar_Syntax_Syntax.sort
                       in
                    FStar_Util.print2 "+++Rewrite %s : %s\n" uu____8290
                      uu____8292)
                 (fun uu____8297  ->
                    let uu____8298 =
                      let uu____8309 = FStar_Tactics_Types.goal_env goal  in
                      split_env bv uu____8309  in
                    match uu____8298 with
                    | FStar_Pervasives_Native.None  ->
                        fail "binder not found in environment"
                    | FStar_Pervasives_Native.Some (e0,bv1,bvs) ->
                        let uu____8336 =
                          destruct_eq bv1.FStar_Syntax_Syntax.sort  in
                        (match uu____8336 with
                         | FStar_Pervasives_Native.Some (x,e) ->
                             let uu____8351 =
                               let uu____8352 = FStar_Syntax_Subst.compress x
                                  in
                               uu____8352.FStar_Syntax_Syntax.n  in
                             (match uu____8351 with
                              | FStar_Syntax_Syntax.Tm_name x1 ->
                                  let s = [FStar_Syntax_Syntax.NT (x1, e)]
                                     in
                                  let s1 bv2 =
                                    let uu___1159_8369 = bv2  in
                                    let uu____8370 =
                                      FStar_Syntax_Subst.subst s
                                        bv2.FStar_Syntax_Syntax.sort
                                       in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___1159_8369.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___1159_8369.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = uu____8370
                                    }  in
                                  let bvs1 = FStar_List.map s1 bvs  in
                                  let new_env = push_bvs e0 (bv1 :: bvs1)  in
                                  let new_goal =
                                    let uu___1163_8378 =
                                      goal.FStar_Tactics_Types.goal_ctx_uvar
                                       in
                                    let uu____8379 =
                                      FStar_TypeChecker_Env.all_binders
                                        new_env
                                       in
                                    let uu____8388 =
                                      let uu____8391 =
                                        FStar_Tactics_Types.goal_type goal
                                         in
                                      FStar_Syntax_Subst.subst s uu____8391
                                       in
                                    {
                                      FStar_Syntax_Syntax.ctx_uvar_head =
                                        (uu___1163_8378.FStar_Syntax_Syntax.ctx_uvar_head);
                                      FStar_Syntax_Syntax.ctx_uvar_gamma =
                                        (new_env.FStar_TypeChecker_Env.gamma);
                                      FStar_Syntax_Syntax.ctx_uvar_binders =
                                        uu____8379;
                                      FStar_Syntax_Syntax.ctx_uvar_typ =
                                        uu____8388;
                                      FStar_Syntax_Syntax.ctx_uvar_reason =
                                        (uu___1163_8378.FStar_Syntax_Syntax.ctx_uvar_reason);
                                      FStar_Syntax_Syntax.ctx_uvar_should_check
                                        =
                                        (uu___1163_8378.FStar_Syntax_Syntax.ctx_uvar_should_check);
                                      FStar_Syntax_Syntax.ctx_uvar_range =
                                        (uu___1163_8378.FStar_Syntax_Syntax.ctx_uvar_range);
                                      FStar_Syntax_Syntax.ctx_uvar_meta =
                                        (uu___1163_8378.FStar_Syntax_Syntax.ctx_uvar_meta)
                                    }  in
                                  replace_cur
                                    (let uu___1166_8394 = goal  in
                                     {
                                       FStar_Tactics_Types.goal_main_env =
                                         (uu___1166_8394.FStar_Tactics_Types.goal_main_env);
                                       FStar_Tactics_Types.goal_ctx_uvar =
                                         new_goal;
                                       FStar_Tactics_Types.opts =
                                         (uu___1166_8394.FStar_Tactics_Types.opts);
                                       FStar_Tactics_Types.is_guard =
                                         (uu___1166_8394.FStar_Tactics_Types.is_guard);
                                       FStar_Tactics_Types.label =
                                         (uu___1166_8394.FStar_Tactics_Types.label)
                                     })
                              | uu____8395 ->
                                  fail
                                    "Not an equality hypothesis with a variable on the LHS")
                         | uu____8397 -> fail "Not an equality hypothesis")))
       in
    FStar_All.pipe_left (wrap_err "rewrite") uu____8266
  
let (rename_to : FStar_Syntax_Syntax.binder -> Prims.string -> unit tac) =
  fun b  ->
    fun s  ->
      let uu____8427 =
        let uu____8430 = cur_goal ()  in
        bind uu____8430
          (fun goal  ->
             let uu____8441 = b  in
             match uu____8441 with
             | (bv,uu____8445) ->
                 let bv' =
                   let uu____8451 =
                     let uu___1177_8452 = bv  in
                     let uu____8453 =
                       FStar_Ident.mk_ident
                         (s,
                           ((bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange))
                        in
                     {
                       FStar_Syntax_Syntax.ppname = uu____8453;
                       FStar_Syntax_Syntax.index =
                         (uu___1177_8452.FStar_Syntax_Syntax.index);
                       FStar_Syntax_Syntax.sort =
                         (uu___1177_8452.FStar_Syntax_Syntax.sort)
                     }  in
                   FStar_Syntax_Syntax.freshen_bv uu____8451  in
                 let s1 =
                   let uu____8458 =
                     let uu____8459 =
                       let uu____8466 = FStar_Syntax_Syntax.bv_to_name bv'
                          in
                       (bv, uu____8466)  in
                     FStar_Syntax_Syntax.NT uu____8459  in
                   [uu____8458]  in
                 let uu____8471 = subst_goal bv bv' s1 goal  in
                 (match uu____8471 with
                  | FStar_Pervasives_Native.None  ->
                      fail "binder not found in environment"
                  | FStar_Pervasives_Native.Some goal1 -> replace_cur goal1))
         in
      FStar_All.pipe_left (wrap_err "rename_to") uu____8427
  
let (binder_retype : FStar_Syntax_Syntax.binder -> unit tac) =
  fun b  ->
    let uu____8493 =
      let uu____8496 = cur_goal ()  in
      bind uu____8496
        (fun goal  ->
           let uu____8505 = b  in
           match uu____8505 with
           | (bv,uu____8509) ->
               let uu____8514 =
                 let uu____8525 = FStar_Tactics_Types.goal_env goal  in
                 split_env bv uu____8525  in
               (match uu____8514 with
                | FStar_Pervasives_Native.None  ->
                    fail "binder is not present in environment"
                | FStar_Pervasives_Native.Some (e0,bv1,bvs) ->
                    let uu____8552 = FStar_Syntax_Util.type_u ()  in
                    (match uu____8552 with
                     | (ty,u) ->
                         let uu____8561 = new_uvar "binder_retype" e0 ty  in
                         bind uu____8561
                           (fun uu____8580  ->
                              match uu____8580 with
                              | (t',u_t') ->
                                  let bv'' =
                                    let uu___1201_8590 = bv1  in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___1201_8590.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___1201_8590.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = t'
                                    }  in
                                  let s =
                                    let uu____8594 =
                                      let uu____8595 =
                                        let uu____8602 =
                                          FStar_Syntax_Syntax.bv_to_name bv''
                                           in
                                        (bv1, uu____8602)  in
                                      FStar_Syntax_Syntax.NT uu____8595  in
                                    [uu____8594]  in
                                  let bvs1 =
                                    FStar_List.map
                                      (fun b1  ->
                                         let uu___1206_8614 = b1  in
                                         let uu____8615 =
                                           FStar_Syntax_Subst.subst s
                                             b1.FStar_Syntax_Syntax.sort
                                            in
                                         {
                                           FStar_Syntax_Syntax.ppname =
                                             (uu___1206_8614.FStar_Syntax_Syntax.ppname);
                                           FStar_Syntax_Syntax.index =
                                             (uu___1206_8614.FStar_Syntax_Syntax.index);
                                           FStar_Syntax_Syntax.sort =
                                             uu____8615
                                         }) bvs
                                     in
                                  let env' = push_bvs e0 (bv'' :: bvs1)  in
                                  bind __dismiss
                                    (fun uu____8622  ->
                                       let new_goal =
                                         let uu____8624 =
                                           FStar_Tactics_Types.goal_with_env
                                             goal env'
                                            in
                                         let uu____8625 =
                                           let uu____8626 =
                                             FStar_Tactics_Types.goal_type
                                               goal
                                              in
                                           FStar_Syntax_Subst.subst s
                                             uu____8626
                                            in
                                         FStar_Tactics_Types.goal_with_type
                                           uu____8624 uu____8625
                                          in
                                       let uu____8627 = add_goals [new_goal]
                                          in
                                       bind uu____8627
                                         (fun uu____8632  ->
                                            let uu____8633 =
                                              FStar_Syntax_Util.mk_eq2
                                                (FStar_Syntax_Syntax.U_succ u)
                                                ty
                                                bv1.FStar_Syntax_Syntax.sort
                                                t'
                                               in
                                            add_irrelevant_goal
                                              "binder_retype equation" e0
                                              uu____8633
                                              goal.FStar_Tactics_Types.opts
                                              goal.FStar_Tactics_Types.label))))))
       in
    FStar_All.pipe_left (wrap_err "binder_retype") uu____8493
  
let (norm_binder_type :
  FStar_Syntax_Embeddings.norm_step Prims.list ->
    FStar_Syntax_Syntax.binder -> unit tac)
  =
  fun s  ->
    fun b  ->
      let uu____8659 =
        let uu____8662 = cur_goal ()  in
        bind uu____8662
          (fun goal  ->
             let uu____8671 = b  in
             match uu____8671 with
             | (bv,uu____8675) ->
                 let uu____8680 =
                   let uu____8691 = FStar_Tactics_Types.goal_env goal  in
                   split_env bv uu____8691  in
                 (match uu____8680 with
                  | FStar_Pervasives_Native.None  ->
                      fail "binder is not present in environment"
                  | FStar_Pervasives_Native.Some (e0,bv1,bvs) ->
                      let steps =
                        let uu____8721 =
                          FStar_TypeChecker_Normalize.tr_norm_steps s  in
                        FStar_List.append
                          [FStar_TypeChecker_Env.Reify;
                          FStar_TypeChecker_Env.UnfoldTac] uu____8721
                         in
                      let sort' =
                        normalize steps e0 bv1.FStar_Syntax_Syntax.sort  in
                      let bv' =
                        let uu___1227_8726 = bv1  in
                        {
                          FStar_Syntax_Syntax.ppname =
                            (uu___1227_8726.FStar_Syntax_Syntax.ppname);
                          FStar_Syntax_Syntax.index =
                            (uu___1227_8726.FStar_Syntax_Syntax.index);
                          FStar_Syntax_Syntax.sort = sort'
                        }  in
                      let env' = push_bvs e0 (bv' :: bvs)  in
                      let uu____8728 =
                        FStar_Tactics_Types.goal_with_env goal env'  in
                      replace_cur uu____8728))
         in
      FStar_All.pipe_left (wrap_err "norm_binder_type") uu____8659
  
let (revert : unit -> unit tac) =
  fun uu____8741  ->
    let uu____8744 = cur_goal ()  in
    bind uu____8744
      (fun goal  ->
         let uu____8750 =
           let uu____8757 = FStar_Tactics_Types.goal_env goal  in
           FStar_TypeChecker_Env.pop_bv uu____8757  in
         match uu____8750 with
         | FStar_Pervasives_Native.None  ->
             fail "Cannot revert; empty context"
         | FStar_Pervasives_Native.Some (x,env') ->
             let typ' =
               let uu____8774 =
                 let uu____8777 = FStar_Tactics_Types.goal_type goal  in
                 FStar_Syntax_Syntax.mk_Total uu____8777  in
               FStar_Syntax_Util.arrow [(x, FStar_Pervasives_Native.None)]
                 uu____8774
                in
             let uu____8792 = new_uvar "revert" env' typ'  in
             bind uu____8792
               (fun uu____8808  ->
                  match uu____8808 with
                  | (r,u_r) ->
                      let uu____8817 =
                        let uu____8820 =
                          let uu____8821 =
                            let uu____8822 =
                              FStar_Tactics_Types.goal_type goal  in
                            uu____8822.FStar_Syntax_Syntax.pos  in
                          let uu____8825 =
                            let uu____8830 =
                              let uu____8831 =
                                let uu____8840 =
                                  FStar_Syntax_Syntax.bv_to_name x  in
                                FStar_Syntax_Syntax.as_arg uu____8840  in
                              [uu____8831]  in
                            FStar_Syntax_Syntax.mk_Tm_app r uu____8830  in
                          uu____8825 FStar_Pervasives_Native.None uu____8821
                           in
                        set_solution goal uu____8820  in
                      bind uu____8817
                        (fun uu____8859  ->
                           let g =
                             FStar_Tactics_Types.mk_goal env' u_r
                               goal.FStar_Tactics_Types.opts
                               goal.FStar_Tactics_Types.is_guard
                               goal.FStar_Tactics_Types.label
                              in
                           replace_cur g)))
  
let (free_in :
  FStar_Syntax_Syntax.bv -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun bv  ->
    fun t  ->
      let uu____8873 = FStar_Syntax_Free.names t  in
      FStar_Util.set_mem bv uu____8873
  
let (clear : FStar_Syntax_Syntax.binder -> unit tac) =
  fun b  ->
    let bv = FStar_Pervasives_Native.fst b  in
    let uu____8889 = cur_goal ()  in
    bind uu____8889
      (fun goal  ->
         mlog
           (fun uu____8897  ->
              let uu____8898 = FStar_Syntax_Print.binder_to_string b  in
              let uu____8900 =
                let uu____8902 =
                  let uu____8904 =
                    let uu____8913 = FStar_Tactics_Types.goal_env goal  in
                    FStar_TypeChecker_Env.all_binders uu____8913  in
                  FStar_All.pipe_right uu____8904 FStar_List.length  in
                FStar_All.pipe_right uu____8902 FStar_Util.string_of_int  in
              FStar_Util.print2 "Clear of (%s), env has %s binders\n"
                uu____8898 uu____8900)
           (fun uu____8934  ->
              let uu____8935 =
                let uu____8946 = FStar_Tactics_Types.goal_env goal  in
                split_env bv uu____8946  in
              match uu____8935 with
              | FStar_Pervasives_Native.None  ->
                  fail "Cannot clear; binder not in environment"
              | FStar_Pervasives_Native.Some (e',bv1,bvs) ->
                  let rec check1 bvs1 =
                    match bvs1 with
                    | [] -> ret ()
                    | bv'::bvs2 ->
                        let uu____8991 =
                          free_in bv1 bv'.FStar_Syntax_Syntax.sort  in
                        if uu____8991
                        then
                          let uu____8996 =
                            let uu____8998 =
                              FStar_Syntax_Print.bv_to_string bv'  in
                            FStar_Util.format1
                              "Cannot clear; binder present in the type of %s"
                              uu____8998
                             in
                          fail uu____8996
                        else check1 bvs2
                     in
                  let uu____9003 =
                    let uu____9005 = FStar_Tactics_Types.goal_type goal  in
                    free_in bv1 uu____9005  in
                  if uu____9003
                  then fail "Cannot clear; binder present in goal"
                  else
                    (let uu____9012 = check1 bvs  in
                     bind uu____9012
                       (fun uu____9018  ->
                          let env' = push_bvs e' bvs  in
                          let uu____9020 =
                            let uu____9027 =
                              FStar_Tactics_Types.goal_type goal  in
                            new_uvar "clear.witness" env' uu____9027  in
                          bind uu____9020
                            (fun uu____9037  ->
                               match uu____9037 with
                               | (ut,uvar_ut) ->
                                   let uu____9046 = set_solution goal ut  in
                                   bind uu____9046
                                     (fun uu____9051  ->
                                        let uu____9052 =
                                          FStar_Tactics_Types.mk_goal env'
                                            uvar_ut
                                            goal.FStar_Tactics_Types.opts
                                            goal.FStar_Tactics_Types.is_guard
                                            goal.FStar_Tactics_Types.label
                                           in
                                        replace_cur uu____9052))))))
  
let (clear_top : unit -> unit tac) =
  fun uu____9060  ->
    let uu____9063 = cur_goal ()  in
    bind uu____9063
      (fun goal  ->
         let uu____9069 =
           let uu____9076 = FStar_Tactics_Types.goal_env goal  in
           FStar_TypeChecker_Env.pop_bv uu____9076  in
         match uu____9069 with
         | FStar_Pervasives_Native.None  ->
             fail "Cannot clear; empty context"
         | FStar_Pervasives_Native.Some (x,uu____9085) ->
             let uu____9090 = FStar_Syntax_Syntax.mk_binder x  in
             clear uu____9090)
  
let (prune : Prims.string -> unit tac) =
  fun s  ->
    let uu____9103 = cur_goal ()  in
    bind uu____9103
      (fun g  ->
         let ctx = FStar_Tactics_Types.goal_env g  in
         let ctx' =
           let uu____9113 = FStar_Ident.path_of_text s  in
           FStar_TypeChecker_Env.rem_proof_ns ctx uu____9113  in
         let g' = FStar_Tactics_Types.goal_with_env g ctx'  in
         bind __dismiss (fun uu____9116  -> add_goals [g']))
  
let (addns : Prims.string -> unit tac) =
  fun s  ->
    let uu____9129 = cur_goal ()  in
    bind uu____9129
      (fun g  ->
         let ctx = FStar_Tactics_Types.goal_env g  in
         let ctx' =
           let uu____9139 = FStar_Ident.path_of_text s  in
           FStar_TypeChecker_Env.add_proof_ns ctx uu____9139  in
         let g' = FStar_Tactics_Types.goal_with_env g ctx'  in
         bind __dismiss (fun uu____9142  -> add_goals [g']))
  
let rec (tac_fold_env :
  FStar_Tactics_Types.direction ->
    (env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term tac) ->
      env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term tac)
  =
  fun d  ->
    fun f  ->
      fun env  ->
        fun t  ->
          let tn =
            let uu____9183 = FStar_Syntax_Subst.compress t  in
            uu____9183.FStar_Syntax_Syntax.n  in
          let uu____9186 =
            if d = FStar_Tactics_Types.TopDown
            then
              f env
                (let uu___1411_9193 = t  in
                 {
                   FStar_Syntax_Syntax.n = tn;
                   FStar_Syntax_Syntax.pos =
                     (uu___1411_9193.FStar_Syntax_Syntax.pos);
                   FStar_Syntax_Syntax.vars =
                     (uu___1411_9193.FStar_Syntax_Syntax.vars)
                 })
            else ret t  in
          bind uu____9186
            (fun t1  ->
               let ff = tac_fold_env d f env  in
               let tn1 =
                 let uu____9210 =
                   let uu____9211 = FStar_Syntax_Subst.compress t1  in
                   uu____9211.FStar_Syntax_Syntax.n  in
                 match uu____9210 with
                 | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
                     let uu____9242 = ff hd1  in
                     bind uu____9242
                       (fun hd2  ->
                          let fa uu____9268 =
                            match uu____9268 with
                            | (a,q) ->
                                let uu____9289 = ff a  in
                                bind uu____9289 (fun a1  -> ret (a1, q))
                             in
                          let uu____9308 = mapM fa args  in
                          bind uu____9308
                            (fun args1  ->
                               ret (FStar_Syntax_Syntax.Tm_app (hd2, args1))))
                 | FStar_Syntax_Syntax.Tm_abs (bs,t2,k) ->
                     let uu____9390 = FStar_Syntax_Subst.open_term bs t2  in
                     (match uu____9390 with
                      | (bs1,t') ->
                          let uu____9399 =
                            let uu____9402 =
                              FStar_TypeChecker_Env.push_binders env bs1  in
                            tac_fold_env d f uu____9402 t'  in
                          bind uu____9399
                            (fun t''  ->
                               let uu____9406 =
                                 let uu____9407 =
                                   let uu____9426 =
                                     FStar_Syntax_Subst.close_binders bs1  in
                                   let uu____9435 =
                                     FStar_Syntax_Subst.close bs1 t''  in
                                   (uu____9426, uu____9435, k)  in
                                 FStar_Syntax_Syntax.Tm_abs uu____9407  in
                               ret uu____9406))
                 | FStar_Syntax_Syntax.Tm_arrow (bs,k) -> ret tn
                 | FStar_Syntax_Syntax.Tm_match (hd1,brs) ->
                     let uu____9510 = ff hd1  in
                     bind uu____9510
                       (fun hd2  ->
                          let ffb br =
                            let uu____9525 =
                              FStar_Syntax_Subst.open_branch br  in
                            match uu____9525 with
                            | (pat,w,e) ->
                                let bvs = FStar_Syntax_Syntax.pat_bvs pat  in
                                let ff1 =
                                  let uu____9557 =
                                    FStar_TypeChecker_Env.push_bvs env bvs
                                     in
                                  tac_fold_env d f uu____9557  in
                                let uu____9558 = ff1 e  in
                                bind uu____9558
                                  (fun e1  ->
                                     let br1 =
                                       FStar_Syntax_Subst.close_branch
                                         (pat, w, e1)
                                        in
                                     ret br1)
                             in
                          let uu____9573 = mapM ffb brs  in
                          bind uu____9573
                            (fun brs1  ->
                               ret (FStar_Syntax_Syntax.Tm_match (hd2, brs1))))
                 | FStar_Syntax_Syntax.Tm_let
                     ((false
                       ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inl bv;
                          FStar_Syntax_Syntax.lbunivs = uu____9617;
                          FStar_Syntax_Syntax.lbtyp = uu____9618;
                          FStar_Syntax_Syntax.lbeff = uu____9619;
                          FStar_Syntax_Syntax.lbdef = def;
                          FStar_Syntax_Syntax.lbattrs = uu____9621;
                          FStar_Syntax_Syntax.lbpos = uu____9622;_}::[]),e)
                     ->
                     let lb =
                       let uu____9650 =
                         let uu____9651 = FStar_Syntax_Subst.compress t1  in
                         uu____9651.FStar_Syntax_Syntax.n  in
                       match uu____9650 with
                       | FStar_Syntax_Syntax.Tm_let
                           ((false ,lb::[]),uu____9655) -> lb
                       | uu____9671 -> failwith "impossible"  in
                     let fflb lb1 =
                       let uu____9681 = ff lb1.FStar_Syntax_Syntax.lbdef  in
                       bind uu____9681
                         (fun def1  ->
                            ret
                              (let uu___1364_9687 = lb1  in
                               {
                                 FStar_Syntax_Syntax.lbname =
                                   (uu___1364_9687.FStar_Syntax_Syntax.lbname);
                                 FStar_Syntax_Syntax.lbunivs =
                                   (uu___1364_9687.FStar_Syntax_Syntax.lbunivs);
                                 FStar_Syntax_Syntax.lbtyp =
                                   (uu___1364_9687.FStar_Syntax_Syntax.lbtyp);
                                 FStar_Syntax_Syntax.lbeff =
                                   (uu___1364_9687.FStar_Syntax_Syntax.lbeff);
                                 FStar_Syntax_Syntax.lbdef = def1;
                                 FStar_Syntax_Syntax.lbattrs =
                                   (uu___1364_9687.FStar_Syntax_Syntax.lbattrs);
                                 FStar_Syntax_Syntax.lbpos =
                                   (uu___1364_9687.FStar_Syntax_Syntax.lbpos)
                               }))
                        in
                     let uu____9688 = fflb lb  in
                     bind uu____9688
                       (fun lb1  ->
                          let uu____9698 =
                            let uu____9703 =
                              let uu____9704 =
                                FStar_Syntax_Syntax.mk_binder bv  in
                              [uu____9704]  in
                            FStar_Syntax_Subst.open_term uu____9703 e  in
                          match uu____9698 with
                          | (bs,e1) ->
                              let ff1 =
                                let uu____9734 =
                                  FStar_TypeChecker_Env.push_binders env bs
                                   in
                                tac_fold_env d f uu____9734  in
                              let uu____9735 = ff1 e1  in
                              bind uu____9735
                                (fun e2  ->
                                   let e3 = FStar_Syntax_Subst.close bs e2
                                      in
                                   ret
                                     (FStar_Syntax_Syntax.Tm_let
                                        ((false, [lb1]), e3))))
                 | FStar_Syntax_Syntax.Tm_let ((true ,lbs),e) ->
                     let fflb lb =
                       let uu____9782 = ff lb.FStar_Syntax_Syntax.lbdef  in
                       bind uu____9782
                         (fun def  ->
                            ret
                              (let uu___1382_9788 = lb  in
                               {
                                 FStar_Syntax_Syntax.lbname =
                                   (uu___1382_9788.FStar_Syntax_Syntax.lbname);
                                 FStar_Syntax_Syntax.lbunivs =
                                   (uu___1382_9788.FStar_Syntax_Syntax.lbunivs);
                                 FStar_Syntax_Syntax.lbtyp =
                                   (uu___1382_9788.FStar_Syntax_Syntax.lbtyp);
                                 FStar_Syntax_Syntax.lbeff =
                                   (uu___1382_9788.FStar_Syntax_Syntax.lbeff);
                                 FStar_Syntax_Syntax.lbdef = def;
                                 FStar_Syntax_Syntax.lbattrs =
                                   (uu___1382_9788.FStar_Syntax_Syntax.lbattrs);
                                 FStar_Syntax_Syntax.lbpos =
                                   (uu___1382_9788.FStar_Syntax_Syntax.lbpos)
                               }))
                        in
                     let uu____9789 = FStar_Syntax_Subst.open_let_rec lbs e
                        in
                     (match uu____9789 with
                      | (lbs1,e1) ->
                          let uu____9804 = mapM fflb lbs1  in
                          bind uu____9804
                            (fun lbs2  ->
                               let uu____9816 = ff e1  in
                               bind uu____9816
                                 (fun e2  ->
                                    let uu____9824 =
                                      FStar_Syntax_Subst.close_let_rec lbs2
                                        e2
                                       in
                                    match uu____9824 with
                                    | (lbs3,e3) ->
                                        ret
                                          (FStar_Syntax_Syntax.Tm_let
                                             ((true, lbs3), e3)))))
                 | FStar_Syntax_Syntax.Tm_ascribed (t2,asc,eff) ->
                     let uu____9895 = ff t2  in
                     bind uu____9895
                       (fun t3  ->
                          ret
                            (FStar_Syntax_Syntax.Tm_ascribed (t3, asc, eff)))
                 | FStar_Syntax_Syntax.Tm_meta (t2,m) ->
                     let uu____9926 = ff t2  in
                     bind uu____9926
                       (fun t3  -> ret (FStar_Syntax_Syntax.Tm_meta (t3, m)))
                 | uu____9933 -> ret tn  in
               bind tn1
                 (fun tn2  ->
                    let t' =
                      let uu___1406_9940 = t1  in
                      {
                        FStar_Syntax_Syntax.n = tn2;
                        FStar_Syntax_Syntax.pos =
                          (uu___1406_9940.FStar_Syntax_Syntax.pos);
                        FStar_Syntax_Syntax.vars =
                          (uu___1406_9940.FStar_Syntax_Syntax.vars)
                      }  in
                    if d = FStar_Tactics_Types.BottomUp
                    then f env t'
                    else ret t'))
  
let (pointwise_rec :
  FStar_Tactics_Types.proofstate ->
    unit tac ->
      FStar_Options.optionstate ->
        Prims.string ->
          FStar_TypeChecker_Env.env ->
            FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term tac)
  =
  fun ps  ->
    fun tau  ->
      fun opts  ->
        fun label1  ->
          fun env  ->
            fun t  ->
              let uu____9987 =
                FStar_TypeChecker_TcTerm.tc_term
                  (let uu___1419_9996 = env  in
                   {
                     FStar_TypeChecker_Env.solver =
                       (uu___1419_9996.FStar_TypeChecker_Env.solver);
                     FStar_TypeChecker_Env.range =
                       (uu___1419_9996.FStar_TypeChecker_Env.range);
                     FStar_TypeChecker_Env.curmodule =
                       (uu___1419_9996.FStar_TypeChecker_Env.curmodule);
                     FStar_TypeChecker_Env.gamma =
                       (uu___1419_9996.FStar_TypeChecker_Env.gamma);
                     FStar_TypeChecker_Env.gamma_sig =
                       (uu___1419_9996.FStar_TypeChecker_Env.gamma_sig);
                     FStar_TypeChecker_Env.gamma_cache =
                       (uu___1419_9996.FStar_TypeChecker_Env.gamma_cache);
                     FStar_TypeChecker_Env.modules =
                       (uu___1419_9996.FStar_TypeChecker_Env.modules);
                     FStar_TypeChecker_Env.expected_typ =
                       (uu___1419_9996.FStar_TypeChecker_Env.expected_typ);
                     FStar_TypeChecker_Env.sigtab =
                       (uu___1419_9996.FStar_TypeChecker_Env.sigtab);
                     FStar_TypeChecker_Env.attrtab =
                       (uu___1419_9996.FStar_TypeChecker_Env.attrtab);
                     FStar_TypeChecker_Env.instantiate_imp =
                       (uu___1419_9996.FStar_TypeChecker_Env.instantiate_imp);
                     FStar_TypeChecker_Env.effects =
                       (uu___1419_9996.FStar_TypeChecker_Env.effects);
                     FStar_TypeChecker_Env.generalize =
                       (uu___1419_9996.FStar_TypeChecker_Env.generalize);
                     FStar_TypeChecker_Env.letrecs =
                       (uu___1419_9996.FStar_TypeChecker_Env.letrecs);
                     FStar_TypeChecker_Env.top_level =
                       (uu___1419_9996.FStar_TypeChecker_Env.top_level);
                     FStar_TypeChecker_Env.check_uvars =
                       (uu___1419_9996.FStar_TypeChecker_Env.check_uvars);
                     FStar_TypeChecker_Env.use_eq =
                       (uu___1419_9996.FStar_TypeChecker_Env.use_eq);
                     FStar_TypeChecker_Env.use_eq_strict =
                       (uu___1419_9996.FStar_TypeChecker_Env.use_eq_strict);
                     FStar_TypeChecker_Env.is_iface =
                       (uu___1419_9996.FStar_TypeChecker_Env.is_iface);
                     FStar_TypeChecker_Env.admit =
                       (uu___1419_9996.FStar_TypeChecker_Env.admit);
                     FStar_TypeChecker_Env.lax = true;
                     FStar_TypeChecker_Env.lax_universes =
                       (uu___1419_9996.FStar_TypeChecker_Env.lax_universes);
                     FStar_TypeChecker_Env.phase1 =
                       (uu___1419_9996.FStar_TypeChecker_Env.phase1);
                     FStar_TypeChecker_Env.failhard =
                       (uu___1419_9996.FStar_TypeChecker_Env.failhard);
                     FStar_TypeChecker_Env.nosynth =
                       (uu___1419_9996.FStar_TypeChecker_Env.nosynth);
                     FStar_TypeChecker_Env.uvar_subtyping =
                       (uu___1419_9996.FStar_TypeChecker_Env.uvar_subtyping);
                     FStar_TypeChecker_Env.tc_term =
                       (uu___1419_9996.FStar_TypeChecker_Env.tc_term);
                     FStar_TypeChecker_Env.type_of =
                       (uu___1419_9996.FStar_TypeChecker_Env.type_of);
                     FStar_TypeChecker_Env.universe_of =
                       (uu___1419_9996.FStar_TypeChecker_Env.universe_of);
                     FStar_TypeChecker_Env.check_type_of =
                       (uu___1419_9996.FStar_TypeChecker_Env.check_type_of);
                     FStar_TypeChecker_Env.use_bv_sorts =
                       (uu___1419_9996.FStar_TypeChecker_Env.use_bv_sorts);
                     FStar_TypeChecker_Env.qtbl_name_and_index =
                       (uu___1419_9996.FStar_TypeChecker_Env.qtbl_name_and_index);
                     FStar_TypeChecker_Env.normalized_eff_names =
                       (uu___1419_9996.FStar_TypeChecker_Env.normalized_eff_names);
                     FStar_TypeChecker_Env.fv_delta_depths =
                       (uu___1419_9996.FStar_TypeChecker_Env.fv_delta_depths);
                     FStar_TypeChecker_Env.proof_ns =
                       (uu___1419_9996.FStar_TypeChecker_Env.proof_ns);
                     FStar_TypeChecker_Env.synth_hook =
                       (uu___1419_9996.FStar_TypeChecker_Env.synth_hook);
                     FStar_TypeChecker_Env.try_solve_implicits_hook =
                       (uu___1419_9996.FStar_TypeChecker_Env.try_solve_implicits_hook);
                     FStar_TypeChecker_Env.splice =
                       (uu___1419_9996.FStar_TypeChecker_Env.splice);
                     FStar_TypeChecker_Env.mpreprocess =
                       (uu___1419_9996.FStar_TypeChecker_Env.mpreprocess);
                     FStar_TypeChecker_Env.postprocess =
                       (uu___1419_9996.FStar_TypeChecker_Env.postprocess);
                     FStar_TypeChecker_Env.is_native_tactic =
                       (uu___1419_9996.FStar_TypeChecker_Env.is_native_tactic);
                     FStar_TypeChecker_Env.identifier_info =
                       (uu___1419_9996.FStar_TypeChecker_Env.identifier_info);
                     FStar_TypeChecker_Env.tc_hooks =
                       (uu___1419_9996.FStar_TypeChecker_Env.tc_hooks);
                     FStar_TypeChecker_Env.dsenv =
                       (uu___1419_9996.FStar_TypeChecker_Env.dsenv);
                     FStar_TypeChecker_Env.nbe =
                       (uu___1419_9996.FStar_TypeChecker_Env.nbe);
                     FStar_TypeChecker_Env.strict_args_tab =
                       (uu___1419_9996.FStar_TypeChecker_Env.strict_args_tab);
                     FStar_TypeChecker_Env.erasable_types_tab =
                       (uu___1419_9996.FStar_TypeChecker_Env.erasable_types_tab)
                   }) t
                 in
              match uu____9987 with
              | (uu____10000,lcomp,g) ->
                  let uu____10003 =
                    (let uu____10007 =
                       FStar_TypeChecker_Common.is_pure_or_ghost_lcomp lcomp
                        in
                     Prims.op_Negation uu____10007) ||
                      (let uu____10010 = FStar_TypeChecker_Env.is_trivial g
                          in
                       Prims.op_Negation uu____10010)
                     in
                  if uu____10003
                  then ret t
                  else
                    (let rewrite_eq =
                       let typ = lcomp.FStar_TypeChecker_Common.res_typ  in
                       let uu____10021 = new_uvar "pointwise_rec" env typ  in
                       bind uu____10021
                         (fun uu____10038  ->
                            match uu____10038 with
                            | (ut,uvar_ut) ->
                                (log ps
                                   (fun uu____10051  ->
                                      let uu____10052 =
                                        FStar_Syntax_Print.term_to_string t
                                         in
                                      let uu____10054 =
                                        FStar_Syntax_Print.term_to_string ut
                                         in
                                      FStar_Util.print2
                                        "Pointwise_rec: making equality\n\t%s ==\n\t%s\n"
                                        uu____10052 uu____10054);
                                 (let uu____10057 =
                                    let uu____10060 =
                                      let uu____10061 =
                                        FStar_TypeChecker_TcTerm.universe_of
                                          env typ
                                         in
                                      FStar_Syntax_Util.mk_eq2 uu____10061
                                        typ t ut
                                       in
                                    add_irrelevant_goal
                                      "pointwise_rec equation" env
                                      uu____10060 opts label1
                                     in
                                  bind uu____10057
                                    (fun uu____10065  ->
                                       let uu____10066 =
                                         bind tau
                                           (fun uu____10072  ->
                                              let ut1 =
                                                FStar_TypeChecker_Normalize.reduce_uvar_solutions
                                                  env ut
                                                 in
                                              log ps
                                                (fun uu____10078  ->
                                                   let uu____10079 =
                                                     FStar_Syntax_Print.term_to_string
                                                       t
                                                      in
                                                   let uu____10081 =
                                                     FStar_Syntax_Print.term_to_string
                                                       ut1
                                                      in
                                                   FStar_Util.print2
                                                     "pointwise_rec: succeeded rewriting\n\t%s to\n\t%s\n"
                                                     uu____10079 uu____10081);
                                              ret ut1)
                                          in
                                       focus uu____10066))))
                        in
                     let uu____10084 = catch rewrite_eq  in
                     bind uu____10084
                       (fun uu___4_10096  ->
                          match uu___4_10096 with
                          | FStar_Util.Inl (FStar_Tactics_Types.TacticFailure
                              "SKIP") -> ret t
                          | FStar_Util.Inl e -> traise e
                          | FStar_Util.Inr x -> ret x))
  
type ctrl = FStar_BigInt.t
let (keepGoing : ctrl) = FStar_BigInt.zero 
let (proceedToNextSubtree : FStar_BigInt.bigint) = FStar_BigInt.one 
let (globalStop : FStar_BigInt.bigint) =
  FStar_BigInt.succ_big_int FStar_BigInt.one 
type rewrite_result = Prims.bool
let (skipThisTerm : Prims.bool) = false 
let (rewroteThisTerm : Prims.bool) = true 
type 'a ctrl_tac = ('a * ctrl) tac
let rec (ctrl_tac_fold :
  (env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term ctrl_tac) ->
    env ->
      ctrl -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term ctrl_tac)
  =
  fun f  ->
    fun env  ->
      fun ctrl  ->
        fun t  ->
          let keep_going c =
            if c = proceedToNextSubtree then keepGoing else c  in
          let maybe_continue ctrl1 t1 k =
            if ctrl1 = globalStop
            then ret (t1, globalStop)
            else
              if ctrl1 = proceedToNextSubtree
              then ret (t1, keepGoing)
              else k t1
             in
          let uu____10296 = FStar_Syntax_Subst.compress t  in
          maybe_continue ctrl uu____10296
            (fun t1  ->
               let uu____10304 =
                 f env
                   (let uu___1496_10312 = t1  in
                    {
                      FStar_Syntax_Syntax.n = (t1.FStar_Syntax_Syntax.n);
                      FStar_Syntax_Syntax.pos =
                        (uu___1496_10312.FStar_Syntax_Syntax.pos);
                      FStar_Syntax_Syntax.vars =
                        (uu___1496_10312.FStar_Syntax_Syntax.vars)
                    })
                  in
               bind uu____10304
                 (fun uu____10328  ->
                    match uu____10328 with
                    | (t2,ctrl1) ->
                        maybe_continue ctrl1 t2
                          (fun t3  ->
                             let uu____10351 =
                               let uu____10352 =
                                 FStar_Syntax_Subst.compress t3  in
                               uu____10352.FStar_Syntax_Syntax.n  in
                             match uu____10351 with
                             | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
                                 let uu____10389 =
                                   ctrl_tac_fold f env ctrl1 hd1  in
                                 bind uu____10389
                                   (fun uu____10411  ->
                                      match uu____10411 with
                                      | (hd2,ctrl2) ->
                                          let ctrl3 = keep_going ctrl2  in
                                          let uu____10427 =
                                            ctrl_tac_fold_args f env ctrl3
                                              args
                                             in
                                          bind uu____10427
                                            (fun uu____10451  ->
                                               match uu____10451 with
                                               | (args1,ctrl4) ->
                                                   ret
                                                     ((let uu___1476_10481 =
                                                         t3  in
                                                       {
                                                         FStar_Syntax_Syntax.n
                                                           =
                                                           (FStar_Syntax_Syntax.Tm_app
                                                              (hd2, args1));
                                                         FStar_Syntax_Syntax.pos
                                                           =
                                                           (uu___1476_10481.FStar_Syntax_Syntax.pos);
                                                         FStar_Syntax_Syntax.vars
                                                           =
                                                           (uu___1476_10481.FStar_Syntax_Syntax.vars)
                                                       }), ctrl4)))
                             | FStar_Syntax_Syntax.Tm_abs (bs,t4,k) ->
                                 let uu____10523 =
                                   FStar_Syntax_Subst.open_term bs t4  in
                                 (match uu____10523 with
                                  | (bs1,t') ->
                                      let uu____10538 =
                                        let uu____10545 =
                                          FStar_TypeChecker_Env.push_binders
                                            env bs1
                                           in
                                        ctrl_tac_fold f uu____10545 ctrl1 t'
                                         in
                                      bind uu____10538
                                        (fun uu____10560  ->
                                           match uu____10560 with
                                           | (t'',ctrl2) ->
                                               let uu____10575 =
                                                 let uu____10582 =
                                                   let uu___1489_10585 = t4
                                                      in
                                                   let uu____10588 =
                                                     let uu____10589 =
                                                       let uu____10608 =
                                                         FStar_Syntax_Subst.close_binders
                                                           bs1
                                                          in
                                                       let uu____10617 =
                                                         FStar_Syntax_Subst.close
                                                           bs1 t''
                                                          in
                                                       (uu____10608,
                                                         uu____10617, k)
                                                        in
                                                     FStar_Syntax_Syntax.Tm_abs
                                                       uu____10589
                                                      in
                                                   {
                                                     FStar_Syntax_Syntax.n =
                                                       uu____10588;
                                                     FStar_Syntax_Syntax.pos
                                                       =
                                                       (uu___1489_10585.FStar_Syntax_Syntax.pos);
                                                     FStar_Syntax_Syntax.vars
                                                       =
                                                       (uu___1489_10585.FStar_Syntax_Syntax.vars)
                                                   }  in
                                                 (uu____10582, ctrl2)  in
                                               ret uu____10575))
                             | FStar_Syntax_Syntax.Tm_arrow (bs,k) ->
                                 ret (t3, ctrl1)
                             | uu____10670 -> ret (t3, ctrl1))))

and (ctrl_tac_fold_args :
  (env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term ctrl_tac) ->
    env ->
      ctrl ->
        FStar_Syntax_Syntax.arg Prims.list ->
          FStar_Syntax_Syntax.arg Prims.list ctrl_tac)
  =
  fun f  ->
    fun env  ->
      fun ctrl  ->
        fun ts  ->
          match ts with
          | [] -> ret ([], ctrl)
          | (t,q)::ts1 ->
              let uu____10716 = ctrl_tac_fold f env ctrl t  in
              bind uu____10716
                (fun uu____10737  ->
                   match uu____10737 with
                   | (t1,ctrl1) ->
                       let uu____10752 = ctrl_tac_fold_args f env ctrl1 ts1
                          in
                       bind uu____10752
                         (fun uu____10776  ->
                            match uu____10776 with
                            | (ts2,ctrl2) -> ret (((t1, q) :: ts2), ctrl2)))

let (rewrite_rec :
  FStar_Tactics_Types.proofstate ->
    (FStar_Syntax_Syntax.term -> rewrite_result ctrl_tac) ->
      unit tac ->
        FStar_Options.optionstate ->
          Prims.string ->
            FStar_TypeChecker_Env.env ->
              FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term ctrl_tac)
  =
  fun ps  ->
    fun ctrl  ->
      fun rewriter  ->
        fun opts  ->
          fun label1  ->
            fun env  ->
              fun t  ->
                let t1 = FStar_Syntax_Subst.compress t  in
                let uu____10867 =
                  let uu____10875 =
                    add_irrelevant_goal "dummy" env FStar_Syntax_Util.t_true
                      opts label1
                     in
                  bind uu____10875
                    (fun uu____10886  ->
                       let uu____10887 = ctrl t1  in
                       bind uu____10887
                         (fun res  ->
                            let uu____10913 = trivial ()  in
                            bind uu____10913 (fun uu____10922  -> ret res)))
                   in
                bind uu____10867
                  (fun uu____10940  ->
                     match uu____10940 with
                     | (should_rewrite,ctrl1) ->
                         if Prims.op_Negation should_rewrite
                         then ret (t1, ctrl1)
                         else
                           (let uu____10969 =
                              FStar_TypeChecker_TcTerm.tc_term
                                (let uu___1526_10978 = env  in
                                 {
                                   FStar_TypeChecker_Env.solver =
                                     (uu___1526_10978.FStar_TypeChecker_Env.solver);
                                   FStar_TypeChecker_Env.range =
                                     (uu___1526_10978.FStar_TypeChecker_Env.range);
                                   FStar_TypeChecker_Env.curmodule =
                                     (uu___1526_10978.FStar_TypeChecker_Env.curmodule);
                                   FStar_TypeChecker_Env.gamma =
                                     (uu___1526_10978.FStar_TypeChecker_Env.gamma);
                                   FStar_TypeChecker_Env.gamma_sig =
                                     (uu___1526_10978.FStar_TypeChecker_Env.gamma_sig);
                                   FStar_TypeChecker_Env.gamma_cache =
                                     (uu___1526_10978.FStar_TypeChecker_Env.gamma_cache);
                                   FStar_TypeChecker_Env.modules =
                                     (uu___1526_10978.FStar_TypeChecker_Env.modules);
                                   FStar_TypeChecker_Env.expected_typ =
                                     (uu___1526_10978.FStar_TypeChecker_Env.expected_typ);
                                   FStar_TypeChecker_Env.sigtab =
                                     (uu___1526_10978.FStar_TypeChecker_Env.sigtab);
                                   FStar_TypeChecker_Env.attrtab =
                                     (uu___1526_10978.FStar_TypeChecker_Env.attrtab);
                                   FStar_TypeChecker_Env.instantiate_imp =
                                     (uu___1526_10978.FStar_TypeChecker_Env.instantiate_imp);
                                   FStar_TypeChecker_Env.effects =
                                     (uu___1526_10978.FStar_TypeChecker_Env.effects);
                                   FStar_TypeChecker_Env.generalize =
                                     (uu___1526_10978.FStar_TypeChecker_Env.generalize);
                                   FStar_TypeChecker_Env.letrecs =
                                     (uu___1526_10978.FStar_TypeChecker_Env.letrecs);
                                   FStar_TypeChecker_Env.top_level =
                                     (uu___1526_10978.FStar_TypeChecker_Env.top_level);
                                   FStar_TypeChecker_Env.check_uvars =
                                     (uu___1526_10978.FStar_TypeChecker_Env.check_uvars);
                                   FStar_TypeChecker_Env.use_eq =
                                     (uu___1526_10978.FStar_TypeChecker_Env.use_eq);
                                   FStar_TypeChecker_Env.use_eq_strict =
                                     (uu___1526_10978.FStar_TypeChecker_Env.use_eq_strict);
                                   FStar_TypeChecker_Env.is_iface =
                                     (uu___1526_10978.FStar_TypeChecker_Env.is_iface);
                                   FStar_TypeChecker_Env.admit =
                                     (uu___1526_10978.FStar_TypeChecker_Env.admit);
                                   FStar_TypeChecker_Env.lax = true;
                                   FStar_TypeChecker_Env.lax_universes =
                                     (uu___1526_10978.FStar_TypeChecker_Env.lax_universes);
                                   FStar_TypeChecker_Env.phase1 =
                                     (uu___1526_10978.FStar_TypeChecker_Env.phase1);
                                   FStar_TypeChecker_Env.failhard =
                                     (uu___1526_10978.FStar_TypeChecker_Env.failhard);
                                   FStar_TypeChecker_Env.nosynth =
                                     (uu___1526_10978.FStar_TypeChecker_Env.nosynth);
                                   FStar_TypeChecker_Env.uvar_subtyping =
                                     (uu___1526_10978.FStar_TypeChecker_Env.uvar_subtyping);
                                   FStar_TypeChecker_Env.tc_term =
                                     (uu___1526_10978.FStar_TypeChecker_Env.tc_term);
                                   FStar_TypeChecker_Env.type_of =
                                     (uu___1526_10978.FStar_TypeChecker_Env.type_of);
                                   FStar_TypeChecker_Env.universe_of =
                                     (uu___1526_10978.FStar_TypeChecker_Env.universe_of);
                                   FStar_TypeChecker_Env.check_type_of =
                                     (uu___1526_10978.FStar_TypeChecker_Env.check_type_of);
                                   FStar_TypeChecker_Env.use_bv_sorts =
                                     (uu___1526_10978.FStar_TypeChecker_Env.use_bv_sorts);
                                   FStar_TypeChecker_Env.qtbl_name_and_index
                                     =
                                     (uu___1526_10978.FStar_TypeChecker_Env.qtbl_name_and_index);
                                   FStar_TypeChecker_Env.normalized_eff_names
                                     =
                                     (uu___1526_10978.FStar_TypeChecker_Env.normalized_eff_names);
                                   FStar_TypeChecker_Env.fv_delta_depths =
                                     (uu___1526_10978.FStar_TypeChecker_Env.fv_delta_depths);
                                   FStar_TypeChecker_Env.proof_ns =
                                     (uu___1526_10978.FStar_TypeChecker_Env.proof_ns);
                                   FStar_TypeChecker_Env.synth_hook =
                                     (uu___1526_10978.FStar_TypeChecker_Env.synth_hook);
                                   FStar_TypeChecker_Env.try_solve_implicits_hook
                                     =
                                     (uu___1526_10978.FStar_TypeChecker_Env.try_solve_implicits_hook);
                                   FStar_TypeChecker_Env.splice =
                                     (uu___1526_10978.FStar_TypeChecker_Env.splice);
                                   FStar_TypeChecker_Env.mpreprocess =
                                     (uu___1526_10978.FStar_TypeChecker_Env.mpreprocess);
                                   FStar_TypeChecker_Env.postprocess =
                                     (uu___1526_10978.FStar_TypeChecker_Env.postprocess);
                                   FStar_TypeChecker_Env.is_native_tactic =
                                     (uu___1526_10978.FStar_TypeChecker_Env.is_native_tactic);
                                   FStar_TypeChecker_Env.identifier_info =
                                     (uu___1526_10978.FStar_TypeChecker_Env.identifier_info);
                                   FStar_TypeChecker_Env.tc_hooks =
                                     (uu___1526_10978.FStar_TypeChecker_Env.tc_hooks);
                                   FStar_TypeChecker_Env.dsenv =
                                     (uu___1526_10978.FStar_TypeChecker_Env.dsenv);
                                   FStar_TypeChecker_Env.nbe =
                                     (uu___1526_10978.FStar_TypeChecker_Env.nbe);
                                   FStar_TypeChecker_Env.strict_args_tab =
                                     (uu___1526_10978.FStar_TypeChecker_Env.strict_args_tab);
                                   FStar_TypeChecker_Env.erasable_types_tab =
                                     (uu___1526_10978.FStar_TypeChecker_Env.erasable_types_tab)
                                 }) t1
                               in
                            match uu____10969 with
                            | (t2,lcomp,g) ->
                                let uu____10989 =
                                  (let uu____10993 =
                                     FStar_TypeChecker_Common.is_pure_or_ghost_lcomp
                                       lcomp
                                      in
                                   Prims.op_Negation uu____10993) ||
                                    (let uu____10996 =
                                       FStar_TypeChecker_Env.is_trivial g  in
                                     Prims.op_Negation uu____10996)
                                   in
                                if uu____10989
                                then ret (t2, globalStop)
                                else
                                  (let typ =
                                     lcomp.FStar_TypeChecker_Common.res_typ
                                      in
                                   let uu____11012 =
                                     new_uvar "pointwise_rec" env typ  in
                                   bind uu____11012
                                     (fun uu____11033  ->
                                        match uu____11033 with
                                        | (ut,uvar_ut) ->
                                            (log ps
                                               (fun uu____11050  ->
                                                  let uu____11051 =
                                                    FStar_Syntax_Print.term_to_string
                                                      t2
                                                     in
                                                  let uu____11053 =
                                                    FStar_Syntax_Print.term_to_string
                                                      ut
                                                     in
                                                  FStar_Util.print2
                                                    "Pointwise_rec: making equality\n\t%s ==\n\t%s\n"
                                                    uu____11051 uu____11053);
                                             (let uu____11056 =
                                                let uu____11059 =
                                                  let uu____11060 =
                                                    FStar_TypeChecker_TcTerm.universe_of
                                                      env typ
                                                     in
                                                  FStar_Syntax_Util.mk_eq2
                                                    uu____11060 typ t2 ut
                                                   in
                                                add_irrelevant_goal
                                                  "rewrite_rec equation" env
                                                  uu____11059 opts label1
                                                 in
                                              bind uu____11056
                                                (fun uu____11068  ->
                                                   let uu____11069 =
                                                     bind rewriter
                                                       (fun uu____11083  ->
                                                          let ut1 =
                                                            FStar_TypeChecker_Normalize.reduce_uvar_solutions
                                                              env ut
                                                             in
                                                          log ps
                                                            (fun uu____11089 
                                                               ->
                                                               let uu____11090
                                                                 =
                                                                 FStar_Syntax_Print.term_to_string
                                                                   t2
                                                                  in
                                                               let uu____11092
                                                                 =
                                                                 FStar_Syntax_Print.term_to_string
                                                                   ut1
                                                                  in
                                                               FStar_Util.print2
                                                                 "rewrite_rec: succeeded rewriting\n\t%s to\n\t%s\n"
                                                                 uu____11090
                                                                 uu____11092);
                                                          ret (ut1, ctrl1))
                                                      in
                                                   focus uu____11069)))))))
  
let (topdown_rewrite :
  (FStar_Syntax_Syntax.term -> (Prims.bool * FStar_BigInt.t) tac) ->
    unit tac -> unit tac)
  =
  fun ctrl  ->
    fun rewriter  ->
      let uu____11137 =
        bind get
          (fun ps  ->
             let uu____11147 =
               match ps.FStar_Tactics_Types.goals with
               | g::gs -> (g, gs)
               | [] -> failwith "no goals"  in
             match uu____11147 with
             | (g,gs) ->
                 let gt1 = FStar_Tactics_Types.goal_type g  in
                 (log ps
                    (fun uu____11185  ->
                       let uu____11186 =
                         FStar_Syntax_Print.term_to_string gt1  in
                       FStar_Util.print1 "Topdown_rewrite starting with %s\n"
                         uu____11186);
                  bind dismiss_all
                    (fun uu____11191  ->
                       let uu____11192 =
                         let uu____11199 = FStar_Tactics_Types.goal_env g  in
                         ctrl_tac_fold
                           (rewrite_rec ps ctrl rewriter
                              g.FStar_Tactics_Types.opts
                              g.FStar_Tactics_Types.label) uu____11199
                           keepGoing gt1
                          in
                       bind uu____11192
                         (fun uu____11209  ->
                            match uu____11209 with
                            | (gt',uu____11217) ->
                                (log ps
                                   (fun uu____11221  ->
                                      let uu____11222 =
                                        FStar_Syntax_Print.term_to_string gt'
                                         in
                                      FStar_Util.print1
                                        "Topdown_rewrite seems to have succeded with %s\n"
                                        uu____11222);
                                 (let uu____11225 = push_goals gs  in
                                  bind uu____11225
                                    (fun uu____11230  ->
                                       let uu____11231 =
                                         let uu____11234 =
                                           let uu____11235 =
                                             FStar_Tactics_Types.goal_with_type
                                               g gt'
                                              in
                                           FStar_All.pipe_right uu____11235
                                             bnorm_goal
                                            in
                                         [uu____11234]  in
                                       add_goals uu____11231)))))))
         in
      FStar_All.pipe_left (wrap_err "topdown_rewrite") uu____11137
  
let (t_pointwise : FStar_Tactics_Types.direction -> unit tac -> unit tac) =
  fun d  ->
    fun tau  ->
      let uu____11260 =
        bind get
          (fun ps  ->
             let uu____11270 =
               match ps.FStar_Tactics_Types.goals with
               | g::gs -> (g, gs)
               | [] -> failwith "no goals"  in
             match uu____11270 with
             | (g,gs) ->
                 let gt1 = FStar_Tactics_Types.goal_type g  in
                 (log ps
                    (fun uu____11308  ->
                       let uu____11309 =
                         FStar_Syntax_Print.term_to_string gt1  in
                       FStar_Util.print1 "Pointwise starting with %s\n"
                         uu____11309);
                  bind dismiss_all
                    (fun uu____11314  ->
                       let uu____11315 =
                         let uu____11318 = FStar_Tactics_Types.goal_env g  in
                         tac_fold_env d
                           (pointwise_rec ps tau g.FStar_Tactics_Types.opts
                              g.FStar_Tactics_Types.label) uu____11318 gt1
                          in
                       bind uu____11315
                         (fun gt'  ->
                            log ps
                              (fun uu____11326  ->
                                 let uu____11327 =
                                   FStar_Syntax_Print.term_to_string gt'  in
                                 FStar_Util.print1
                                   "Pointwise seems to have succeded with %s\n"
                                   uu____11327);
                            (let uu____11330 = push_goals gs  in
                             bind uu____11330
                               (fun uu____11335  ->
                                  let uu____11336 =
                                    let uu____11339 =
                                      let uu____11340 =
                                        FStar_Tactics_Types.goal_with_type g
                                          gt'
                                         in
                                      FStar_All.pipe_right uu____11340
                                        bnorm_goal
                                       in
                                    [uu____11339]  in
                                  add_goals uu____11336))))))
         in
      FStar_All.pipe_left (wrap_err "t_pointwise") uu____11260
  
let (_trefl :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> unit tac) =
  fun l  ->
    fun r  ->
      let uu____11361 = cur_goal ()  in
      bind uu____11361
        (fun g  ->
           let uu____11367 =
             let uu____11371 = FStar_Tactics_Types.goal_env g  in
             do_unify uu____11371 l r  in
           bind uu____11367
             (fun b  ->
                if b
                then solve' g FStar_Syntax_Util.exp_unit
                else
                  (let l1 =
                     let uu____11382 = FStar_Tactics_Types.goal_env g  in
                     FStar_TypeChecker_Normalize.normalize
                       [FStar_TypeChecker_Env.UnfoldUntil
                          FStar_Syntax_Syntax.delta_constant;
                       FStar_TypeChecker_Env.Primops;
                       FStar_TypeChecker_Env.UnfoldTac] uu____11382 l
                      in
                   let r1 =
                     let uu____11384 = FStar_Tactics_Types.goal_env g  in
                     FStar_TypeChecker_Normalize.normalize
                       [FStar_TypeChecker_Env.UnfoldUntil
                          FStar_Syntax_Syntax.delta_constant;
                       FStar_TypeChecker_Env.Primops;
                       FStar_TypeChecker_Env.UnfoldTac] uu____11384 r
                      in
                   let uu____11385 =
                     let uu____11389 = FStar_Tactics_Types.goal_env g  in
                     do_unify uu____11389 l1 r1  in
                   bind uu____11385
                     (fun b1  ->
                        if b1
                        then solve' g FStar_Syntax_Util.exp_unit
                        else
                          (let uu____11399 =
                             let uu____11406 =
                               let uu____11412 =
                                 FStar_Tactics_Types.goal_env g  in
                               tts uu____11412  in
                             FStar_TypeChecker_Err.print_discrepancy
                               uu____11406 l1 r1
                              in
                           match uu____11399 with
                           | (ls,rs) ->
                               fail2 "not a trivial equality ((%s) vs (%s))"
                                 ls rs)))))
  
let (trefl : unit -> unit tac) =
  fun uu____11429  ->
    let uu____11432 =
      let uu____11435 = cur_goal ()  in
      bind uu____11435
        (fun g  ->
           let uu____11443 =
             let uu____11450 =
               let uu____11451 = FStar_Tactics_Types.goal_env g  in
               let uu____11452 = FStar_Tactics_Types.goal_type g  in
               bnorm uu____11451 uu____11452  in
             destruct_eq uu____11450  in
           match uu____11443 with
           | FStar_Pervasives_Native.Some (l,r) -> _trefl l r
           | FStar_Pervasives_Native.None  ->
               let uu____11465 =
                 let uu____11467 = FStar_Tactics_Types.goal_env g  in
                 let uu____11468 = FStar_Tactics_Types.goal_type g  in
                 tts uu____11467 uu____11468  in
               fail1 "not an equality (%s)" uu____11465)
       in
    FStar_All.pipe_left (wrap_err "trefl") uu____11432
  
let (dup : unit -> unit tac) =
  fun uu____11482  ->
    let uu____11485 = cur_goal ()  in
    bind uu____11485
      (fun g  ->
         let uu____11491 =
           let uu____11498 = FStar_Tactics_Types.goal_env g  in
           let uu____11499 = FStar_Tactics_Types.goal_type g  in
           new_uvar "dup" uu____11498 uu____11499  in
         bind uu____11491
           (fun uu____11509  ->
              match uu____11509 with
              | (u,u_uvar) ->
                  let g' =
                    let uu___1609_11519 = g  in
                    {
                      FStar_Tactics_Types.goal_main_env =
                        (uu___1609_11519.FStar_Tactics_Types.goal_main_env);
                      FStar_Tactics_Types.goal_ctx_uvar = u_uvar;
                      FStar_Tactics_Types.opts =
                        (uu___1609_11519.FStar_Tactics_Types.opts);
                      FStar_Tactics_Types.is_guard =
                        (uu___1609_11519.FStar_Tactics_Types.is_guard);
                      FStar_Tactics_Types.label =
                        (uu___1609_11519.FStar_Tactics_Types.label)
                    }  in
                  bind __dismiss
                    (fun uu____11522  ->
                       let uu____11523 =
                         let uu____11526 = FStar_Tactics_Types.goal_env g  in
                         let uu____11527 =
                           let uu____11528 =
                             let uu____11529 = FStar_Tactics_Types.goal_env g
                                in
                             let uu____11530 =
                               FStar_Tactics_Types.goal_type g  in
                             FStar_TypeChecker_TcTerm.universe_of uu____11529
                               uu____11530
                              in
                           let uu____11531 = FStar_Tactics_Types.goal_type g
                              in
                           let uu____11532 =
                             FStar_Tactics_Types.goal_witness g  in
                           FStar_Syntax_Util.mk_eq2 uu____11528 uu____11531 u
                             uu____11532
                            in
                         add_irrelevant_goal "dup equation" uu____11526
                           uu____11527 g.FStar_Tactics_Types.opts
                           g.FStar_Tactics_Types.label
                          in
                       bind uu____11523
                         (fun uu____11536  ->
                            let uu____11537 = add_goals [g']  in
                            bind uu____11537 (fun uu____11541  -> ret ())))))
  
let longest_prefix :
  'a .
    ('a -> 'a -> Prims.bool) ->
      'a Prims.list ->
        'a Prims.list -> ('a Prims.list * 'a Prims.list * 'a Prims.list)
  =
  fun f  ->
    fun l1  ->
      fun l2  ->
        let rec aux acc l11 l21 =
          match (l11, l21) with
          | (x::xs,y::ys) ->
              let uu____11667 = f x y  in
              if uu____11667 then aux (x :: acc) xs ys else (acc, xs, ys)
          | uu____11690 -> (acc, l11, l21)  in
        let uu____11705 = aux [] l1 l2  in
        match uu____11705 with | (pr,t1,t2) -> ((FStar_List.rev pr), t1, t2)
  
let (join_goals :
  FStar_Tactics_Types.goal ->
    FStar_Tactics_Types.goal -> FStar_Tactics_Types.goal tac)
  =
  fun g1  ->
    fun g2  ->
      let close_forall_no_univs1 bs f =
        FStar_List.fold_right
          (fun b  ->
             fun f1  ->
               FStar_Syntax_Util.mk_forall_no_univ
                 (FStar_Pervasives_Native.fst b) f1) bs f
         in
      let uu____11811 = get_phi g1  in
      match uu____11811 with
      | FStar_Pervasives_Native.None  -> fail "goal 1 is not irrelevant"
      | FStar_Pervasives_Native.Some phi1 ->
          let uu____11818 = get_phi g2  in
          (match uu____11818 with
           | FStar_Pervasives_Native.None  -> fail "goal 2 is not irrelevant"
           | FStar_Pervasives_Native.Some phi2 ->
               let gamma1 =
                 (g1.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_gamma
                  in
               let gamma2 =
                 (g2.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_gamma
                  in
               let uu____11831 =
                 longest_prefix FStar_Syntax_Syntax.eq_binding
                   (FStar_List.rev gamma1) (FStar_List.rev gamma2)
                  in
               (match uu____11831 with
                | (gamma,r1,r2) ->
                    let t1 =
                      let uu____11862 =
                        FStar_TypeChecker_Env.binders_of_bindings
                          (FStar_List.rev r1)
                         in
                      close_forall_no_univs1 uu____11862 phi1  in
                    let t2 =
                      let uu____11872 =
                        FStar_TypeChecker_Env.binders_of_bindings
                          (FStar_List.rev r2)
                         in
                      close_forall_no_univs1 uu____11872 phi2  in
                    let uu____11881 =
                      set_solution g1 FStar_Syntax_Util.exp_unit  in
                    bind uu____11881
                      (fun uu____11886  ->
                         let uu____11887 =
                           set_solution g2 FStar_Syntax_Util.exp_unit  in
                         bind uu____11887
                           (fun uu____11894  ->
                              let ng = FStar_Syntax_Util.mk_conj t1 t2  in
                              let nenv =
                                let uu___1660_11899 =
                                  FStar_Tactics_Types.goal_env g1  in
                                let uu____11900 =
                                  FStar_Util.smap_create (Prims.of_int (100))
                                   in
                                {
                                  FStar_TypeChecker_Env.solver =
                                    (uu___1660_11899.FStar_TypeChecker_Env.solver);
                                  FStar_TypeChecker_Env.range =
                                    (uu___1660_11899.FStar_TypeChecker_Env.range);
                                  FStar_TypeChecker_Env.curmodule =
                                    (uu___1660_11899.FStar_TypeChecker_Env.curmodule);
                                  FStar_TypeChecker_Env.gamma =
                                    (FStar_List.rev gamma);
                                  FStar_TypeChecker_Env.gamma_sig =
                                    (uu___1660_11899.FStar_TypeChecker_Env.gamma_sig);
                                  FStar_TypeChecker_Env.gamma_cache =
                                    uu____11900;
                                  FStar_TypeChecker_Env.modules =
                                    (uu___1660_11899.FStar_TypeChecker_Env.modules);
                                  FStar_TypeChecker_Env.expected_typ =
                                    (uu___1660_11899.FStar_TypeChecker_Env.expected_typ);
                                  FStar_TypeChecker_Env.sigtab =
                                    (uu___1660_11899.FStar_TypeChecker_Env.sigtab);
                                  FStar_TypeChecker_Env.attrtab =
                                    (uu___1660_11899.FStar_TypeChecker_Env.attrtab);
                                  FStar_TypeChecker_Env.instantiate_imp =
                                    (uu___1660_11899.FStar_TypeChecker_Env.instantiate_imp);
                                  FStar_TypeChecker_Env.effects =
                                    (uu___1660_11899.FStar_TypeChecker_Env.effects);
                                  FStar_TypeChecker_Env.generalize =
                                    (uu___1660_11899.FStar_TypeChecker_Env.generalize);
                                  FStar_TypeChecker_Env.letrecs =
                                    (uu___1660_11899.FStar_TypeChecker_Env.letrecs);
                                  FStar_TypeChecker_Env.top_level =
                                    (uu___1660_11899.FStar_TypeChecker_Env.top_level);
                                  FStar_TypeChecker_Env.check_uvars =
                                    (uu___1660_11899.FStar_TypeChecker_Env.check_uvars);
                                  FStar_TypeChecker_Env.use_eq =
                                    (uu___1660_11899.FStar_TypeChecker_Env.use_eq);
                                  FStar_TypeChecker_Env.use_eq_strict =
                                    (uu___1660_11899.FStar_TypeChecker_Env.use_eq_strict);
                                  FStar_TypeChecker_Env.is_iface =
                                    (uu___1660_11899.FStar_TypeChecker_Env.is_iface);
                                  FStar_TypeChecker_Env.admit =
                                    (uu___1660_11899.FStar_TypeChecker_Env.admit);
                                  FStar_TypeChecker_Env.lax =
                                    (uu___1660_11899.FStar_TypeChecker_Env.lax);
                                  FStar_TypeChecker_Env.lax_universes =
                                    (uu___1660_11899.FStar_TypeChecker_Env.lax_universes);
                                  FStar_TypeChecker_Env.phase1 =
                                    (uu___1660_11899.FStar_TypeChecker_Env.phase1);
                                  FStar_TypeChecker_Env.failhard =
                                    (uu___1660_11899.FStar_TypeChecker_Env.failhard);
                                  FStar_TypeChecker_Env.nosynth =
                                    (uu___1660_11899.FStar_TypeChecker_Env.nosynth);
                                  FStar_TypeChecker_Env.uvar_subtyping =
                                    (uu___1660_11899.FStar_TypeChecker_Env.uvar_subtyping);
                                  FStar_TypeChecker_Env.tc_term =
                                    (uu___1660_11899.FStar_TypeChecker_Env.tc_term);
                                  FStar_TypeChecker_Env.type_of =
                                    (uu___1660_11899.FStar_TypeChecker_Env.type_of);
                                  FStar_TypeChecker_Env.universe_of =
                                    (uu___1660_11899.FStar_TypeChecker_Env.universe_of);
                                  FStar_TypeChecker_Env.check_type_of =
                                    (uu___1660_11899.FStar_TypeChecker_Env.check_type_of);
                                  FStar_TypeChecker_Env.use_bv_sorts =
                                    (uu___1660_11899.FStar_TypeChecker_Env.use_bv_sorts);
                                  FStar_TypeChecker_Env.qtbl_name_and_index =
                                    (uu___1660_11899.FStar_TypeChecker_Env.qtbl_name_and_index);
                                  FStar_TypeChecker_Env.normalized_eff_names
                                    =
                                    (uu___1660_11899.FStar_TypeChecker_Env.normalized_eff_names);
                                  FStar_TypeChecker_Env.fv_delta_depths =
                                    (uu___1660_11899.FStar_TypeChecker_Env.fv_delta_depths);
                                  FStar_TypeChecker_Env.proof_ns =
                                    (uu___1660_11899.FStar_TypeChecker_Env.proof_ns);
                                  FStar_TypeChecker_Env.synth_hook =
                                    (uu___1660_11899.FStar_TypeChecker_Env.synth_hook);
                                  FStar_TypeChecker_Env.try_solve_implicits_hook
                                    =
                                    (uu___1660_11899.FStar_TypeChecker_Env.try_solve_implicits_hook);
                                  FStar_TypeChecker_Env.splice =
                                    (uu___1660_11899.FStar_TypeChecker_Env.splice);
                                  FStar_TypeChecker_Env.mpreprocess =
                                    (uu___1660_11899.FStar_TypeChecker_Env.mpreprocess);
                                  FStar_TypeChecker_Env.postprocess =
                                    (uu___1660_11899.FStar_TypeChecker_Env.postprocess);
                                  FStar_TypeChecker_Env.is_native_tactic =
                                    (uu___1660_11899.FStar_TypeChecker_Env.is_native_tactic);
                                  FStar_TypeChecker_Env.identifier_info =
                                    (uu___1660_11899.FStar_TypeChecker_Env.identifier_info);
                                  FStar_TypeChecker_Env.tc_hooks =
                                    (uu___1660_11899.FStar_TypeChecker_Env.tc_hooks);
                                  FStar_TypeChecker_Env.dsenv =
                                    (uu___1660_11899.FStar_TypeChecker_Env.dsenv);
                                  FStar_TypeChecker_Env.nbe =
                                    (uu___1660_11899.FStar_TypeChecker_Env.nbe);
                                  FStar_TypeChecker_Env.strict_args_tab =
                                    (uu___1660_11899.FStar_TypeChecker_Env.strict_args_tab);
                                  FStar_TypeChecker_Env.erasable_types_tab =
                                    (uu___1660_11899.FStar_TypeChecker_Env.erasable_types_tab)
                                }  in
                              let uu____11904 =
                                mk_irrelevant_goal "joined" nenv ng
                                  g1.FStar_Tactics_Types.opts
                                  g1.FStar_Tactics_Types.label
                                 in
                              bind uu____11904
                                (fun goal  ->
                                   mlog
                                     (fun uu____11914  ->
                                        let uu____11915 =
                                          goal_to_string_verbose g1  in
                                        let uu____11917 =
                                          goal_to_string_verbose g2  in
                                        let uu____11919 =
                                          goal_to_string_verbose goal  in
                                        FStar_Util.print3
                                          "join_goals of\n(%s)\nand\n(%s)\n= (%s)\n"
                                          uu____11915 uu____11917 uu____11919)
                                     (fun uu____11923  -> ret goal))))))
  
let (join : unit -> unit tac) =
  fun uu____11931  ->
    bind get
      (fun ps  ->
         match ps.FStar_Tactics_Types.goals with
         | g1::g2::gs ->
             let uu____11947 =
               set
                 (let uu___1675_11952 = ps  in
                  {
                    FStar_Tactics_Types.main_context =
                      (uu___1675_11952.FStar_Tactics_Types.main_context);
                    FStar_Tactics_Types.all_implicits =
                      (uu___1675_11952.FStar_Tactics_Types.all_implicits);
                    FStar_Tactics_Types.goals = gs;
                    FStar_Tactics_Types.smt_goals =
                      (uu___1675_11952.FStar_Tactics_Types.smt_goals);
                    FStar_Tactics_Types.depth =
                      (uu___1675_11952.FStar_Tactics_Types.depth);
                    FStar_Tactics_Types.__dump =
                      (uu___1675_11952.FStar_Tactics_Types.__dump);
                    FStar_Tactics_Types.psc =
                      (uu___1675_11952.FStar_Tactics_Types.psc);
                    FStar_Tactics_Types.entry_range =
                      (uu___1675_11952.FStar_Tactics_Types.entry_range);
                    FStar_Tactics_Types.guard_policy =
                      (uu___1675_11952.FStar_Tactics_Types.guard_policy);
                    FStar_Tactics_Types.freshness =
                      (uu___1675_11952.FStar_Tactics_Types.freshness);
                    FStar_Tactics_Types.tac_verb_dbg =
                      (uu___1675_11952.FStar_Tactics_Types.tac_verb_dbg);
                    FStar_Tactics_Types.local_state =
                      (uu___1675_11952.FStar_Tactics_Types.local_state)
                  })
                in
             bind uu____11947
               (fun uu____11955  ->
                  let uu____11956 = join_goals g1 g2  in
                  bind uu____11956 (fun g12  -> add_goals [g12]))
         | uu____11961 -> fail "join: less than 2 goals")
  
let (set_options : Prims.string -> unit tac) =
  fun s  ->
    let uu____11977 =
      let uu____11980 = cur_goal ()  in
      bind uu____11980
        (fun g  ->
           FStar_Options.push ();
           (let uu____11993 = FStar_Util.smap_copy g.FStar_Tactics_Types.opts
               in
            FStar_Options.set uu____11993);
           (let res = FStar_Options.set_options s  in
            let opts' = FStar_Options.peek ()  in
            FStar_Options.pop ();
            (match res with
             | FStar_Getopt.Success  ->
                 let g' =
                   let uu___1686_12000 = g  in
                   {
                     FStar_Tactics_Types.goal_main_env =
                       (uu___1686_12000.FStar_Tactics_Types.goal_main_env);
                     FStar_Tactics_Types.goal_ctx_uvar =
                       (uu___1686_12000.FStar_Tactics_Types.goal_ctx_uvar);
                     FStar_Tactics_Types.opts = opts';
                     FStar_Tactics_Types.is_guard =
                       (uu___1686_12000.FStar_Tactics_Types.is_guard);
                     FStar_Tactics_Types.label =
                       (uu___1686_12000.FStar_Tactics_Types.label)
                   }  in
                 replace_cur g'
             | FStar_Getopt.Error err ->
                 fail2 "Setting options `%s` failed: %s" s err
             | FStar_Getopt.Help  ->
                 fail1 "Setting options `%s` failed (got `Help`?)" s)))
       in
    FStar_All.pipe_left (wrap_err "set_options") uu____11977
  
let (top_env : unit -> env tac) =
  fun uu____12017  ->
    bind get
      (fun ps  -> FStar_All.pipe_left ret ps.FStar_Tactics_Types.main_context)
  
let (lax_on : unit -> Prims.bool tac) =
  fun uu____12032  ->
    let uu____12036 = cur_goal ()  in
    bind uu____12036
      (fun g  ->
         let uu____12043 =
           (FStar_Options.lax ()) ||
             (let uu____12046 = FStar_Tactics_Types.goal_env g  in
              uu____12046.FStar_TypeChecker_Env.lax)
            in
         ret uu____12043)
  
let (unquote :
  FStar_Reflection_Data.typ ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term tac)
  =
  fun ty  ->
    fun tm  ->
      let uu____12063 =
        mlog
          (fun uu____12068  ->
             let uu____12069 = FStar_Syntax_Print.term_to_string tm  in
             FStar_Util.print1 "unquote: tm = %s\n" uu____12069)
          (fun uu____12074  ->
             let uu____12075 = cur_goal ()  in
             bind uu____12075
               (fun goal  ->
                  let env =
                    let uu____12083 = FStar_Tactics_Types.goal_env goal  in
                    FStar_TypeChecker_Env.set_expected_typ uu____12083 ty  in
                  let uu____12084 = __tc_ghost env tm  in
                  bind uu____12084
                    (fun uu____12103  ->
                       match uu____12103 with
                       | (tm1,typ,guard) ->
                           mlog
                             (fun uu____12117  ->
                                let uu____12118 =
                                  FStar_Syntax_Print.term_to_string tm1  in
                                FStar_Util.print1 "unquote: tm' = %s\n"
                                  uu____12118)
                             (fun uu____12122  ->
                                mlog
                                  (fun uu____12125  ->
                                     let uu____12126 =
                                       FStar_Syntax_Print.term_to_string typ
                                        in
                                     FStar_Util.print1 "unquote: typ = %s\n"
                                       uu____12126)
                                  (fun uu____12131  ->
                                     let uu____12132 =
                                       proc_guard "unquote" env guard  in
                                     bind uu____12132
                                       (fun uu____12137  -> ret tm1))))))
         in
      FStar_All.pipe_left (wrap_err "unquote") uu____12063
  
let (uvar_env :
  env ->
    FStar_Reflection_Data.typ FStar_Pervasives_Native.option ->
      FStar_Syntax_Syntax.term tac)
  =
  fun env  ->
    fun ty  ->
      let uu____12162 =
        match ty with
        | FStar_Pervasives_Native.Some ty1 -> ret ty1
        | FStar_Pervasives_Native.None  ->
            let uu____12168 =
              let uu____12175 =
                let uu____12176 = FStar_Syntax_Util.type_u ()  in
                FStar_All.pipe_left FStar_Pervasives_Native.fst uu____12176
                 in
              new_uvar "uvar_env.2" env uu____12175  in
            bind uu____12168
              (fun uu____12193  ->
                 match uu____12193 with | (typ,uvar_typ) -> ret typ)
         in
      bind uu____12162
        (fun typ  ->
           let uu____12205 = new_uvar "uvar_env" env typ  in
           bind uu____12205
             (fun uu____12220  ->
                match uu____12220 with | (t,uvar_t) -> ret t))
  
let (unshelve : FStar_Syntax_Syntax.term -> unit tac) =
  fun t  ->
    let uu____12239 =
      bind get
        (fun ps  ->
           let env = ps.FStar_Tactics_Types.main_context  in
           let opts =
             match ps.FStar_Tactics_Types.goals with
             | g::uu____12258 -> g.FStar_Tactics_Types.opts
             | uu____12261 -> FStar_Options.peek ()  in
           let uu____12264 = FStar_Syntax_Util.head_and_args t  in
           match uu____12264 with
           | ({
                FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                  (ctx_uvar,uu____12284);
                FStar_Syntax_Syntax.pos = uu____12285;
                FStar_Syntax_Syntax.vars = uu____12286;_},uu____12287)
               ->
               let env1 =
                 let uu___1740_12329 = env  in
                 {
                   FStar_TypeChecker_Env.solver =
                     (uu___1740_12329.FStar_TypeChecker_Env.solver);
                   FStar_TypeChecker_Env.range =
                     (uu___1740_12329.FStar_TypeChecker_Env.range);
                   FStar_TypeChecker_Env.curmodule =
                     (uu___1740_12329.FStar_TypeChecker_Env.curmodule);
                   FStar_TypeChecker_Env.gamma =
                     (ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_gamma);
                   FStar_TypeChecker_Env.gamma_sig =
                     (uu___1740_12329.FStar_TypeChecker_Env.gamma_sig);
                   FStar_TypeChecker_Env.gamma_cache =
                     (uu___1740_12329.FStar_TypeChecker_Env.gamma_cache);
                   FStar_TypeChecker_Env.modules =
                     (uu___1740_12329.FStar_TypeChecker_Env.modules);
                   FStar_TypeChecker_Env.expected_typ =
                     (uu___1740_12329.FStar_TypeChecker_Env.expected_typ);
                   FStar_TypeChecker_Env.sigtab =
                     (uu___1740_12329.FStar_TypeChecker_Env.sigtab);
                   FStar_TypeChecker_Env.attrtab =
                     (uu___1740_12329.FStar_TypeChecker_Env.attrtab);
                   FStar_TypeChecker_Env.instantiate_imp =
                     (uu___1740_12329.FStar_TypeChecker_Env.instantiate_imp);
                   FStar_TypeChecker_Env.effects =
                     (uu___1740_12329.FStar_TypeChecker_Env.effects);
                   FStar_TypeChecker_Env.generalize =
                     (uu___1740_12329.FStar_TypeChecker_Env.generalize);
                   FStar_TypeChecker_Env.letrecs =
                     (uu___1740_12329.FStar_TypeChecker_Env.letrecs);
                   FStar_TypeChecker_Env.top_level =
                     (uu___1740_12329.FStar_TypeChecker_Env.top_level);
                   FStar_TypeChecker_Env.check_uvars =
                     (uu___1740_12329.FStar_TypeChecker_Env.check_uvars);
                   FStar_TypeChecker_Env.use_eq =
                     (uu___1740_12329.FStar_TypeChecker_Env.use_eq);
                   FStar_TypeChecker_Env.use_eq_strict =
                     (uu___1740_12329.FStar_TypeChecker_Env.use_eq_strict);
                   FStar_TypeChecker_Env.is_iface =
                     (uu___1740_12329.FStar_TypeChecker_Env.is_iface);
                   FStar_TypeChecker_Env.admit =
                     (uu___1740_12329.FStar_TypeChecker_Env.admit);
                   FStar_TypeChecker_Env.lax =
                     (uu___1740_12329.FStar_TypeChecker_Env.lax);
                   FStar_TypeChecker_Env.lax_universes =
                     (uu___1740_12329.FStar_TypeChecker_Env.lax_universes);
                   FStar_TypeChecker_Env.phase1 =
                     (uu___1740_12329.FStar_TypeChecker_Env.phase1);
                   FStar_TypeChecker_Env.failhard =
                     (uu___1740_12329.FStar_TypeChecker_Env.failhard);
                   FStar_TypeChecker_Env.nosynth =
                     (uu___1740_12329.FStar_TypeChecker_Env.nosynth);
                   FStar_TypeChecker_Env.uvar_subtyping =
                     (uu___1740_12329.FStar_TypeChecker_Env.uvar_subtyping);
                   FStar_TypeChecker_Env.tc_term =
                     (uu___1740_12329.FStar_TypeChecker_Env.tc_term);
                   FStar_TypeChecker_Env.type_of =
                     (uu___1740_12329.FStar_TypeChecker_Env.type_of);
                   FStar_TypeChecker_Env.universe_of =
                     (uu___1740_12329.FStar_TypeChecker_Env.universe_of);
                   FStar_TypeChecker_Env.check_type_of =
                     (uu___1740_12329.FStar_TypeChecker_Env.check_type_of);
                   FStar_TypeChecker_Env.use_bv_sorts =
                     (uu___1740_12329.FStar_TypeChecker_Env.use_bv_sorts);
                   FStar_TypeChecker_Env.qtbl_name_and_index =
                     (uu___1740_12329.FStar_TypeChecker_Env.qtbl_name_and_index);
                   FStar_TypeChecker_Env.normalized_eff_names =
                     (uu___1740_12329.FStar_TypeChecker_Env.normalized_eff_names);
                   FStar_TypeChecker_Env.fv_delta_depths =
                     (uu___1740_12329.FStar_TypeChecker_Env.fv_delta_depths);
                   FStar_TypeChecker_Env.proof_ns =
                     (uu___1740_12329.FStar_TypeChecker_Env.proof_ns);
                   FStar_TypeChecker_Env.synth_hook =
                     (uu___1740_12329.FStar_TypeChecker_Env.synth_hook);
                   FStar_TypeChecker_Env.try_solve_implicits_hook =
                     (uu___1740_12329.FStar_TypeChecker_Env.try_solve_implicits_hook);
                   FStar_TypeChecker_Env.splice =
                     (uu___1740_12329.FStar_TypeChecker_Env.splice);
                   FStar_TypeChecker_Env.mpreprocess =
                     (uu___1740_12329.FStar_TypeChecker_Env.mpreprocess);
                   FStar_TypeChecker_Env.postprocess =
                     (uu___1740_12329.FStar_TypeChecker_Env.postprocess);
                   FStar_TypeChecker_Env.is_native_tactic =
                     (uu___1740_12329.FStar_TypeChecker_Env.is_native_tactic);
                   FStar_TypeChecker_Env.identifier_info =
                     (uu___1740_12329.FStar_TypeChecker_Env.identifier_info);
                   FStar_TypeChecker_Env.tc_hooks =
                     (uu___1740_12329.FStar_TypeChecker_Env.tc_hooks);
                   FStar_TypeChecker_Env.dsenv =
                     (uu___1740_12329.FStar_TypeChecker_Env.dsenv);
                   FStar_TypeChecker_Env.nbe =
                     (uu___1740_12329.FStar_TypeChecker_Env.nbe);
                   FStar_TypeChecker_Env.strict_args_tab =
                     (uu___1740_12329.FStar_TypeChecker_Env.strict_args_tab);
                   FStar_TypeChecker_Env.erasable_types_tab =
                     (uu___1740_12329.FStar_TypeChecker_Env.erasable_types_tab)
                 }  in
               let g =
                 FStar_Tactics_Types.mk_goal env1 ctx_uvar opts false ""  in
               let uu____12333 =
                 let uu____12336 = bnorm_goal g  in [uu____12336]  in
               add_goals uu____12333
           | uu____12337 -> fail "not a uvar")
       in
    FStar_All.pipe_left (wrap_err "unshelve") uu____12239
  
let (tac_and : Prims.bool tac -> Prims.bool tac -> Prims.bool tac) =
  fun t1  ->
    fun t2  ->
      let comp =
        bind t1
          (fun b  ->
             let uu____12399 = if b then t2 else ret false  in
             bind uu____12399 (fun b'  -> if b' then ret b' else fail ""))
         in
      let uu____12425 = trytac comp  in
      bind uu____12425
        (fun uu___5_12437  ->
           match uu___5_12437 with
           | FStar_Pervasives_Native.Some (true ) -> ret true
           | FStar_Pervasives_Native.Some (false ) -> failwith "impossible"
           | FStar_Pervasives_Native.None  -> ret false)
  
let (unify_env :
  env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.bool tac)
  =
  fun e  ->
    fun t1  ->
      fun t2  ->
        let uu____12479 =
          bind get
            (fun ps  ->
               let uu____12487 = __tc e t1  in
               bind uu____12487
                 (fun uu____12508  ->
                    match uu____12508 with
                    | (t11,ty1,g1) ->
                        let uu____12521 = __tc e t2  in
                        bind uu____12521
                          (fun uu____12542  ->
                             match uu____12542 with
                             | (t21,ty2,g2) ->
                                 let uu____12555 =
                                   proc_guard "unify_env g1" e g1  in
                                 bind uu____12555
                                   (fun uu____12562  ->
                                      let uu____12563 =
                                        proc_guard "unify_env g2" e g2  in
                                      bind uu____12563
                                        (fun uu____12571  ->
                                           let uu____12572 =
                                             do_unify e ty1 ty2  in
                                           let uu____12576 =
                                             do_unify e t11 t21  in
                                           tac_and uu____12572 uu____12576)))))
           in
        FStar_All.pipe_left (wrap_err "unify_env") uu____12479
  
let (launch_process :
  Prims.string -> Prims.string Prims.list -> Prims.string -> Prims.string tac)
  =
  fun prog  ->
    fun args  ->
      fun input  ->
        bind idtac
          (fun uu____12624  ->
             let uu____12625 = FStar_Options.unsafe_tactic_exec ()  in
             if uu____12625
             then
               let s =
                 FStar_Util.run_process "tactic_launch" prog args
                   (FStar_Pervasives_Native.Some input)
                  in
               ret s
             else
               fail
                 "launch_process: will not run anything unless --unsafe_tactic_exec is provided")
  
let (fresh_bv_named :
  Prims.string -> FStar_Reflection_Data.typ -> FStar_Syntax_Syntax.bv tac) =
  fun nm  ->
    fun t  ->
      bind idtac
        (fun uu____12659  ->
           let uu____12660 =
             FStar_Syntax_Syntax.gen_bv nm FStar_Pervasives_Native.None t  in
           ret uu____12660)
  
let (change : FStar_Reflection_Data.typ -> unit tac) =
  fun ty  ->
    let uu____12671 =
      mlog
        (fun uu____12676  ->
           let uu____12677 = FStar_Syntax_Print.term_to_string ty  in
           FStar_Util.print1 "change: ty = %s\n" uu____12677)
        (fun uu____12682  ->
           let uu____12683 = cur_goal ()  in
           bind uu____12683
             (fun g  ->
                let uu____12689 =
                  let uu____12698 = FStar_Tactics_Types.goal_env g  in
                  __tc uu____12698 ty  in
                bind uu____12689
                  (fun uu____12710  ->
                     match uu____12710 with
                     | (ty1,uu____12720,guard) ->
                         let uu____12722 =
                           let uu____12725 = FStar_Tactics_Types.goal_env g
                              in
                           proc_guard "change" uu____12725 guard  in
                         bind uu____12722
                           (fun uu____12729  ->
                              let uu____12730 =
                                let uu____12734 =
                                  FStar_Tactics_Types.goal_env g  in
                                let uu____12735 =
                                  FStar_Tactics_Types.goal_type g  in
                                do_unify uu____12734 uu____12735 ty1  in
                              bind uu____12730
                                (fun bb  ->
                                   if bb
                                   then
                                     let uu____12744 =
                                       FStar_Tactics_Types.goal_with_type g
                                         ty1
                                        in
                                     replace_cur uu____12744
                                   else
                                     (let steps =
                                        [FStar_TypeChecker_Env.AllowUnboundUniverses;
                                        FStar_TypeChecker_Env.UnfoldUntil
                                          FStar_Syntax_Syntax.delta_constant;
                                        FStar_TypeChecker_Env.Primops]  in
                                      let ng =
                                        let uu____12751 =
                                          FStar_Tactics_Types.goal_env g  in
                                        let uu____12752 =
                                          FStar_Tactics_Types.goal_type g  in
                                        normalize steps uu____12751
                                          uu____12752
                                         in
                                      let nty =
                                        let uu____12754 =
                                          FStar_Tactics_Types.goal_env g  in
                                        normalize steps uu____12754 ty1  in
                                      let uu____12755 =
                                        let uu____12759 =
                                          FStar_Tactics_Types.goal_env g  in
                                        do_unify uu____12759 ng nty  in
                                      bind uu____12755
                                        (fun b  ->
                                           if b
                                           then
                                             let uu____12768 =
                                               FStar_Tactics_Types.goal_with_type
                                                 g ty1
                                                in
                                             replace_cur uu____12768
                                           else fail "not convertible")))))))
       in
    FStar_All.pipe_left (wrap_err "change") uu____12671
  
let failwhen : 'a . Prims.bool -> Prims.string -> (unit -> 'a tac) -> 'a tac
  = fun b  -> fun msg  -> fun k  -> if b then fail msg else k () 
let (t_destruct :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.fv * FStar_BigInt.t) Prims.list tac)
  =
  fun s_tm  ->
    let uu____12842 =
      let uu____12851 = cur_goal ()  in
      bind uu____12851
        (fun g  ->
           let uu____12863 =
             let uu____12872 = FStar_Tactics_Types.goal_env g  in
             __tc uu____12872 s_tm  in
           bind uu____12863
             (fun uu____12890  ->
                match uu____12890 with
                | (s_tm1,s_ty,guard) ->
                    let uu____12908 =
                      let uu____12911 = FStar_Tactics_Types.goal_env g  in
                      proc_guard "destruct" uu____12911 guard  in
                    bind uu____12908
                      (fun uu____12925  ->
                         let s_ty1 =
                           let uu____12927 = FStar_Tactics_Types.goal_env g
                              in
                           FStar_TypeChecker_Normalize.normalize
                             [FStar_TypeChecker_Env.UnfoldTac;
                             FStar_TypeChecker_Env.Weak;
                             FStar_TypeChecker_Env.HNF;
                             FStar_TypeChecker_Env.UnfoldUntil
                               FStar_Syntax_Syntax.delta_constant]
                             uu____12927 s_ty
                            in
                         let uu____12928 =
                           FStar_Syntax_Util.head_and_args' s_ty1  in
                         match uu____12928 with
                         | (h,args) ->
                             let uu____12973 =
                               let uu____12980 =
                                 let uu____12981 =
                                   FStar_Syntax_Subst.compress h  in
                                 uu____12981.FStar_Syntax_Syntax.n  in
                               match uu____12980 with
                               | FStar_Syntax_Syntax.Tm_fvar fv ->
                                   ret (fv, [])
                               | FStar_Syntax_Syntax.Tm_uinst
                                   ({
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.Tm_fvar fv;
                                      FStar_Syntax_Syntax.pos = uu____12996;
                                      FStar_Syntax_Syntax.vars = uu____12997;_},us)
                                   -> ret (fv, us)
                               | uu____13007 -> fail "type is not an fv"  in
                             bind uu____12973
                               (fun uu____13028  ->
                                  match uu____13028 with
                                  | (fv,a_us) ->
                                      let t_lid =
                                        FStar_Syntax_Syntax.lid_of_fv fv  in
                                      let uu____13044 =
                                        let uu____13047 =
                                          FStar_Tactics_Types.goal_env g  in
                                        FStar_TypeChecker_Env.lookup_sigelt
                                          uu____13047 t_lid
                                         in
                                      (match uu____13044 with
                                       | FStar_Pervasives_Native.None  ->
                                           fail
                                             "type not found in environment"
                                       | FStar_Pervasives_Native.Some se ->
                                           (match se.FStar_Syntax_Syntax.sigel
                                            with
                                            | FStar_Syntax_Syntax.Sig_inductive_typ
                                                (_lid,t_us,t_ps,t_ty,mut,c_lids)
                                                ->
                                                let erasable =
                                                  FStar_Syntax_Util.has_attribute
                                                    se.FStar_Syntax_Syntax.sigattrs
                                                    FStar_Parser_Const.erasable_attr
                                                   in
                                                let uu____13088 =
                                                  erasable &&
                                                    (let uu____13091 =
                                                       is_irrelevant g  in
                                                     Prims.op_Negation
                                                       uu____13091)
                                                   in
                                                failwhen uu____13088
                                                  "cannot destruct erasable type to solve proof-relevant goal"
                                                  (fun uu____13101  ->
                                                     failwhen
                                                       ((FStar_List.length
                                                           a_us)
                                                          <>
                                                          (FStar_List.length
                                                             t_us))
                                                       "t_us don't match?"
                                                       (fun uu____13114  ->
                                                          let uu____13115 =
                                                            FStar_Syntax_Subst.open_term
                                                              t_ps t_ty
                                                             in
                                                          match uu____13115
                                                          with
                                                          | (t_ps1,t_ty1) ->
                                                              let uu____13130
                                                                =
                                                                mapM
                                                                  (fun c_lid 
                                                                    ->
                                                                    let uu____13158
                                                                    =
                                                                    let uu____13161
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    g  in
                                                                    FStar_TypeChecker_Env.lookup_sigelt
                                                                    uu____13161
                                                                    c_lid  in
                                                                    match uu____13158
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.None
                                                                     ->
                                                                    fail
                                                                    "ctor not found?"
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    se1 ->
                                                                    (match 
                                                                    se1.FStar_Syntax_Syntax.sigel
                                                                    with
                                                                    | 
                                                                    FStar_Syntax_Syntax.Sig_datacon
                                                                    (_c_lid,c_us,c_ty,_t_lid,nparam,mut1)
                                                                    ->
                                                                    let fv1 =
                                                                    FStar_Syntax_Syntax.lid_as_fv
                                                                    c_lid
                                                                    FStar_Syntax_Syntax.delta_constant
                                                                    (FStar_Pervasives_Native.Some
                                                                    FStar_Syntax_Syntax.Data_ctor)
                                                                     in
                                                                    failwhen
                                                                    ((FStar_List.length
                                                                    a_us) <>
                                                                    (FStar_List.length
                                                                    c_us))
                                                                    "t_us don't match?"
                                                                    (fun
                                                                    uu____13238
                                                                     ->
                                                                    let s =
                                                                    FStar_TypeChecker_Env.mk_univ_subst
                                                                    c_us a_us
                                                                     in
                                                                    let c_ty1
                                                                    =
                                                                    FStar_Syntax_Subst.subst
                                                                    s c_ty
                                                                     in
                                                                    let uu____13243
                                                                    =
                                                                    FStar_TypeChecker_Env.inst_tscheme
                                                                    (c_us,
                                                                    c_ty1)
                                                                     in
                                                                    match uu____13243
                                                                    with
                                                                    | 
                                                                    (c_us1,c_ty2)
                                                                    ->
                                                                    let uu____13266
                                                                    =
                                                                    FStar_Syntax_Util.arrow_formals_comp
                                                                    c_ty2  in
                                                                    (match uu____13266
                                                                    with
                                                                    | 
                                                                    (bs,comp)
                                                                    ->
                                                                    let uu____13309
                                                                    =
                                                                    let rename_bv
                                                                    bv =
                                                                    let ppname
                                                                    =
                                                                    bv.FStar_Syntax_Syntax.ppname
                                                                     in
                                                                    let ppname1
                                                                    =
                                                                    let uu___1867_13332
                                                                    = ppname
                                                                     in
                                                                    {
                                                                    FStar_Ident.idText
                                                                    =
                                                                    (Prims.op_Hat
                                                                    "a"
                                                                    ppname.FStar_Ident.idText);
                                                                    FStar_Ident.idRange
                                                                    =
                                                                    (uu___1867_13332.FStar_Ident.idRange)
                                                                    }  in
                                                                    FStar_Syntax_Syntax.freshen_bv
                                                                    (let uu___1870_13336
                                                                    = bv  in
                                                                    {
                                                                    FStar_Syntax_Syntax.ppname
                                                                    = ppname1;
                                                                    FStar_Syntax_Syntax.index
                                                                    =
                                                                    (uu___1870_13336.FStar_Syntax_Syntax.index);
                                                                    FStar_Syntax_Syntax.sort
                                                                    =
                                                                    (uu___1870_13336.FStar_Syntax_Syntax.sort)
                                                                    })  in
                                                                    let bs' =
                                                                    FStar_List.map
                                                                    (fun
                                                                    uu____13362
                                                                     ->
                                                                    match uu____13362
                                                                    with
                                                                    | 
                                                                    (bv,aq)
                                                                    ->
                                                                    let uu____13381
                                                                    =
                                                                    rename_bv
                                                                    bv  in
                                                                    (uu____13381,
                                                                    aq)) bs
                                                                     in
                                                                    let subst1
                                                                    =
                                                                    FStar_List.map2
                                                                    (fun
                                                                    uu____13406
                                                                     ->
                                                                    fun
                                                                    uu____13407
                                                                     ->
                                                                    match 
                                                                    (uu____13406,
                                                                    uu____13407)
                                                                    with
                                                                    | 
                                                                    ((bv,uu____13433),
                                                                    (bv',uu____13435))
                                                                    ->
                                                                    let uu____13456
                                                                    =
                                                                    let uu____13463
                                                                    =
                                                                    FStar_Syntax_Syntax.bv_to_name
                                                                    bv'  in
                                                                    (bv,
                                                                    uu____13463)
                                                                     in
                                                                    FStar_Syntax_Syntax.NT
                                                                    uu____13456)
                                                                    bs bs'
                                                                     in
                                                                    let uu____13468
                                                                    =
                                                                    FStar_Syntax_Subst.subst_binders
                                                                    subst1
                                                                    bs'  in
                                                                    let uu____13477
                                                                    =
                                                                    FStar_Syntax_Subst.subst_comp
                                                                    subst1
                                                                    comp  in
                                                                    (uu____13468,
                                                                    uu____13477)
                                                                     in
                                                                    (match uu____13309
                                                                    with
                                                                    | 
                                                                    (bs1,comp1)
                                                                    ->
                                                                    let uu____13524
                                                                    =
                                                                    FStar_List.splitAt
                                                                    nparam
                                                                    bs1  in
                                                                    (match uu____13524
                                                                    with
                                                                    | 
                                                                    (d_ps,bs2)
                                                                    ->
                                                                    let uu____13597
                                                                    =
                                                                    let uu____13599
                                                                    =
                                                                    FStar_Syntax_Util.is_total_comp
                                                                    comp1  in
                                                                    Prims.op_Negation
                                                                    uu____13599
                                                                     in
                                                                    failwhen
                                                                    uu____13597
                                                                    "not total?"
                                                                    (fun
                                                                    uu____13618
                                                                     ->
                                                                    let mk_pat
                                                                    p =
                                                                    {
                                                                    FStar_Syntax_Syntax.v
                                                                    = p;
                                                                    FStar_Syntax_Syntax.p
                                                                    =
                                                                    (s_tm1.FStar_Syntax_Syntax.pos)
                                                                    }  in
                                                                    let is_imp
                                                                    uu___6_13635
                                                                    =
                                                                    match uu___6_13635
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    (FStar_Syntax_Syntax.Implicit
                                                                    uu____13639)
                                                                    -> true
                                                                    | 
                                                                    uu____13642
                                                                    -> false
                                                                     in
                                                                    let uu____13646
                                                                    =
                                                                    FStar_List.splitAt
                                                                    nparam
                                                                    args  in
                                                                    match uu____13646
                                                                    with
                                                                    | 
                                                                    (a_ps,a_is)
                                                                    ->
                                                                    failwhen
                                                                    ((FStar_List.length
                                                                    a_ps) <>
                                                                    (FStar_List.length
                                                                    d_ps))
                                                                    "params not match?"
                                                                    (fun
                                                                    uu____13782
                                                                     ->
                                                                    let d_ps_a_ps
                                                                    =
                                                                    FStar_List.zip
                                                                    d_ps a_ps
                                                                     in
                                                                    let subst1
                                                                    =
                                                                    FStar_List.map
                                                                    (fun
                                                                    uu____13844
                                                                     ->
                                                                    match uu____13844
                                                                    with
                                                                    | 
                                                                    ((bv,uu____13864),
                                                                    (t,uu____13866))
                                                                    ->
                                                                    FStar_Syntax_Syntax.NT
                                                                    (bv, t))
                                                                    d_ps_a_ps
                                                                     in
                                                                    let bs3 =
                                                                    FStar_Syntax_Subst.subst_binders
                                                                    subst1
                                                                    bs2  in
                                                                    let subpats_1
                                                                    =
                                                                    FStar_List.map
                                                                    (fun
                                                                    uu____13936
                                                                     ->
                                                                    match uu____13936
                                                                    with
                                                                    | 
                                                                    ((bv,uu____13963),
                                                                    (t,uu____13965))
                                                                    ->
                                                                    ((mk_pat
                                                                    (FStar_Syntax_Syntax.Pat_dot_term
                                                                    (bv, t))),
                                                                    true))
                                                                    d_ps_a_ps
                                                                     in
                                                                    let subpats_2
                                                                    =
                                                                    FStar_List.map
                                                                    (fun
                                                                    uu____14024
                                                                     ->
                                                                    match uu____14024
                                                                    with
                                                                    | 
                                                                    (bv,aq)
                                                                    ->
                                                                    ((mk_pat
                                                                    (FStar_Syntax_Syntax.Pat_var
                                                                    bv)),
                                                                    (is_imp
                                                                    aq))) bs3
                                                                     in
                                                                    let subpats
                                                                    =
                                                                    FStar_List.append
                                                                    subpats_1
                                                                    subpats_2
                                                                     in
                                                                    let pat =
                                                                    mk_pat
                                                                    (FStar_Syntax_Syntax.Pat_cons
                                                                    (fv1,
                                                                    subpats))
                                                                     in
                                                                    let env =
                                                                    FStar_Tactics_Types.goal_env
                                                                    g  in
                                                                    let cod =
                                                                    FStar_Tactics_Types.goal_type
                                                                    g  in
                                                                    let equ =
                                                                    env.FStar_TypeChecker_Env.universe_of
                                                                    env s_ty1
                                                                     in
                                                                    let uu____14079
                                                                    =
                                                                    FStar_TypeChecker_TcTerm.tc_pat
                                                                    (let uu___1929_14103
                                                                    = env  in
                                                                    {
                                                                    FStar_TypeChecker_Env.solver
                                                                    =
                                                                    (uu___1929_14103.FStar_TypeChecker_Env.solver);
                                                                    FStar_TypeChecker_Env.range
                                                                    =
                                                                    (uu___1929_14103.FStar_TypeChecker_Env.range);
                                                                    FStar_TypeChecker_Env.curmodule
                                                                    =
                                                                    (uu___1929_14103.FStar_TypeChecker_Env.curmodule);
                                                                    FStar_TypeChecker_Env.gamma
                                                                    =
                                                                    (uu___1929_14103.FStar_TypeChecker_Env.gamma);
                                                                    FStar_TypeChecker_Env.gamma_sig
                                                                    =
                                                                    (uu___1929_14103.FStar_TypeChecker_Env.gamma_sig);
                                                                    FStar_TypeChecker_Env.gamma_cache
                                                                    =
                                                                    (uu___1929_14103.FStar_TypeChecker_Env.gamma_cache);
                                                                    FStar_TypeChecker_Env.modules
                                                                    =
                                                                    (uu___1929_14103.FStar_TypeChecker_Env.modules);
                                                                    FStar_TypeChecker_Env.expected_typ
                                                                    =
                                                                    (uu___1929_14103.FStar_TypeChecker_Env.expected_typ);
                                                                    FStar_TypeChecker_Env.sigtab
                                                                    =
                                                                    (uu___1929_14103.FStar_TypeChecker_Env.sigtab);
                                                                    FStar_TypeChecker_Env.attrtab
                                                                    =
                                                                    (uu___1929_14103.FStar_TypeChecker_Env.attrtab);
                                                                    FStar_TypeChecker_Env.instantiate_imp
                                                                    =
                                                                    (uu___1929_14103.FStar_TypeChecker_Env.instantiate_imp);
                                                                    FStar_TypeChecker_Env.effects
                                                                    =
                                                                    (uu___1929_14103.FStar_TypeChecker_Env.effects);
                                                                    FStar_TypeChecker_Env.generalize
                                                                    =
                                                                    (uu___1929_14103.FStar_TypeChecker_Env.generalize);
                                                                    FStar_TypeChecker_Env.letrecs
                                                                    =
                                                                    (uu___1929_14103.FStar_TypeChecker_Env.letrecs);
                                                                    FStar_TypeChecker_Env.top_level
                                                                    =
                                                                    (uu___1929_14103.FStar_TypeChecker_Env.top_level);
                                                                    FStar_TypeChecker_Env.check_uvars
                                                                    =
                                                                    (uu___1929_14103.FStar_TypeChecker_Env.check_uvars);
                                                                    FStar_TypeChecker_Env.use_eq
                                                                    =
                                                                    (uu___1929_14103.FStar_TypeChecker_Env.use_eq);
                                                                    FStar_TypeChecker_Env.use_eq_strict
                                                                    =
                                                                    (uu___1929_14103.FStar_TypeChecker_Env.use_eq_strict);
                                                                    FStar_TypeChecker_Env.is_iface
                                                                    =
                                                                    (uu___1929_14103.FStar_TypeChecker_Env.is_iface);
                                                                    FStar_TypeChecker_Env.admit
                                                                    =
                                                                    (uu___1929_14103.FStar_TypeChecker_Env.admit);
                                                                    FStar_TypeChecker_Env.lax
                                                                    = true;
                                                                    FStar_TypeChecker_Env.lax_universes
                                                                    =
                                                                    (uu___1929_14103.FStar_TypeChecker_Env.lax_universes);
                                                                    FStar_TypeChecker_Env.phase1
                                                                    =
                                                                    (uu___1929_14103.FStar_TypeChecker_Env.phase1);
                                                                    FStar_TypeChecker_Env.failhard
                                                                    =
                                                                    (uu___1929_14103.FStar_TypeChecker_Env.failhard);
                                                                    FStar_TypeChecker_Env.nosynth
                                                                    =
                                                                    (uu___1929_14103.FStar_TypeChecker_Env.nosynth);
                                                                    FStar_TypeChecker_Env.uvar_subtyping
                                                                    =
                                                                    (uu___1929_14103.FStar_TypeChecker_Env.uvar_subtyping);
                                                                    FStar_TypeChecker_Env.tc_term
                                                                    =
                                                                    (uu___1929_14103.FStar_TypeChecker_Env.tc_term);
                                                                    FStar_TypeChecker_Env.type_of
                                                                    =
                                                                    (uu___1929_14103.FStar_TypeChecker_Env.type_of);
                                                                    FStar_TypeChecker_Env.universe_of
                                                                    =
                                                                    (uu___1929_14103.FStar_TypeChecker_Env.universe_of);
                                                                    FStar_TypeChecker_Env.check_type_of
                                                                    =
                                                                    (uu___1929_14103.FStar_TypeChecker_Env.check_type_of);
                                                                    FStar_TypeChecker_Env.use_bv_sorts
                                                                    =
                                                                    (uu___1929_14103.FStar_TypeChecker_Env.use_bv_sorts);
                                                                    FStar_TypeChecker_Env.qtbl_name_and_index
                                                                    =
                                                                    (uu___1929_14103.FStar_TypeChecker_Env.qtbl_name_and_index);
                                                                    FStar_TypeChecker_Env.normalized_eff_names
                                                                    =
                                                                    (uu___1929_14103.FStar_TypeChecker_Env.normalized_eff_names);
                                                                    FStar_TypeChecker_Env.fv_delta_depths
                                                                    =
                                                                    (uu___1929_14103.FStar_TypeChecker_Env.fv_delta_depths);
                                                                    FStar_TypeChecker_Env.proof_ns
                                                                    =
                                                                    (uu___1929_14103.FStar_TypeChecker_Env.proof_ns);
                                                                    FStar_TypeChecker_Env.synth_hook
                                                                    =
                                                                    (uu___1929_14103.FStar_TypeChecker_Env.synth_hook);
                                                                    FStar_TypeChecker_Env.try_solve_implicits_hook
                                                                    =
                                                                    (uu___1929_14103.FStar_TypeChecker_Env.try_solve_implicits_hook);
                                                                    FStar_TypeChecker_Env.splice
                                                                    =
                                                                    (uu___1929_14103.FStar_TypeChecker_Env.splice);
                                                                    FStar_TypeChecker_Env.mpreprocess
                                                                    =
                                                                    (uu___1929_14103.FStar_TypeChecker_Env.mpreprocess);
                                                                    FStar_TypeChecker_Env.postprocess
                                                                    =
                                                                    (uu___1929_14103.FStar_TypeChecker_Env.postprocess);
                                                                    FStar_TypeChecker_Env.is_native_tactic
                                                                    =
                                                                    (uu___1929_14103.FStar_TypeChecker_Env.is_native_tactic);
                                                                    FStar_TypeChecker_Env.identifier_info
                                                                    =
                                                                    (uu___1929_14103.FStar_TypeChecker_Env.identifier_info);
                                                                    FStar_TypeChecker_Env.tc_hooks
                                                                    =
                                                                    (uu___1929_14103.FStar_TypeChecker_Env.tc_hooks);
                                                                    FStar_TypeChecker_Env.dsenv
                                                                    =
                                                                    (uu___1929_14103.FStar_TypeChecker_Env.dsenv);
                                                                    FStar_TypeChecker_Env.nbe
                                                                    =
                                                                    (uu___1929_14103.FStar_TypeChecker_Env.nbe);
                                                                    FStar_TypeChecker_Env.strict_args_tab
                                                                    =
                                                                    (uu___1929_14103.FStar_TypeChecker_Env.strict_args_tab);
                                                                    FStar_TypeChecker_Env.erasable_types_tab
                                                                    =
                                                                    (uu___1929_14103.FStar_TypeChecker_Env.erasable_types_tab)
                                                                    }) s_ty1
                                                                    pat  in
                                                                    match uu____14079
                                                                    with
                                                                    | 
                                                                    (uu____14117,uu____14118,uu____14119,uu____14120,pat_t,uu____14122,_guard_pat,_erasable)
                                                                    ->
                                                                    let eq_b
                                                                    =
                                                                    let uu____14136
                                                                    =
                                                                    let uu____14137
                                                                    =
                                                                    FStar_Syntax_Util.mk_eq2
                                                                    equ s_ty1
                                                                    s_tm1
                                                                    pat_t  in
                                                                    FStar_Syntax_Util.mk_squash
                                                                    equ
                                                                    uu____14137
                                                                     in
                                                                    FStar_Syntax_Syntax.gen_bv
                                                                    "breq"
                                                                    FStar_Pervasives_Native.None
                                                                    uu____14136
                                                                     in
                                                                    let cod1
                                                                    =
                                                                    let uu____14142
                                                                    =
                                                                    let uu____14151
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_binder
                                                                    eq_b  in
                                                                    [uu____14151]
                                                                     in
                                                                    let uu____14170
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Total
                                                                    cod  in
                                                                    FStar_Syntax_Util.arrow
                                                                    uu____14142
                                                                    uu____14170
                                                                     in
                                                                    let nty =
                                                                    let uu____14176
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Total
                                                                    cod1  in
                                                                    FStar_Syntax_Util.arrow
                                                                    bs3
                                                                    uu____14176
                                                                     in
                                                                    let uu____14179
                                                                    =
                                                                    new_uvar
                                                                    "destruct branch"
                                                                    env nty
                                                                     in
                                                                    bind
                                                                    uu____14179
                                                                    (fun
                                                                    uu____14209
                                                                     ->
                                                                    match uu____14209
                                                                    with
                                                                    | 
                                                                    (uvt,uv)
                                                                    ->
                                                                    let g' =
                                                                    FStar_Tactics_Types.mk_goal
                                                                    env uv
                                                                    g.FStar_Tactics_Types.opts
                                                                    false
                                                                    g.FStar_Tactics_Types.label
                                                                     in
                                                                    let brt =
                                                                    FStar_Syntax_Util.mk_app_binders
                                                                    uvt bs3
                                                                     in
                                                                    let brt1
                                                                    =
                                                                    let uu____14236
                                                                    =
                                                                    let uu____14247
                                                                    =
                                                                    FStar_Syntax_Syntax.as_arg
                                                                    FStar_Syntax_Util.exp_unit
                                                                     in
                                                                    [uu____14247]
                                                                     in
                                                                    FStar_Syntax_Util.mk_app
                                                                    brt
                                                                    uu____14236
                                                                     in
                                                                    let br =
                                                                    FStar_Syntax_Subst.close_branch
                                                                    (pat,
                                                                    FStar_Pervasives_Native.None,
                                                                    brt1)  in
                                                                    let uu____14283
                                                                    =
                                                                    let uu____14294
                                                                    =
                                                                    let uu____14299
                                                                    =
                                                                    FStar_BigInt.of_int_fs
                                                                    (FStar_List.length
                                                                    bs3)  in
                                                                    (fv1,
                                                                    uu____14299)
                                                                     in
                                                                    (g', br,
                                                                    uu____14294)
                                                                     in
                                                                    ret
                                                                    uu____14283)))))))
                                                                    | 
                                                                    uu____14320
                                                                    ->
                                                                    fail
                                                                    "impossible: not a ctor"))
                                                                  c_lids
                                                                 in
                                                              bind
                                                                uu____13130
                                                                (fun goal_brs
                                                                    ->
                                                                   let uu____14370
                                                                    =
                                                                    FStar_List.unzip3
                                                                    goal_brs
                                                                     in
                                                                   match uu____14370
                                                                   with
                                                                   | 
                                                                   (goals,brs,infos)
                                                                    ->
                                                                    let w =
                                                                    FStar_Syntax_Syntax.mk
                                                                    (FStar_Syntax_Syntax.Tm_match
                                                                    (s_tm1,
                                                                    brs))
                                                                    FStar_Pervasives_Native.None
                                                                    s_tm1.FStar_Syntax_Syntax.pos
                                                                     in
                                                                    let uu____14443
                                                                    =
                                                                    solve' g
                                                                    w  in
                                                                    bind
                                                                    uu____14443
                                                                    (fun
                                                                    uu____14454
                                                                     ->
                                                                    let uu____14455
                                                                    =
                                                                    add_goals
                                                                    goals  in
                                                                    bind
                                                                    uu____14455
                                                                    (fun
                                                                    uu____14465
                                                                     ->
                                                                    ret infos)))))
                                            | uu____14472 ->
                                                fail "not an inductive type"))))))
       in
    FStar_All.pipe_left (wrap_err "destruct") uu____12842
  
let rec last : 'a . 'a Prims.list -> 'a =
  fun l  ->
    match l with
    | [] -> failwith "last: empty list"
    | x::[] -> x
    | uu____14521::xs -> last xs
  
let rec init : 'a . 'a Prims.list -> 'a Prims.list =
  fun l  ->
    match l with
    | [] -> failwith "init: empty list"
    | x::[] -> []
    | x::xs -> let uu____14551 = init xs  in x :: uu____14551
  
let rec (inspect :
  FStar_Syntax_Syntax.term -> FStar_Reflection_Data.term_view tac) =
  fun t  ->
    let uu____14564 =
      let t1 = FStar_Syntax_Util.unascribe t  in
      let t2 = FStar_Syntax_Util.un_uinst t1  in
      let t3 = FStar_Syntax_Util.unlazy_emb t2  in
      match t3.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_meta (t4,uu____14573) -> inspect t4
      | FStar_Syntax_Syntax.Tm_name bv ->
          FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_Var bv)
      | FStar_Syntax_Syntax.Tm_bvar bv ->
          FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_BVar bv)
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_FVar fv)
      | FStar_Syntax_Syntax.Tm_app (hd1,[]) ->
          failwith "empty arguments on Tm_app"
      | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
          let uu____14639 = last args  in
          (match uu____14639 with
           | (a,q) ->
               let q' = FStar_Reflection_Basic.inspect_aqual q  in
               let uu____14669 =
                 let uu____14670 =
                   let uu____14675 =
                     let uu____14676 =
                       let uu____14681 = init args  in
                       FStar_Syntax_Syntax.mk_Tm_app hd1 uu____14681  in
                     uu____14676 FStar_Pervasives_Native.None
                       t3.FStar_Syntax_Syntax.pos
                      in
                   (uu____14675, (a, q'))  in
                 FStar_Reflection_Data.Tv_App uu____14670  in
               FStar_All.pipe_left ret uu____14669)
      | FStar_Syntax_Syntax.Tm_abs ([],uu____14692,uu____14693) ->
          failwith "empty arguments on Tm_abs"
      | FStar_Syntax_Syntax.Tm_abs (bs,t4,k) ->
          let uu____14746 = FStar_Syntax_Subst.open_term bs t4  in
          (match uu____14746 with
           | (bs1,t5) ->
               (match bs1 with
                | [] -> failwith "impossible"
                | b::bs2 ->
                    let uu____14788 =
                      let uu____14789 =
                        let uu____14794 = FStar_Syntax_Util.abs bs2 t5 k  in
                        (b, uu____14794)  in
                      FStar_Reflection_Data.Tv_Abs uu____14789  in
                    FStar_All.pipe_left ret uu____14788))
      | FStar_Syntax_Syntax.Tm_type uu____14797 ->
          FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_Type ())
      | FStar_Syntax_Syntax.Tm_arrow ([],k) ->
          failwith "empty binders on arrow"
      | FStar_Syntax_Syntax.Tm_arrow uu____14822 ->
          let uu____14837 = FStar_Syntax_Util.arrow_one t3  in
          (match uu____14837 with
           | FStar_Pervasives_Native.Some (b,c) ->
               FStar_All.pipe_left ret
                 (FStar_Reflection_Data.Tv_Arrow (b, c))
           | FStar_Pervasives_Native.None  -> failwith "impossible")
      | FStar_Syntax_Syntax.Tm_refine (bv,t4) ->
          let b = FStar_Syntax_Syntax.mk_binder bv  in
          let uu____14868 = FStar_Syntax_Subst.open_term [b] t4  in
          (match uu____14868 with
           | (b',t5) ->
               let b1 =
                 match b' with
                 | b'1::[] -> b'1
                 | uu____14921 -> failwith "impossible"  in
               FStar_All.pipe_left ret
                 (FStar_Reflection_Data.Tv_Refine
                    ((FStar_Pervasives_Native.fst b1), t5)))
      | FStar_Syntax_Syntax.Tm_constant c ->
          let uu____14934 =
            let uu____14935 = FStar_Reflection_Basic.inspect_const c  in
            FStar_Reflection_Data.Tv_Const uu____14935  in
          FStar_All.pipe_left ret uu____14934
      | FStar_Syntax_Syntax.Tm_uvar (ctx_u,s) ->
          let uu____14956 =
            let uu____14957 =
              let uu____14962 =
                let uu____14963 =
                  FStar_Syntax_Unionfind.uvar_id
                    ctx_u.FStar_Syntax_Syntax.ctx_uvar_head
                   in
                FStar_BigInt.of_int_fs uu____14963  in
              (uu____14962, (ctx_u, s))  in
            FStar_Reflection_Data.Tv_Uvar uu____14957  in
          FStar_All.pipe_left ret uu____14956
      | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),t21) ->
          if lb.FStar_Syntax_Syntax.lbunivs <> []
          then FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown
          else
            (match lb.FStar_Syntax_Syntax.lbname with
             | FStar_Util.Inr uu____15003 ->
                 FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown
             | FStar_Util.Inl bv ->
                 let b = FStar_Syntax_Syntax.mk_binder bv  in
                 let uu____15008 = FStar_Syntax_Subst.open_term [b] t21  in
                 (match uu____15008 with
                  | (bs,t22) ->
                      let b1 =
                        match bs with
                        | b1::[] -> b1
                        | uu____15061 ->
                            failwith
                              "impossible: open_term returned different amount of binders"
                         in
                      FStar_All.pipe_left ret
                        (FStar_Reflection_Data.Tv_Let
                           (false, (lb.FStar_Syntax_Syntax.lbattrs),
                             (FStar_Pervasives_Native.fst b1),
                             (lb.FStar_Syntax_Syntax.lbdef), t22))))
      | FStar_Syntax_Syntax.Tm_let ((true ,lb::[]),t21) ->
          if lb.FStar_Syntax_Syntax.lbunivs <> []
          then FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown
          else
            (match lb.FStar_Syntax_Syntax.lbname with
             | FStar_Util.Inr uu____15105 ->
                 FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown
             | FStar_Util.Inl bv ->
                 let uu____15109 = FStar_Syntax_Subst.open_let_rec [lb] t21
                    in
                 (match uu____15109 with
                  | (lbs,t22) ->
                      (match lbs with
                       | lb1::[] ->
                           (match lb1.FStar_Syntax_Syntax.lbname with
                            | FStar_Util.Inr uu____15129 ->
                                ret FStar_Reflection_Data.Tv_Unknown
                            | FStar_Util.Inl bv1 ->
                                FStar_All.pipe_left ret
                                  (FStar_Reflection_Data.Tv_Let
                                     (true,
                                       (lb1.FStar_Syntax_Syntax.lbattrs),
                                       bv1, (lb1.FStar_Syntax_Syntax.lbdef),
                                       t22)))
                       | uu____15137 ->
                           failwith
                             "impossible: open_term returned different amount of binders")))
      | FStar_Syntax_Syntax.Tm_match (t4,brs) ->
          let rec inspect_pat p =
            match p.FStar_Syntax_Syntax.v with
            | FStar_Syntax_Syntax.Pat_constant c ->
                let uu____15192 = FStar_Reflection_Basic.inspect_const c  in
                FStar_Reflection_Data.Pat_Constant uu____15192
            | FStar_Syntax_Syntax.Pat_cons (fv,ps) ->
                let uu____15213 =
                  let uu____15225 =
                    FStar_List.map
                      (fun uu____15249  ->
                         match uu____15249 with
                         | (p1,b) ->
                             let uu____15270 = inspect_pat p1  in
                             (uu____15270, b)) ps
                     in
                  (fv, uu____15225)  in
                FStar_Reflection_Data.Pat_Cons uu____15213
            | FStar_Syntax_Syntax.Pat_var bv ->
                FStar_Reflection_Data.Pat_Var bv
            | FStar_Syntax_Syntax.Pat_wild bv ->
                FStar_Reflection_Data.Pat_Wild bv
            | FStar_Syntax_Syntax.Pat_dot_term (bv,t5) ->
                FStar_Reflection_Data.Pat_Dot_Term (bv, t5)
             in
          let brs1 = FStar_List.map FStar_Syntax_Subst.open_branch brs  in
          let brs2 =
            FStar_List.map
              (fun uu___7_15366  ->
                 match uu___7_15366 with
                 | (pat,uu____15388,t5) ->
                     let uu____15406 = inspect_pat pat  in (uu____15406, t5))
              brs1
             in
          FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_Match (t4, brs2))
      | FStar_Syntax_Syntax.Tm_unknown  ->
          FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown
      | uu____15415 ->
          ((let uu____15417 =
              let uu____15423 =
                let uu____15425 = FStar_Syntax_Print.tag_of_term t3  in
                let uu____15427 = FStar_Syntax_Print.term_to_string t3  in
                FStar_Util.format2
                  "inspect: outside of expected syntax (%s, %s)\n"
                  uu____15425 uu____15427
                 in
              (FStar_Errors.Warning_CantInspect, uu____15423)  in
            FStar_Errors.log_issue t3.FStar_Syntax_Syntax.pos uu____15417);
           FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown)
       in
    wrap_err "inspect" uu____14564
  
let (pack : FStar_Reflection_Data.term_view -> FStar_Syntax_Syntax.term tac)
  =
  fun tv  ->
    match tv with
    | FStar_Reflection_Data.Tv_Var bv ->
        let uu____15445 = FStar_Syntax_Syntax.bv_to_name bv  in
        FStar_All.pipe_left ret uu____15445
    | FStar_Reflection_Data.Tv_BVar bv ->
        let uu____15449 = FStar_Syntax_Syntax.bv_to_tm bv  in
        FStar_All.pipe_left ret uu____15449
    | FStar_Reflection_Data.Tv_FVar fv ->
        let uu____15453 = FStar_Syntax_Syntax.fv_to_tm fv  in
        FStar_All.pipe_left ret uu____15453
    | FStar_Reflection_Data.Tv_App (l,(r,q)) ->
        let q' = FStar_Reflection_Basic.pack_aqual q  in
        let uu____15460 = FStar_Syntax_Util.mk_app l [(r, q')]  in
        FStar_All.pipe_left ret uu____15460
    | FStar_Reflection_Data.Tv_Abs (b,t) ->
        let uu____15485 =
          FStar_Syntax_Util.abs [b] t FStar_Pervasives_Native.None  in
        FStar_All.pipe_left ret uu____15485
    | FStar_Reflection_Data.Tv_Arrow (b,c) ->
        let uu____15502 = FStar_Syntax_Util.arrow [b] c  in
        FStar_All.pipe_left ret uu____15502
    | FStar_Reflection_Data.Tv_Type () ->
        FStar_All.pipe_left ret FStar_Syntax_Util.ktype
    | FStar_Reflection_Data.Tv_Refine (bv,t) ->
        let uu____15521 = FStar_Syntax_Util.refine bv t  in
        FStar_All.pipe_left ret uu____15521
    | FStar_Reflection_Data.Tv_Const c ->
        let uu____15525 =
          let uu____15526 =
            let uu____15533 =
              let uu____15534 = FStar_Reflection_Basic.pack_const c  in
              FStar_Syntax_Syntax.Tm_constant uu____15534  in
            FStar_Syntax_Syntax.mk uu____15533  in
          uu____15526 FStar_Pervasives_Native.None FStar_Range.dummyRange  in
        FStar_All.pipe_left ret uu____15525
    | FStar_Reflection_Data.Tv_Uvar (_u,ctx_u_s) ->
        let uu____15539 =
          FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_uvar ctx_u_s)
            FStar_Pervasives_Native.None FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____15539
    | FStar_Reflection_Data.Tv_Let (false ,attrs,bv,t1,t2) ->
        let lb =
          FStar_Syntax_Util.mk_letbinding (FStar_Util.Inl bv) []
            bv.FStar_Syntax_Syntax.sort FStar_Parser_Const.effect_Tot_lid t1
            attrs FStar_Range.dummyRange
           in
        let uu____15553 =
          let uu____15554 =
            let uu____15561 =
              let uu____15562 =
                let uu____15576 =
                  let uu____15579 =
                    let uu____15580 = FStar_Syntax_Syntax.mk_binder bv  in
                    [uu____15580]  in
                  FStar_Syntax_Subst.close uu____15579 t2  in
                ((false, [lb]), uu____15576)  in
              FStar_Syntax_Syntax.Tm_let uu____15562  in
            FStar_Syntax_Syntax.mk uu____15561  in
          uu____15554 FStar_Pervasives_Native.None FStar_Range.dummyRange  in
        FStar_All.pipe_left ret uu____15553
    | FStar_Reflection_Data.Tv_Let (true ,attrs,bv,t1,t2) ->
        let lb =
          FStar_Syntax_Util.mk_letbinding (FStar_Util.Inl bv) []
            bv.FStar_Syntax_Syntax.sort FStar_Parser_Const.effect_Tot_lid t1
            attrs FStar_Range.dummyRange
           in
        let uu____15625 = FStar_Syntax_Subst.close_let_rec [lb] t2  in
        (match uu____15625 with
         | (lbs,body) ->
             let uu____15640 =
               FStar_Syntax_Syntax.mk
                 (FStar_Syntax_Syntax.Tm_let ((true, lbs), body))
                 FStar_Pervasives_Native.None FStar_Range.dummyRange
                in
             FStar_All.pipe_left ret uu____15640)
    | FStar_Reflection_Data.Tv_Match (t,brs) ->
        let wrap v1 =
          {
            FStar_Syntax_Syntax.v = v1;
            FStar_Syntax_Syntax.p = FStar_Range.dummyRange
          }  in
        let rec pack_pat p =
          match p with
          | FStar_Reflection_Data.Pat_Constant c ->
              let uu____15677 =
                let uu____15678 = FStar_Reflection_Basic.pack_const c  in
                FStar_Syntax_Syntax.Pat_constant uu____15678  in
              FStar_All.pipe_left wrap uu____15677
          | FStar_Reflection_Data.Pat_Cons (fv,ps) ->
              let uu____15695 =
                let uu____15696 =
                  let uu____15710 =
                    FStar_List.map
                      (fun uu____15734  ->
                         match uu____15734 with
                         | (p1,b) ->
                             let uu____15749 = pack_pat p1  in
                             (uu____15749, b)) ps
                     in
                  (fv, uu____15710)  in
                FStar_Syntax_Syntax.Pat_cons uu____15696  in
              FStar_All.pipe_left wrap uu____15695
          | FStar_Reflection_Data.Pat_Var bv ->
              FStar_All.pipe_left wrap (FStar_Syntax_Syntax.Pat_var bv)
          | FStar_Reflection_Data.Pat_Wild bv ->
              FStar_All.pipe_left wrap (FStar_Syntax_Syntax.Pat_wild bv)
          | FStar_Reflection_Data.Pat_Dot_Term (bv,t1) ->
              FStar_All.pipe_left wrap
                (FStar_Syntax_Syntax.Pat_dot_term (bv, t1))
           in
        let brs1 =
          FStar_List.map
            (fun uu___8_15797  ->
               match uu___8_15797 with
               | (pat,t1) ->
                   let uu____15814 = pack_pat pat  in
                   (uu____15814, FStar_Pervasives_Native.None, t1)) brs
           in
        let brs2 = FStar_List.map FStar_Syntax_Subst.close_branch brs1  in
        let uu____15862 =
          FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_match (t, brs2))
            FStar_Pervasives_Native.None FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____15862
    | FStar_Reflection_Data.Tv_AscribedT (e,t,tacopt) ->
        let uu____15890 =
          FStar_Syntax_Syntax.mk
            (FStar_Syntax_Syntax.Tm_ascribed
               (e, ((FStar_Util.Inl t), tacopt),
                 FStar_Pervasives_Native.None)) FStar_Pervasives_Native.None
            FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____15890
    | FStar_Reflection_Data.Tv_AscribedC (e,c,tacopt) ->
        let uu____15936 =
          FStar_Syntax_Syntax.mk
            (FStar_Syntax_Syntax.Tm_ascribed
               (e, ((FStar_Util.Inr c), tacopt),
                 FStar_Pervasives_Native.None)) FStar_Pervasives_Native.None
            FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____15936
    | FStar_Reflection_Data.Tv_Unknown  ->
        let uu____15975 =
          FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown
            FStar_Pervasives_Native.None FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____15975
  
let (lget :
  FStar_Reflection_Data.typ -> Prims.string -> FStar_Syntax_Syntax.term tac)
  =
  fun ty  ->
    fun k  ->
      let uu____15995 =
        bind get
          (fun ps  ->
             let uu____16001 =
               FStar_Util.psmap_try_find ps.FStar_Tactics_Types.local_state k
                in
             match uu____16001 with
             | FStar_Pervasives_Native.None  -> fail "not found"
             | FStar_Pervasives_Native.Some t -> unquote ty t)
         in
      FStar_All.pipe_left (wrap_err "lget") uu____15995
  
let (lset :
  FStar_Reflection_Data.typ ->
    Prims.string -> FStar_Syntax_Syntax.term -> unit tac)
  =
  fun _ty  ->
    fun k  ->
      fun t  ->
        let uu____16035 =
          bind get
            (fun ps  ->
               let ps1 =
                 let uu___2233_16042 = ps  in
                 let uu____16043 =
                   FStar_Util.psmap_add ps.FStar_Tactics_Types.local_state k
                     t
                    in
                 {
                   FStar_Tactics_Types.main_context =
                     (uu___2233_16042.FStar_Tactics_Types.main_context);
                   FStar_Tactics_Types.all_implicits =
                     (uu___2233_16042.FStar_Tactics_Types.all_implicits);
                   FStar_Tactics_Types.goals =
                     (uu___2233_16042.FStar_Tactics_Types.goals);
                   FStar_Tactics_Types.smt_goals =
                     (uu___2233_16042.FStar_Tactics_Types.smt_goals);
                   FStar_Tactics_Types.depth =
                     (uu___2233_16042.FStar_Tactics_Types.depth);
                   FStar_Tactics_Types.__dump =
                     (uu___2233_16042.FStar_Tactics_Types.__dump);
                   FStar_Tactics_Types.psc =
                     (uu___2233_16042.FStar_Tactics_Types.psc);
                   FStar_Tactics_Types.entry_range =
                     (uu___2233_16042.FStar_Tactics_Types.entry_range);
                   FStar_Tactics_Types.guard_policy =
                     (uu___2233_16042.FStar_Tactics_Types.guard_policy);
                   FStar_Tactics_Types.freshness =
                     (uu___2233_16042.FStar_Tactics_Types.freshness);
                   FStar_Tactics_Types.tac_verb_dbg =
                     (uu___2233_16042.FStar_Tactics_Types.tac_verb_dbg);
                   FStar_Tactics_Types.local_state = uu____16043
                 }  in
               set ps1)
           in
        FStar_All.pipe_left (wrap_err "lset") uu____16035
  
let (goal_of_goal_ty :
  env ->
    FStar_Reflection_Data.typ ->
      (FStar_Tactics_Types.goal * FStar_TypeChecker_Common.guard_t))
  =
  fun env  ->
    fun typ  ->
      let uu____16070 =
        FStar_TypeChecker_Util.new_implicit_var "proofstate_of_goal_ty"
          typ.FStar_Syntax_Syntax.pos env typ
         in
      match uu____16070 with
      | (u,ctx_uvars,g_u) ->
          let uu____16103 = FStar_List.hd ctx_uvars  in
          (match uu____16103 with
           | (ctx_uvar,uu____16117) ->
               let g =
                 let uu____16119 = FStar_Options.peek ()  in
                 FStar_Tactics_Types.mk_goal env ctx_uvar uu____16119 false
                   ""
                  in
               (g, g_u))
  
let (tac_env : FStar_TypeChecker_Env.env -> FStar_TypeChecker_Env.env) =
  fun env  ->
    let uu____16128 = FStar_TypeChecker_Env.clear_expected_typ env  in
    match uu____16128 with
    | (env1,uu____16136) ->
        let env2 =
          let uu___2250_16142 = env1  in
          {
            FStar_TypeChecker_Env.solver =
              (uu___2250_16142.FStar_TypeChecker_Env.solver);
            FStar_TypeChecker_Env.range =
              (uu___2250_16142.FStar_TypeChecker_Env.range);
            FStar_TypeChecker_Env.curmodule =
              (uu___2250_16142.FStar_TypeChecker_Env.curmodule);
            FStar_TypeChecker_Env.gamma =
              (uu___2250_16142.FStar_TypeChecker_Env.gamma);
            FStar_TypeChecker_Env.gamma_sig =
              (uu___2250_16142.FStar_TypeChecker_Env.gamma_sig);
            FStar_TypeChecker_Env.gamma_cache =
              (uu___2250_16142.FStar_TypeChecker_Env.gamma_cache);
            FStar_TypeChecker_Env.modules =
              (uu___2250_16142.FStar_TypeChecker_Env.modules);
            FStar_TypeChecker_Env.expected_typ =
              (uu___2250_16142.FStar_TypeChecker_Env.expected_typ);
            FStar_TypeChecker_Env.sigtab =
              (uu___2250_16142.FStar_TypeChecker_Env.sigtab);
            FStar_TypeChecker_Env.attrtab =
              (uu___2250_16142.FStar_TypeChecker_Env.attrtab);
            FStar_TypeChecker_Env.instantiate_imp = false;
            FStar_TypeChecker_Env.effects =
              (uu___2250_16142.FStar_TypeChecker_Env.effects);
            FStar_TypeChecker_Env.generalize =
              (uu___2250_16142.FStar_TypeChecker_Env.generalize);
            FStar_TypeChecker_Env.letrecs =
              (uu___2250_16142.FStar_TypeChecker_Env.letrecs);
            FStar_TypeChecker_Env.top_level =
              (uu___2250_16142.FStar_TypeChecker_Env.top_level);
            FStar_TypeChecker_Env.check_uvars =
              (uu___2250_16142.FStar_TypeChecker_Env.check_uvars);
            FStar_TypeChecker_Env.use_eq =
              (uu___2250_16142.FStar_TypeChecker_Env.use_eq);
            FStar_TypeChecker_Env.use_eq_strict =
              (uu___2250_16142.FStar_TypeChecker_Env.use_eq_strict);
            FStar_TypeChecker_Env.is_iface =
              (uu___2250_16142.FStar_TypeChecker_Env.is_iface);
            FStar_TypeChecker_Env.admit =
              (uu___2250_16142.FStar_TypeChecker_Env.admit);
            FStar_TypeChecker_Env.lax =
              (uu___2250_16142.FStar_TypeChecker_Env.lax);
            FStar_TypeChecker_Env.lax_universes =
              (uu___2250_16142.FStar_TypeChecker_Env.lax_universes);
            FStar_TypeChecker_Env.phase1 =
              (uu___2250_16142.FStar_TypeChecker_Env.phase1);
            FStar_TypeChecker_Env.failhard =
              (uu___2250_16142.FStar_TypeChecker_Env.failhard);
            FStar_TypeChecker_Env.nosynth =
              (uu___2250_16142.FStar_TypeChecker_Env.nosynth);
            FStar_TypeChecker_Env.uvar_subtyping =
              (uu___2250_16142.FStar_TypeChecker_Env.uvar_subtyping);
            FStar_TypeChecker_Env.tc_term =
              (uu___2250_16142.FStar_TypeChecker_Env.tc_term);
            FStar_TypeChecker_Env.type_of =
              (uu___2250_16142.FStar_TypeChecker_Env.type_of);
            FStar_TypeChecker_Env.universe_of =
              (uu___2250_16142.FStar_TypeChecker_Env.universe_of);
            FStar_TypeChecker_Env.check_type_of =
              (uu___2250_16142.FStar_TypeChecker_Env.check_type_of);
            FStar_TypeChecker_Env.use_bv_sorts =
              (uu___2250_16142.FStar_TypeChecker_Env.use_bv_sorts);
            FStar_TypeChecker_Env.qtbl_name_and_index =
              (uu___2250_16142.FStar_TypeChecker_Env.qtbl_name_and_index);
            FStar_TypeChecker_Env.normalized_eff_names =
              (uu___2250_16142.FStar_TypeChecker_Env.normalized_eff_names);
            FStar_TypeChecker_Env.fv_delta_depths =
              (uu___2250_16142.FStar_TypeChecker_Env.fv_delta_depths);
            FStar_TypeChecker_Env.proof_ns =
              (uu___2250_16142.FStar_TypeChecker_Env.proof_ns);
            FStar_TypeChecker_Env.synth_hook =
              (uu___2250_16142.FStar_TypeChecker_Env.synth_hook);
            FStar_TypeChecker_Env.try_solve_implicits_hook =
              (uu___2250_16142.FStar_TypeChecker_Env.try_solve_implicits_hook);
            FStar_TypeChecker_Env.splice =
              (uu___2250_16142.FStar_TypeChecker_Env.splice);
            FStar_TypeChecker_Env.mpreprocess =
              (uu___2250_16142.FStar_TypeChecker_Env.mpreprocess);
            FStar_TypeChecker_Env.postprocess =
              (uu___2250_16142.FStar_TypeChecker_Env.postprocess);
            FStar_TypeChecker_Env.is_native_tactic =
              (uu___2250_16142.FStar_TypeChecker_Env.is_native_tactic);
            FStar_TypeChecker_Env.identifier_info =
              (uu___2250_16142.FStar_TypeChecker_Env.identifier_info);
            FStar_TypeChecker_Env.tc_hooks =
              (uu___2250_16142.FStar_TypeChecker_Env.tc_hooks);
            FStar_TypeChecker_Env.dsenv =
              (uu___2250_16142.FStar_TypeChecker_Env.dsenv);
            FStar_TypeChecker_Env.nbe =
              (uu___2250_16142.FStar_TypeChecker_Env.nbe);
            FStar_TypeChecker_Env.strict_args_tab =
              (uu___2250_16142.FStar_TypeChecker_Env.strict_args_tab);
            FStar_TypeChecker_Env.erasable_types_tab =
              (uu___2250_16142.FStar_TypeChecker_Env.erasable_types_tab)
          }  in
        let env3 =
          let uu___2253_16145 = env2  in
          {
            FStar_TypeChecker_Env.solver =
              (uu___2253_16145.FStar_TypeChecker_Env.solver);
            FStar_TypeChecker_Env.range =
              (uu___2253_16145.FStar_TypeChecker_Env.range);
            FStar_TypeChecker_Env.curmodule =
              (uu___2253_16145.FStar_TypeChecker_Env.curmodule);
            FStar_TypeChecker_Env.gamma =
              (uu___2253_16145.FStar_TypeChecker_Env.gamma);
            FStar_TypeChecker_Env.gamma_sig =
              (uu___2253_16145.FStar_TypeChecker_Env.gamma_sig);
            FStar_TypeChecker_Env.gamma_cache =
              (uu___2253_16145.FStar_TypeChecker_Env.gamma_cache);
            FStar_TypeChecker_Env.modules =
              (uu___2253_16145.FStar_TypeChecker_Env.modules);
            FStar_TypeChecker_Env.expected_typ =
              (uu___2253_16145.FStar_TypeChecker_Env.expected_typ);
            FStar_TypeChecker_Env.sigtab =
              (uu___2253_16145.FStar_TypeChecker_Env.sigtab);
            FStar_TypeChecker_Env.attrtab =
              (uu___2253_16145.FStar_TypeChecker_Env.attrtab);
            FStar_TypeChecker_Env.instantiate_imp =
              (uu___2253_16145.FStar_TypeChecker_Env.instantiate_imp);
            FStar_TypeChecker_Env.effects =
              (uu___2253_16145.FStar_TypeChecker_Env.effects);
            FStar_TypeChecker_Env.generalize =
              (uu___2253_16145.FStar_TypeChecker_Env.generalize);
            FStar_TypeChecker_Env.letrecs =
              (uu___2253_16145.FStar_TypeChecker_Env.letrecs);
            FStar_TypeChecker_Env.top_level =
              (uu___2253_16145.FStar_TypeChecker_Env.top_level);
            FStar_TypeChecker_Env.check_uvars =
              (uu___2253_16145.FStar_TypeChecker_Env.check_uvars);
            FStar_TypeChecker_Env.use_eq =
              (uu___2253_16145.FStar_TypeChecker_Env.use_eq);
            FStar_TypeChecker_Env.use_eq_strict =
              (uu___2253_16145.FStar_TypeChecker_Env.use_eq_strict);
            FStar_TypeChecker_Env.is_iface =
              (uu___2253_16145.FStar_TypeChecker_Env.is_iface);
            FStar_TypeChecker_Env.admit =
              (uu___2253_16145.FStar_TypeChecker_Env.admit);
            FStar_TypeChecker_Env.lax =
              (uu___2253_16145.FStar_TypeChecker_Env.lax);
            FStar_TypeChecker_Env.lax_universes =
              (uu___2253_16145.FStar_TypeChecker_Env.lax_universes);
            FStar_TypeChecker_Env.phase1 =
              (uu___2253_16145.FStar_TypeChecker_Env.phase1);
            FStar_TypeChecker_Env.failhard = true;
            FStar_TypeChecker_Env.nosynth =
              (uu___2253_16145.FStar_TypeChecker_Env.nosynth);
            FStar_TypeChecker_Env.uvar_subtyping =
              (uu___2253_16145.FStar_TypeChecker_Env.uvar_subtyping);
            FStar_TypeChecker_Env.tc_term =
              (uu___2253_16145.FStar_TypeChecker_Env.tc_term);
            FStar_TypeChecker_Env.type_of =
              (uu___2253_16145.FStar_TypeChecker_Env.type_of);
            FStar_TypeChecker_Env.universe_of =
              (uu___2253_16145.FStar_TypeChecker_Env.universe_of);
            FStar_TypeChecker_Env.check_type_of =
              (uu___2253_16145.FStar_TypeChecker_Env.check_type_of);
            FStar_TypeChecker_Env.use_bv_sorts =
              (uu___2253_16145.FStar_TypeChecker_Env.use_bv_sorts);
            FStar_TypeChecker_Env.qtbl_name_and_index =
              (uu___2253_16145.FStar_TypeChecker_Env.qtbl_name_and_index);
            FStar_TypeChecker_Env.normalized_eff_names =
              (uu___2253_16145.FStar_TypeChecker_Env.normalized_eff_names);
            FStar_TypeChecker_Env.fv_delta_depths =
              (uu___2253_16145.FStar_TypeChecker_Env.fv_delta_depths);
            FStar_TypeChecker_Env.proof_ns =
              (uu___2253_16145.FStar_TypeChecker_Env.proof_ns);
            FStar_TypeChecker_Env.synth_hook =
              (uu___2253_16145.FStar_TypeChecker_Env.synth_hook);
            FStar_TypeChecker_Env.try_solve_implicits_hook =
              (uu___2253_16145.FStar_TypeChecker_Env.try_solve_implicits_hook);
            FStar_TypeChecker_Env.splice =
              (uu___2253_16145.FStar_TypeChecker_Env.splice);
            FStar_TypeChecker_Env.mpreprocess =
              (uu___2253_16145.FStar_TypeChecker_Env.mpreprocess);
            FStar_TypeChecker_Env.postprocess =
              (uu___2253_16145.FStar_TypeChecker_Env.postprocess);
            FStar_TypeChecker_Env.is_native_tactic =
              (uu___2253_16145.FStar_TypeChecker_Env.is_native_tactic);
            FStar_TypeChecker_Env.identifier_info =
              (uu___2253_16145.FStar_TypeChecker_Env.identifier_info);
            FStar_TypeChecker_Env.tc_hooks =
              (uu___2253_16145.FStar_TypeChecker_Env.tc_hooks);
            FStar_TypeChecker_Env.dsenv =
              (uu___2253_16145.FStar_TypeChecker_Env.dsenv);
            FStar_TypeChecker_Env.nbe =
              (uu___2253_16145.FStar_TypeChecker_Env.nbe);
            FStar_TypeChecker_Env.strict_args_tab =
              (uu___2253_16145.FStar_TypeChecker_Env.strict_args_tab);
            FStar_TypeChecker_Env.erasable_types_tab =
              (uu___2253_16145.FStar_TypeChecker_Env.erasable_types_tab)
          }  in
        env3
  
let (proofstate_of_goals :
  FStar_Range.range ->
    env ->
      FStar_Tactics_Types.goal Prims.list ->
        FStar_TypeChecker_Common.implicit Prims.list ->
          FStar_Tactics_Types.proofstate)
  =
  fun rng  ->
    fun env  ->
      fun goals  ->
        fun imps  ->
          let env1 = tac_env env  in
          let ps =
            let uu____16178 =
              FStar_TypeChecker_Env.debug env1
                (FStar_Options.Other "TacVerbose")
               in
            let uu____16181 = FStar_Util.psmap_empty ()  in
            {
              FStar_Tactics_Types.main_context = env1;
              FStar_Tactics_Types.all_implicits = imps;
              FStar_Tactics_Types.goals = goals;
              FStar_Tactics_Types.smt_goals = [];
              FStar_Tactics_Types.depth = Prims.int_zero;
              FStar_Tactics_Types.__dump = do_dump_proofstate;
              FStar_Tactics_Types.psc = FStar_TypeChecker_Cfg.null_psc;
              FStar_Tactics_Types.entry_range = rng;
              FStar_Tactics_Types.guard_policy = FStar_Tactics_Types.SMT;
              FStar_Tactics_Types.freshness = Prims.int_zero;
              FStar_Tactics_Types.tac_verb_dbg = uu____16178;
              FStar_Tactics_Types.local_state = uu____16181
            }  in
          ps
  
let (proofstate_of_goal_ty :
  FStar_Range.range ->
    env ->
      FStar_Reflection_Data.typ ->
        (FStar_Tactics_Types.proofstate * FStar_Syntax_Syntax.term))
  =
  fun rng  ->
    fun env  ->
      fun typ  ->
        let env1 = tac_env env  in
        let uu____16207 = goal_of_goal_ty env1 typ  in
        match uu____16207 with
        | (g,g_u) ->
            let ps =
              proofstate_of_goals rng env1 [g]
                g_u.FStar_TypeChecker_Common.implicits
               in
            let uu____16219 = FStar_Tactics_Types.goal_witness g  in
            (ps, uu____16219)
  
let (goal_of_implicit :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Env.implicit -> FStar_Tactics_Types.goal)
  =
  fun env  ->
    fun i  ->
      let uu____16231 = FStar_Options.peek ()  in
      FStar_Tactics_Types.mk_goal env i.FStar_TypeChecker_Common.imp_uvar
        uu____16231 false ""
  
let (proofstate_of_all_implicits :
  FStar_Range.range ->
    env ->
      implicits ->
        (FStar_Tactics_Types.proofstate * FStar_Syntax_Syntax.term))
  =
  fun rng  ->
    fun env  ->
      fun imps  ->
        let goals = FStar_List.map (goal_of_implicit env) imps  in
        let w =
          let uu____16258 = FStar_List.hd goals  in
          FStar_Tactics_Types.goal_witness uu____16258  in
        let ps =
          let uu____16260 =
            FStar_TypeChecker_Env.debug env
              (FStar_Options.Other "TacVerbose")
             in
          let uu____16263 = FStar_Util.psmap_empty ()  in
          {
            FStar_Tactics_Types.main_context = env;
            FStar_Tactics_Types.all_implicits = imps;
            FStar_Tactics_Types.goals = goals;
            FStar_Tactics_Types.smt_goals = [];
            FStar_Tactics_Types.depth = Prims.int_zero;
            FStar_Tactics_Types.__dump =
              (fun ps  -> fun msg  -> do_dump_proofstate ps msg);
            FStar_Tactics_Types.psc = FStar_TypeChecker_Cfg.null_psc;
            FStar_Tactics_Types.entry_range = rng;
            FStar_Tactics_Types.guard_policy = FStar_Tactics_Types.SMT;
            FStar_Tactics_Types.freshness = Prims.int_zero;
            FStar_Tactics_Types.tac_verb_dbg = uu____16260;
            FStar_Tactics_Types.local_state = uu____16263
          }  in
        (ps, w)
  