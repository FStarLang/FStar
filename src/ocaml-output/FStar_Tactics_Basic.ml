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
        (try (fun uu___33_170  -> match () with | () -> run t p) ()
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
                 let uu___232_1717 = ps  in
                 {
                   FStar_Tactics_Types.main_context =
                     (uu___232_1717.FStar_Tactics_Types.main_context);
                   FStar_Tactics_Types.all_implicits =
                     (uu___232_1717.FStar_Tactics_Types.all_implicits);
                   FStar_Tactics_Types.goals =
                     (uu___232_1717.FStar_Tactics_Types.goals);
                   FStar_Tactics_Types.smt_goals =
                     (uu___232_1717.FStar_Tactics_Types.smt_goals);
                   FStar_Tactics_Types.depth =
                     (uu___232_1717.FStar_Tactics_Types.depth);
                   FStar_Tactics_Types.__dump =
                     (uu___232_1717.FStar_Tactics_Types.__dump);
                   FStar_Tactics_Types.psc =
                     (uu___232_1717.FStar_Tactics_Types.psc);
                   FStar_Tactics_Types.entry_range =
                     (uu___232_1717.FStar_Tactics_Types.entry_range);
                   FStar_Tactics_Types.guard_policy =
                     (uu___232_1717.FStar_Tactics_Types.guard_policy);
                   FStar_Tactics_Types.freshness =
                     (q.FStar_Tactics_Types.freshness);
                   FStar_Tactics_Types.tac_verb_dbg =
                     (uu___232_1717.FStar_Tactics_Types.tac_verb_dbg);
                   FStar_Tactics_Types.local_state =
                     (uu___232_1717.FStar_Tactics_Types.local_state)
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
           (fun uu___258_1863  ->
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
           (let uu___293_1979 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___293_1979.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.all_implicits =
                (FStar_List.append i p.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___293_1979.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (uu___293_1979.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___293_1979.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___293_1979.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___293_1979.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___293_1979.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___293_1979.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___293_1979.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___293_1979.FStar_Tactics_Types.tac_verb_dbg);
              FStar_Tactics_Types.local_state =
                (uu___293_1979.FStar_Tactics_Types.local_state)
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
           (fun uu___301_2020  ->
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
         let uu___327_2101 = FStar_TypeChecker_Env.trivial_guard  in
         {
           FStar_TypeChecker_Common.guard_f =
             (uu___327_2101.FStar_TypeChecker_Common.guard_f);
           FStar_TypeChecker_Common.deferred_to_tac =
             (uu___327_2101.FStar_TypeChecker_Common.deferred_to_tac);
           FStar_TypeChecker_Common.deferred =
             (uu___327_2101.FStar_TypeChecker_Common.deferred);
           FStar_TypeChecker_Common.univ_ineqs =
             (uu___327_2101.FStar_TypeChecker_Common.univ_ineqs);
           FStar_TypeChecker_Common.implicits = imps
         }  in
       let g1 =
         FStar_TypeChecker_Rel.resolve_implicits_tac
           ps.FStar_Tactics_Types.main_context g
          in
       let ps' =
         let uu___331_2104 = ps  in
         {
           FStar_Tactics_Types.main_context =
             (uu___331_2104.FStar_Tactics_Types.main_context);
           FStar_Tactics_Types.all_implicits =
             (g1.FStar_TypeChecker_Common.implicits);
           FStar_Tactics_Types.goals =
             (uu___331_2104.FStar_Tactics_Types.goals);
           FStar_Tactics_Types.smt_goals =
             (uu___331_2104.FStar_Tactics_Types.smt_goals);
           FStar_Tactics_Types.depth =
             (uu___331_2104.FStar_Tactics_Types.depth);
           FStar_Tactics_Types.__dump =
             (uu___331_2104.FStar_Tactics_Types.__dump);
           FStar_Tactics_Types.psc = (uu___331_2104.FStar_Tactics_Types.psc);
           FStar_Tactics_Types.entry_range =
             (uu___331_2104.FStar_Tactics_Types.entry_range);
           FStar_Tactics_Types.guard_policy =
             (uu___331_2104.FStar_Tactics_Types.guard_policy);
           FStar_Tactics_Types.freshness =
             (uu___331_2104.FStar_Tactics_Types.freshness);
           FStar_Tactics_Types.tac_verb_dbg =
             (uu___331_2104.FStar_Tactics_Types.tac_verb_dbg);
           FStar_Tactics_Types.local_state =
             (uu___331_2104.FStar_Tactics_Types.local_state)
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
         let uu___354_2228 = ps  in
         let uu____2229 =
           FStar_List.filter
             (fun g  ->
                let uu____2235 = check_goal_solved g  in
                FStar_Option.isNone uu____2235) ps.FStar_Tactics_Types.goals
            in
         {
           FStar_Tactics_Types.main_context =
             (uu___354_2228.FStar_Tactics_Types.main_context);
           FStar_Tactics_Types.all_implicits =
             (uu___354_2228.FStar_Tactics_Types.all_implicits);
           FStar_Tactics_Types.goals = uu____2229;
           FStar_Tactics_Types.smt_goals =
             (uu___354_2228.FStar_Tactics_Types.smt_goals);
           FStar_Tactics_Types.depth =
             (uu___354_2228.FStar_Tactics_Types.depth);
           FStar_Tactics_Types.__dump =
             (uu___354_2228.FStar_Tactics_Types.__dump);
           FStar_Tactics_Types.psc = (uu___354_2228.FStar_Tactics_Types.psc);
           FStar_Tactics_Types.entry_range =
             (uu___354_2228.FStar_Tactics_Types.entry_range);
           FStar_Tactics_Types.guard_policy =
             (uu___354_2228.FStar_Tactics_Types.guard_policy);
           FStar_Tactics_Types.freshness =
             (uu___354_2228.FStar_Tactics_Types.freshness);
           FStar_Tactics_Types.tac_verb_dbg =
             (uu___354_2228.FStar_Tactics_Types.tac_verb_dbg);
           FStar_Tactics_Types.local_state =
             (uu___354_2228.FStar_Tactics_Types.local_state)
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
         let uu___367_2291 = p  in
         let uu____2292 = FStar_List.tl p.FStar_Tactics_Types.goals  in
         {
           FStar_Tactics_Types.main_context =
             (uu___367_2291.FStar_Tactics_Types.main_context);
           FStar_Tactics_Types.all_implicits =
             (uu___367_2291.FStar_Tactics_Types.all_implicits);
           FStar_Tactics_Types.goals = uu____2292;
           FStar_Tactics_Types.smt_goals =
             (uu___367_2291.FStar_Tactics_Types.smt_goals);
           FStar_Tactics_Types.depth =
             (uu___367_2291.FStar_Tactics_Types.depth);
           FStar_Tactics_Types.__dump =
             (uu___367_2291.FStar_Tactics_Types.__dump);
           FStar_Tactics_Types.psc = (uu___367_2291.FStar_Tactics_Types.psc);
           FStar_Tactics_Types.entry_range =
             (uu___367_2291.FStar_Tactics_Types.entry_range);
           FStar_Tactics_Types.guard_policy =
             (uu___367_2291.FStar_Tactics_Types.guard_policy);
           FStar_Tactics_Types.freshness =
             (uu___367_2291.FStar_Tactics_Types.freshness);
           FStar_Tactics_Types.tac_verb_dbg =
             (uu___367_2291.FStar_Tactics_Types.tac_verb_dbg);
           FStar_Tactics_Types.local_state =
             (uu___367_2291.FStar_Tactics_Types.local_state)
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
           (let uu___383_2393 = ps  in
            {
              FStar_Tactics_Types.main_context =
                (uu___383_2393.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.all_implicits =
                (uu___383_2393.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals = gs;
              FStar_Tactics_Types.smt_goals =
                (uu___383_2393.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___383_2393.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___383_2393.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___383_2393.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___383_2393.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___383_2393.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___383_2393.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___383_2393.FStar_Tactics_Types.tac_verb_dbg);
              FStar_Tactics_Types.local_state =
                (uu___383_2393.FStar_Tactics_Types.local_state)
            }))
  
let (set_smt_goals : FStar_Tactics_Types.goal Prims.list -> unit tac) =
  fun gs  ->
    bind get
      (fun ps  ->
         set
           (let uu___387_2412 = ps  in
            {
              FStar_Tactics_Types.main_context =
                (uu___387_2412.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.all_implicits =
                (uu___387_2412.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___387_2412.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals = gs;
              FStar_Tactics_Types.depth =
                (uu___387_2412.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___387_2412.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___387_2412.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___387_2412.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___387_2412.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___387_2412.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___387_2412.FStar_Tactics_Types.tac_verb_dbg);
              FStar_Tactics_Types.local_state =
                (uu___387_2412.FStar_Tactics_Types.local_state)
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
           (let uu___409_2597 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___409_2597.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.all_implicits =
                (uu___409_2597.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (FStar_List.append gs p.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (uu___409_2597.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___409_2597.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___409_2597.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___409_2597.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___409_2597.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___409_2597.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___409_2597.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___409_2597.FStar_Tactics_Types.tac_verb_dbg);
              FStar_Tactics_Types.local_state =
                (uu___409_2597.FStar_Tactics_Types.local_state)
            }))
  
let (add_smt_goals : FStar_Tactics_Types.goal Prims.list -> unit tac) =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___414_2618 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___414_2618.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.all_implicits =
                (uu___414_2618.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___414_2618.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (FStar_List.append gs p.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___414_2618.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___414_2618.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___414_2618.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___414_2618.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___414_2618.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___414_2618.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___414_2618.FStar_Tactics_Types.tac_verb_dbg);
              FStar_Tactics_Types.local_state =
                (uu___414_2618.FStar_Tactics_Types.local_state)
            }))
  
let (push_goals : FStar_Tactics_Types.goal Prims.list -> unit tac) =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___419_2639 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___419_2639.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.all_implicits =
                (uu___419_2639.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (FStar_List.append p.FStar_Tactics_Types.goals gs);
              FStar_Tactics_Types.smt_goals =
                (uu___419_2639.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___419_2639.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___419_2639.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___419_2639.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___419_2639.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___419_2639.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___419_2639.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___419_2639.FStar_Tactics_Types.tac_verb_dbg);
              FStar_Tactics_Types.local_state =
                (uu___419_2639.FStar_Tactics_Types.local_state)
            }))
  
let (push_smt_goals : FStar_Tactics_Types.goal Prims.list -> unit tac) =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___424_2660 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___424_2660.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.all_implicits =
                (uu___424_2660.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___424_2660.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (FStar_List.append p.FStar_Tactics_Types.smt_goals gs);
              FStar_Tactics_Types.depth =
                (uu___424_2660.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___424_2660.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___424_2660.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___424_2660.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___424_2660.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___424_2660.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___424_2660.FStar_Tactics_Types.tac_verb_dbg);
              FStar_Tactics_Types.local_state =
                (uu___424_2660.FStar_Tactics_Types.local_state)
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
            let uu____2737 =
              add_implicits g_u.FStar_TypeChecker_Common.implicits  in
            bind uu____2737
              (fun uu____2746  ->
                 let uu____2747 =
                   let uu____2752 =
                     let uu____2753 = FStar_List.hd ctx_uvar  in
                     FStar_Pervasives_Native.fst uu____2753  in
                   (u, uu____2752)  in
                 ret uu____2747)
  
let (is_true : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____2774 = FStar_Syntax_Util.un_squash t1  in
    match uu____2774 with
    | FStar_Pervasives_Native.Some t' ->
        let t'1 = FStar_Syntax_Util.unascribe t'  in
        let uu____2786 =
          let uu____2787 = FStar_Syntax_Subst.compress t'1  in
          uu____2787.FStar_Syntax_Syntax.n  in
        (match uu____2786 with
         | FStar_Syntax_Syntax.Tm_fvar fv ->
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.true_lid
         | uu____2792 -> false)
    | uu____2794 -> false
  
let (is_false : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____2807 = FStar_Syntax_Util.un_squash t  in
    match uu____2807 with
    | FStar_Pervasives_Native.Some t' ->
        let uu____2818 =
          let uu____2819 = FStar_Syntax_Subst.compress t'  in
          uu____2819.FStar_Syntax_Syntax.n  in
        (match uu____2818 with
         | FStar_Syntax_Syntax.Tm_fvar fv ->
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.false_lid
         | uu____2824 -> false)
    | uu____2826 -> false
  
let (cur_goal : unit -> FStar_Tactics_Types.goal tac) =
  fun uu____2839  ->
    bind get
      (fun p  ->
         match p.FStar_Tactics_Types.goals with
         | [] -> fail "No more goals (1)"
         | hd1::tl1 ->
             let uu____2851 =
               FStar_Syntax_Unionfind.find
                 (hd1.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_head
                in
             (match uu____2851 with
              | FStar_Pervasives_Native.None  -> ret hd1
              | FStar_Pervasives_Native.Some t ->
                  ((let uu____2858 = goal_to_string_verbose hd1  in
                    let uu____2860 = FStar_Syntax_Print.term_to_string t  in
                    FStar_Util.print2
                      "!!!!!!!!!!!! GOAL IS ALREADY SOLVED! %s\nsol is %s\n"
                      uu____2858 uu____2860);
                   ret hd1)))
  
let (tadmit_t : FStar_Syntax_Syntax.term -> unit tac) =
  fun t  ->
    let uu____2873 =
      bind get
        (fun ps  ->
           let uu____2879 = cur_goal ()  in
           bind uu____2879
             (fun g  ->
                (let uu____2886 =
                   let uu____2887 = FStar_Tactics_Types.goal_type g  in
                   uu____2887.FStar_Syntax_Syntax.pos  in
                 let uu____2890 =
                   let uu____2896 =
                     let uu____2898 =
                       goal_to_string "" FStar_Pervasives_Native.None ps g
                        in
                     FStar_Util.format1 "Tactics admitted goal <%s>\n\n"
                       uu____2898
                      in
                   (FStar_Errors.Warning_TacAdmit, uu____2896)  in
                 FStar_Errors.log_issue uu____2886 uu____2890);
                solve' g t))
       in
    FStar_All.pipe_left (wrap_err "tadmit_t") uu____2873
  
let (fresh : unit -> FStar_BigInt.t tac) =
  fun uu____2921  ->
    bind get
      (fun ps  ->
         let n1 = ps.FStar_Tactics_Types.freshness  in
         let ps1 =
           let uu___469_2932 = ps  in
           {
             FStar_Tactics_Types.main_context =
               (uu___469_2932.FStar_Tactics_Types.main_context);
             FStar_Tactics_Types.all_implicits =
               (uu___469_2932.FStar_Tactics_Types.all_implicits);
             FStar_Tactics_Types.goals =
               (uu___469_2932.FStar_Tactics_Types.goals);
             FStar_Tactics_Types.smt_goals =
               (uu___469_2932.FStar_Tactics_Types.smt_goals);
             FStar_Tactics_Types.depth =
               (uu___469_2932.FStar_Tactics_Types.depth);
             FStar_Tactics_Types.__dump =
               (uu___469_2932.FStar_Tactics_Types.__dump);
             FStar_Tactics_Types.psc =
               (uu___469_2932.FStar_Tactics_Types.psc);
             FStar_Tactics_Types.entry_range =
               (uu___469_2932.FStar_Tactics_Types.entry_range);
             FStar_Tactics_Types.guard_policy =
               (uu___469_2932.FStar_Tactics_Types.guard_policy);
             FStar_Tactics_Types.freshness = (n1 + Prims.int_one);
             FStar_Tactics_Types.tac_verb_dbg =
               (uu___469_2932.FStar_Tactics_Types.tac_verb_dbg);
             FStar_Tactics_Types.local_state =
               (uu___469_2932.FStar_Tactics_Types.local_state)
           }  in
         let uu____2934 = set ps1  in
         bind uu____2934
           (fun uu____2939  ->
              let uu____2940 = FStar_BigInt.of_int_fs n1  in ret uu____2940))
  
let (curms : unit -> FStar_BigInt.t tac) =
  fun uu____2948  ->
    let uu____2951 =
      let uu____2952 = FStar_Util.now_ms ()  in
      FStar_All.pipe_right uu____2952 FStar_BigInt.of_int_fs  in
    ret uu____2951
  
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
              let uu____2992 = env.FStar_TypeChecker_Env.universe_of env phi
                 in
              FStar_Syntax_Util.mk_squash uu____2992 phi  in
            let uu____2993 = new_uvar reason env typ  in
            bind uu____2993
              (fun uu____3008  ->
                 match uu____3008 with
                 | (uu____3015,ctx_uvar) ->
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
             (fun uu____3062  ->
                let uu____3063 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.print1 "Tac> __tc(%s)\n" uu____3063)
             (fun uu____3068  ->
                let e1 =
                  let uu___488_3070 = e  in
                  {
                    FStar_TypeChecker_Env.solver =
                      (uu___488_3070.FStar_TypeChecker_Env.solver);
                    FStar_TypeChecker_Env.range =
                      (uu___488_3070.FStar_TypeChecker_Env.range);
                    FStar_TypeChecker_Env.curmodule =
                      (uu___488_3070.FStar_TypeChecker_Env.curmodule);
                    FStar_TypeChecker_Env.gamma =
                      (uu___488_3070.FStar_TypeChecker_Env.gamma);
                    FStar_TypeChecker_Env.gamma_sig =
                      (uu___488_3070.FStar_TypeChecker_Env.gamma_sig);
                    FStar_TypeChecker_Env.gamma_cache =
                      (uu___488_3070.FStar_TypeChecker_Env.gamma_cache);
                    FStar_TypeChecker_Env.modules =
                      (uu___488_3070.FStar_TypeChecker_Env.modules);
                    FStar_TypeChecker_Env.expected_typ =
                      (uu___488_3070.FStar_TypeChecker_Env.expected_typ);
                    FStar_TypeChecker_Env.sigtab =
                      (uu___488_3070.FStar_TypeChecker_Env.sigtab);
                    FStar_TypeChecker_Env.attrtab =
                      (uu___488_3070.FStar_TypeChecker_Env.attrtab);
                    FStar_TypeChecker_Env.instantiate_imp =
                      (uu___488_3070.FStar_TypeChecker_Env.instantiate_imp);
                    FStar_TypeChecker_Env.effects =
                      (uu___488_3070.FStar_TypeChecker_Env.effects);
                    FStar_TypeChecker_Env.generalize =
                      (uu___488_3070.FStar_TypeChecker_Env.generalize);
                    FStar_TypeChecker_Env.letrecs =
                      (uu___488_3070.FStar_TypeChecker_Env.letrecs);
                    FStar_TypeChecker_Env.top_level =
                      (uu___488_3070.FStar_TypeChecker_Env.top_level);
                    FStar_TypeChecker_Env.check_uvars =
                      (uu___488_3070.FStar_TypeChecker_Env.check_uvars);
                    FStar_TypeChecker_Env.use_eq =
                      (uu___488_3070.FStar_TypeChecker_Env.use_eq);
                    FStar_TypeChecker_Env.use_eq_strict =
                      (uu___488_3070.FStar_TypeChecker_Env.use_eq_strict);
                    FStar_TypeChecker_Env.is_iface =
                      (uu___488_3070.FStar_TypeChecker_Env.is_iface);
                    FStar_TypeChecker_Env.admit =
                      (uu___488_3070.FStar_TypeChecker_Env.admit);
                    FStar_TypeChecker_Env.lax =
                      (uu___488_3070.FStar_TypeChecker_Env.lax);
                    FStar_TypeChecker_Env.lax_universes =
                      (uu___488_3070.FStar_TypeChecker_Env.lax_universes);
                    FStar_TypeChecker_Env.phase1 =
                      (uu___488_3070.FStar_TypeChecker_Env.phase1);
                    FStar_TypeChecker_Env.failhard =
                      (uu___488_3070.FStar_TypeChecker_Env.failhard);
                    FStar_TypeChecker_Env.nosynth =
                      (uu___488_3070.FStar_TypeChecker_Env.nosynth);
                    FStar_TypeChecker_Env.uvar_subtyping = false;
                    FStar_TypeChecker_Env.tc_term =
                      (uu___488_3070.FStar_TypeChecker_Env.tc_term);
                    FStar_TypeChecker_Env.type_of =
                      (uu___488_3070.FStar_TypeChecker_Env.type_of);
                    FStar_TypeChecker_Env.universe_of =
                      (uu___488_3070.FStar_TypeChecker_Env.universe_of);
                    FStar_TypeChecker_Env.check_type_of =
                      (uu___488_3070.FStar_TypeChecker_Env.check_type_of);
                    FStar_TypeChecker_Env.use_bv_sorts =
                      (uu___488_3070.FStar_TypeChecker_Env.use_bv_sorts);
                    FStar_TypeChecker_Env.qtbl_name_and_index =
                      (uu___488_3070.FStar_TypeChecker_Env.qtbl_name_and_index);
                    FStar_TypeChecker_Env.normalized_eff_names =
                      (uu___488_3070.FStar_TypeChecker_Env.normalized_eff_names);
                    FStar_TypeChecker_Env.fv_delta_depths =
                      (uu___488_3070.FStar_TypeChecker_Env.fv_delta_depths);
                    FStar_TypeChecker_Env.proof_ns =
                      (uu___488_3070.FStar_TypeChecker_Env.proof_ns);
                    FStar_TypeChecker_Env.synth_hook =
                      (uu___488_3070.FStar_TypeChecker_Env.synth_hook);
                    FStar_TypeChecker_Env.try_solve_implicits_hook =
                      (uu___488_3070.FStar_TypeChecker_Env.try_solve_implicits_hook);
                    FStar_TypeChecker_Env.splice =
                      (uu___488_3070.FStar_TypeChecker_Env.splice);
                    FStar_TypeChecker_Env.mpreprocess =
                      (uu___488_3070.FStar_TypeChecker_Env.mpreprocess);
                    FStar_TypeChecker_Env.postprocess =
                      (uu___488_3070.FStar_TypeChecker_Env.postprocess);
                    FStar_TypeChecker_Env.is_native_tactic =
                      (uu___488_3070.FStar_TypeChecker_Env.is_native_tactic);
                    FStar_TypeChecker_Env.identifier_info =
                      (uu___488_3070.FStar_TypeChecker_Env.identifier_info);
                    FStar_TypeChecker_Env.tc_hooks =
                      (uu___488_3070.FStar_TypeChecker_Env.tc_hooks);
                    FStar_TypeChecker_Env.dsenv =
                      (uu___488_3070.FStar_TypeChecker_Env.dsenv);
                    FStar_TypeChecker_Env.nbe =
                      (uu___488_3070.FStar_TypeChecker_Env.nbe);
                    FStar_TypeChecker_Env.strict_args_tab =
                      (uu___488_3070.FStar_TypeChecker_Env.strict_args_tab);
                    FStar_TypeChecker_Env.erasable_types_tab =
                      (uu___488_3070.FStar_TypeChecker_Env.erasable_types_tab);
                    FStar_TypeChecker_Env.enable_defer_to_tac =
                      (uu___488_3070.FStar_TypeChecker_Env.enable_defer_to_tac)
                  }  in
                try
                  (fun uu___492_3082  ->
                     match () with
                     | () ->
                         let uu____3091 =
                           FStar_TypeChecker_TcTerm.type_of_tot_term e1 t  in
                         ret uu____3091) ()
                with
                | FStar_Errors.Err (uu____3118,msg) ->
                    let uu____3122 = tts e1 t  in
                    let uu____3124 =
                      let uu____3126 = FStar_TypeChecker_Env.all_binders e1
                         in
                      FStar_All.pipe_right uu____3126
                        (FStar_Syntax_Print.binders_to_string ", ")
                       in
                    fail3 "Cannot type %s in context (%s). Error = (%s)"
                      uu____3122 uu____3124 msg
                | FStar_Errors.Error (uu____3136,msg,uu____3138) ->
                    let uu____3141 = tts e1 t  in
                    let uu____3143 =
                      let uu____3145 = FStar_TypeChecker_Env.all_binders e1
                         in
                      FStar_All.pipe_right uu____3145
                        (FStar_Syntax_Print.binders_to_string ", ")
                       in
                    fail3 "Cannot type %s in context (%s). Error = (%s)"
                      uu____3141 uu____3143 msg))
  
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
             (fun uu____3198  ->
                let uu____3199 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.print1 "Tac> __tc_ghost(%s)\n" uu____3199)
             (fun uu____3204  ->
                let e1 =
                  let uu___509_3206 = e  in
                  {
                    FStar_TypeChecker_Env.solver =
                      (uu___509_3206.FStar_TypeChecker_Env.solver);
                    FStar_TypeChecker_Env.range =
                      (uu___509_3206.FStar_TypeChecker_Env.range);
                    FStar_TypeChecker_Env.curmodule =
                      (uu___509_3206.FStar_TypeChecker_Env.curmodule);
                    FStar_TypeChecker_Env.gamma =
                      (uu___509_3206.FStar_TypeChecker_Env.gamma);
                    FStar_TypeChecker_Env.gamma_sig =
                      (uu___509_3206.FStar_TypeChecker_Env.gamma_sig);
                    FStar_TypeChecker_Env.gamma_cache =
                      (uu___509_3206.FStar_TypeChecker_Env.gamma_cache);
                    FStar_TypeChecker_Env.modules =
                      (uu___509_3206.FStar_TypeChecker_Env.modules);
                    FStar_TypeChecker_Env.expected_typ =
                      (uu___509_3206.FStar_TypeChecker_Env.expected_typ);
                    FStar_TypeChecker_Env.sigtab =
                      (uu___509_3206.FStar_TypeChecker_Env.sigtab);
                    FStar_TypeChecker_Env.attrtab =
                      (uu___509_3206.FStar_TypeChecker_Env.attrtab);
                    FStar_TypeChecker_Env.instantiate_imp =
                      (uu___509_3206.FStar_TypeChecker_Env.instantiate_imp);
                    FStar_TypeChecker_Env.effects =
                      (uu___509_3206.FStar_TypeChecker_Env.effects);
                    FStar_TypeChecker_Env.generalize =
                      (uu___509_3206.FStar_TypeChecker_Env.generalize);
                    FStar_TypeChecker_Env.letrecs =
                      (uu___509_3206.FStar_TypeChecker_Env.letrecs);
                    FStar_TypeChecker_Env.top_level =
                      (uu___509_3206.FStar_TypeChecker_Env.top_level);
                    FStar_TypeChecker_Env.check_uvars =
                      (uu___509_3206.FStar_TypeChecker_Env.check_uvars);
                    FStar_TypeChecker_Env.use_eq =
                      (uu___509_3206.FStar_TypeChecker_Env.use_eq);
                    FStar_TypeChecker_Env.use_eq_strict =
                      (uu___509_3206.FStar_TypeChecker_Env.use_eq_strict);
                    FStar_TypeChecker_Env.is_iface =
                      (uu___509_3206.FStar_TypeChecker_Env.is_iface);
                    FStar_TypeChecker_Env.admit =
                      (uu___509_3206.FStar_TypeChecker_Env.admit);
                    FStar_TypeChecker_Env.lax =
                      (uu___509_3206.FStar_TypeChecker_Env.lax);
                    FStar_TypeChecker_Env.lax_universes =
                      (uu___509_3206.FStar_TypeChecker_Env.lax_universes);
                    FStar_TypeChecker_Env.phase1 =
                      (uu___509_3206.FStar_TypeChecker_Env.phase1);
                    FStar_TypeChecker_Env.failhard =
                      (uu___509_3206.FStar_TypeChecker_Env.failhard);
                    FStar_TypeChecker_Env.nosynth =
                      (uu___509_3206.FStar_TypeChecker_Env.nosynth);
                    FStar_TypeChecker_Env.uvar_subtyping = false;
                    FStar_TypeChecker_Env.tc_term =
                      (uu___509_3206.FStar_TypeChecker_Env.tc_term);
                    FStar_TypeChecker_Env.type_of =
                      (uu___509_3206.FStar_TypeChecker_Env.type_of);
                    FStar_TypeChecker_Env.universe_of =
                      (uu___509_3206.FStar_TypeChecker_Env.universe_of);
                    FStar_TypeChecker_Env.check_type_of =
                      (uu___509_3206.FStar_TypeChecker_Env.check_type_of);
                    FStar_TypeChecker_Env.use_bv_sorts =
                      (uu___509_3206.FStar_TypeChecker_Env.use_bv_sorts);
                    FStar_TypeChecker_Env.qtbl_name_and_index =
                      (uu___509_3206.FStar_TypeChecker_Env.qtbl_name_and_index);
                    FStar_TypeChecker_Env.normalized_eff_names =
                      (uu___509_3206.FStar_TypeChecker_Env.normalized_eff_names);
                    FStar_TypeChecker_Env.fv_delta_depths =
                      (uu___509_3206.FStar_TypeChecker_Env.fv_delta_depths);
                    FStar_TypeChecker_Env.proof_ns =
                      (uu___509_3206.FStar_TypeChecker_Env.proof_ns);
                    FStar_TypeChecker_Env.synth_hook =
                      (uu___509_3206.FStar_TypeChecker_Env.synth_hook);
                    FStar_TypeChecker_Env.try_solve_implicits_hook =
                      (uu___509_3206.FStar_TypeChecker_Env.try_solve_implicits_hook);
                    FStar_TypeChecker_Env.splice =
                      (uu___509_3206.FStar_TypeChecker_Env.splice);
                    FStar_TypeChecker_Env.mpreprocess =
                      (uu___509_3206.FStar_TypeChecker_Env.mpreprocess);
                    FStar_TypeChecker_Env.postprocess =
                      (uu___509_3206.FStar_TypeChecker_Env.postprocess);
                    FStar_TypeChecker_Env.is_native_tactic =
                      (uu___509_3206.FStar_TypeChecker_Env.is_native_tactic);
                    FStar_TypeChecker_Env.identifier_info =
                      (uu___509_3206.FStar_TypeChecker_Env.identifier_info);
                    FStar_TypeChecker_Env.tc_hooks =
                      (uu___509_3206.FStar_TypeChecker_Env.tc_hooks);
                    FStar_TypeChecker_Env.dsenv =
                      (uu___509_3206.FStar_TypeChecker_Env.dsenv);
                    FStar_TypeChecker_Env.nbe =
                      (uu___509_3206.FStar_TypeChecker_Env.nbe);
                    FStar_TypeChecker_Env.strict_args_tab =
                      (uu___509_3206.FStar_TypeChecker_Env.strict_args_tab);
                    FStar_TypeChecker_Env.erasable_types_tab =
                      (uu___509_3206.FStar_TypeChecker_Env.erasable_types_tab);
                    FStar_TypeChecker_Env.enable_defer_to_tac =
                      (uu___509_3206.FStar_TypeChecker_Env.enable_defer_to_tac)
                  }  in
                try
                  (fun uu___513_3221  ->
                     match () with
                     | () ->
                         let uu____3230 =
                           FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term e1 t
                            in
                         (match uu____3230 with
                          | (t1,lc,g) ->
                              ret
                                (t1, (lc.FStar_TypeChecker_Common.res_typ),
                                  g))) ()
                with
                | FStar_Errors.Err (uu____3268,msg) ->
                    let uu____3272 = tts e1 t  in
                    let uu____3274 =
                      let uu____3276 = FStar_TypeChecker_Env.all_binders e1
                         in
                      FStar_All.pipe_right uu____3276
                        (FStar_Syntax_Print.binders_to_string ", ")
                       in
                    fail3 "Cannot type %s in context (%s). Error = (%s)"
                      uu____3272 uu____3274 msg
                | FStar_Errors.Error (uu____3286,msg,uu____3288) ->
                    let uu____3291 = tts e1 t  in
                    let uu____3293 =
                      let uu____3295 = FStar_TypeChecker_Env.all_binders e1
                         in
                      FStar_All.pipe_right uu____3295
                        (FStar_Syntax_Print.binders_to_string ", ")
                       in
                    fail3 "Cannot type %s in context (%s). Error = (%s)"
                      uu____3291 uu____3293 msg))
  
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
             (fun uu____3348  ->
                let uu____3349 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.print1 "Tac> __tc_lax(%s)\n" uu____3349)
             (fun uu____3355  ->
                let e1 =
                  let uu___534_3357 = e  in
                  {
                    FStar_TypeChecker_Env.solver =
                      (uu___534_3357.FStar_TypeChecker_Env.solver);
                    FStar_TypeChecker_Env.range =
                      (uu___534_3357.FStar_TypeChecker_Env.range);
                    FStar_TypeChecker_Env.curmodule =
                      (uu___534_3357.FStar_TypeChecker_Env.curmodule);
                    FStar_TypeChecker_Env.gamma =
                      (uu___534_3357.FStar_TypeChecker_Env.gamma);
                    FStar_TypeChecker_Env.gamma_sig =
                      (uu___534_3357.FStar_TypeChecker_Env.gamma_sig);
                    FStar_TypeChecker_Env.gamma_cache =
                      (uu___534_3357.FStar_TypeChecker_Env.gamma_cache);
                    FStar_TypeChecker_Env.modules =
                      (uu___534_3357.FStar_TypeChecker_Env.modules);
                    FStar_TypeChecker_Env.expected_typ =
                      (uu___534_3357.FStar_TypeChecker_Env.expected_typ);
                    FStar_TypeChecker_Env.sigtab =
                      (uu___534_3357.FStar_TypeChecker_Env.sigtab);
                    FStar_TypeChecker_Env.attrtab =
                      (uu___534_3357.FStar_TypeChecker_Env.attrtab);
                    FStar_TypeChecker_Env.instantiate_imp =
                      (uu___534_3357.FStar_TypeChecker_Env.instantiate_imp);
                    FStar_TypeChecker_Env.effects =
                      (uu___534_3357.FStar_TypeChecker_Env.effects);
                    FStar_TypeChecker_Env.generalize =
                      (uu___534_3357.FStar_TypeChecker_Env.generalize);
                    FStar_TypeChecker_Env.letrecs =
                      (uu___534_3357.FStar_TypeChecker_Env.letrecs);
                    FStar_TypeChecker_Env.top_level =
                      (uu___534_3357.FStar_TypeChecker_Env.top_level);
                    FStar_TypeChecker_Env.check_uvars =
                      (uu___534_3357.FStar_TypeChecker_Env.check_uvars);
                    FStar_TypeChecker_Env.use_eq =
                      (uu___534_3357.FStar_TypeChecker_Env.use_eq);
                    FStar_TypeChecker_Env.use_eq_strict =
                      (uu___534_3357.FStar_TypeChecker_Env.use_eq_strict);
                    FStar_TypeChecker_Env.is_iface =
                      (uu___534_3357.FStar_TypeChecker_Env.is_iface);
                    FStar_TypeChecker_Env.admit =
                      (uu___534_3357.FStar_TypeChecker_Env.admit);
                    FStar_TypeChecker_Env.lax =
                      (uu___534_3357.FStar_TypeChecker_Env.lax);
                    FStar_TypeChecker_Env.lax_universes =
                      (uu___534_3357.FStar_TypeChecker_Env.lax_universes);
                    FStar_TypeChecker_Env.phase1 =
                      (uu___534_3357.FStar_TypeChecker_Env.phase1);
                    FStar_TypeChecker_Env.failhard =
                      (uu___534_3357.FStar_TypeChecker_Env.failhard);
                    FStar_TypeChecker_Env.nosynth =
                      (uu___534_3357.FStar_TypeChecker_Env.nosynth);
                    FStar_TypeChecker_Env.uvar_subtyping = false;
                    FStar_TypeChecker_Env.tc_term =
                      (uu___534_3357.FStar_TypeChecker_Env.tc_term);
                    FStar_TypeChecker_Env.type_of =
                      (uu___534_3357.FStar_TypeChecker_Env.type_of);
                    FStar_TypeChecker_Env.universe_of =
                      (uu___534_3357.FStar_TypeChecker_Env.universe_of);
                    FStar_TypeChecker_Env.check_type_of =
                      (uu___534_3357.FStar_TypeChecker_Env.check_type_of);
                    FStar_TypeChecker_Env.use_bv_sorts =
                      (uu___534_3357.FStar_TypeChecker_Env.use_bv_sorts);
                    FStar_TypeChecker_Env.qtbl_name_and_index =
                      (uu___534_3357.FStar_TypeChecker_Env.qtbl_name_and_index);
                    FStar_TypeChecker_Env.normalized_eff_names =
                      (uu___534_3357.FStar_TypeChecker_Env.normalized_eff_names);
                    FStar_TypeChecker_Env.fv_delta_depths =
                      (uu___534_3357.FStar_TypeChecker_Env.fv_delta_depths);
                    FStar_TypeChecker_Env.proof_ns =
                      (uu___534_3357.FStar_TypeChecker_Env.proof_ns);
                    FStar_TypeChecker_Env.synth_hook =
                      (uu___534_3357.FStar_TypeChecker_Env.synth_hook);
                    FStar_TypeChecker_Env.try_solve_implicits_hook =
                      (uu___534_3357.FStar_TypeChecker_Env.try_solve_implicits_hook);
                    FStar_TypeChecker_Env.splice =
                      (uu___534_3357.FStar_TypeChecker_Env.splice);
                    FStar_TypeChecker_Env.mpreprocess =
                      (uu___534_3357.FStar_TypeChecker_Env.mpreprocess);
                    FStar_TypeChecker_Env.postprocess =
                      (uu___534_3357.FStar_TypeChecker_Env.postprocess);
                    FStar_TypeChecker_Env.is_native_tactic =
                      (uu___534_3357.FStar_TypeChecker_Env.is_native_tactic);
                    FStar_TypeChecker_Env.identifier_info =
                      (uu___534_3357.FStar_TypeChecker_Env.identifier_info);
                    FStar_TypeChecker_Env.tc_hooks =
                      (uu___534_3357.FStar_TypeChecker_Env.tc_hooks);
                    FStar_TypeChecker_Env.dsenv =
                      (uu___534_3357.FStar_TypeChecker_Env.dsenv);
                    FStar_TypeChecker_Env.nbe =
                      (uu___534_3357.FStar_TypeChecker_Env.nbe);
                    FStar_TypeChecker_Env.strict_args_tab =
                      (uu___534_3357.FStar_TypeChecker_Env.strict_args_tab);
                    FStar_TypeChecker_Env.erasable_types_tab =
                      (uu___534_3357.FStar_TypeChecker_Env.erasable_types_tab);
                    FStar_TypeChecker_Env.enable_defer_to_tac =
                      (uu___534_3357.FStar_TypeChecker_Env.enable_defer_to_tac)
                  }  in
                let e2 =
                  let uu___537_3360 = e1  in
                  {
                    FStar_TypeChecker_Env.solver =
                      (uu___537_3360.FStar_TypeChecker_Env.solver);
                    FStar_TypeChecker_Env.range =
                      (uu___537_3360.FStar_TypeChecker_Env.range);
                    FStar_TypeChecker_Env.curmodule =
                      (uu___537_3360.FStar_TypeChecker_Env.curmodule);
                    FStar_TypeChecker_Env.gamma =
                      (uu___537_3360.FStar_TypeChecker_Env.gamma);
                    FStar_TypeChecker_Env.gamma_sig =
                      (uu___537_3360.FStar_TypeChecker_Env.gamma_sig);
                    FStar_TypeChecker_Env.gamma_cache =
                      (uu___537_3360.FStar_TypeChecker_Env.gamma_cache);
                    FStar_TypeChecker_Env.modules =
                      (uu___537_3360.FStar_TypeChecker_Env.modules);
                    FStar_TypeChecker_Env.expected_typ =
                      (uu___537_3360.FStar_TypeChecker_Env.expected_typ);
                    FStar_TypeChecker_Env.sigtab =
                      (uu___537_3360.FStar_TypeChecker_Env.sigtab);
                    FStar_TypeChecker_Env.attrtab =
                      (uu___537_3360.FStar_TypeChecker_Env.attrtab);
                    FStar_TypeChecker_Env.instantiate_imp =
                      (uu___537_3360.FStar_TypeChecker_Env.instantiate_imp);
                    FStar_TypeChecker_Env.effects =
                      (uu___537_3360.FStar_TypeChecker_Env.effects);
                    FStar_TypeChecker_Env.generalize =
                      (uu___537_3360.FStar_TypeChecker_Env.generalize);
                    FStar_TypeChecker_Env.letrecs =
                      (uu___537_3360.FStar_TypeChecker_Env.letrecs);
                    FStar_TypeChecker_Env.top_level =
                      (uu___537_3360.FStar_TypeChecker_Env.top_level);
                    FStar_TypeChecker_Env.check_uvars =
                      (uu___537_3360.FStar_TypeChecker_Env.check_uvars);
                    FStar_TypeChecker_Env.use_eq =
                      (uu___537_3360.FStar_TypeChecker_Env.use_eq);
                    FStar_TypeChecker_Env.use_eq_strict =
                      (uu___537_3360.FStar_TypeChecker_Env.use_eq_strict);
                    FStar_TypeChecker_Env.is_iface =
                      (uu___537_3360.FStar_TypeChecker_Env.is_iface);
                    FStar_TypeChecker_Env.admit =
                      (uu___537_3360.FStar_TypeChecker_Env.admit);
                    FStar_TypeChecker_Env.lax = true;
                    FStar_TypeChecker_Env.lax_universes =
                      (uu___537_3360.FStar_TypeChecker_Env.lax_universes);
                    FStar_TypeChecker_Env.phase1 =
                      (uu___537_3360.FStar_TypeChecker_Env.phase1);
                    FStar_TypeChecker_Env.failhard =
                      (uu___537_3360.FStar_TypeChecker_Env.failhard);
                    FStar_TypeChecker_Env.nosynth =
                      (uu___537_3360.FStar_TypeChecker_Env.nosynth);
                    FStar_TypeChecker_Env.uvar_subtyping =
                      (uu___537_3360.FStar_TypeChecker_Env.uvar_subtyping);
                    FStar_TypeChecker_Env.tc_term =
                      (uu___537_3360.FStar_TypeChecker_Env.tc_term);
                    FStar_TypeChecker_Env.type_of =
                      (uu___537_3360.FStar_TypeChecker_Env.type_of);
                    FStar_TypeChecker_Env.universe_of =
                      (uu___537_3360.FStar_TypeChecker_Env.universe_of);
                    FStar_TypeChecker_Env.check_type_of =
                      (uu___537_3360.FStar_TypeChecker_Env.check_type_of);
                    FStar_TypeChecker_Env.use_bv_sorts =
                      (uu___537_3360.FStar_TypeChecker_Env.use_bv_sorts);
                    FStar_TypeChecker_Env.qtbl_name_and_index =
                      (uu___537_3360.FStar_TypeChecker_Env.qtbl_name_and_index);
                    FStar_TypeChecker_Env.normalized_eff_names =
                      (uu___537_3360.FStar_TypeChecker_Env.normalized_eff_names);
                    FStar_TypeChecker_Env.fv_delta_depths =
                      (uu___537_3360.FStar_TypeChecker_Env.fv_delta_depths);
                    FStar_TypeChecker_Env.proof_ns =
                      (uu___537_3360.FStar_TypeChecker_Env.proof_ns);
                    FStar_TypeChecker_Env.synth_hook =
                      (uu___537_3360.FStar_TypeChecker_Env.synth_hook);
                    FStar_TypeChecker_Env.try_solve_implicits_hook =
                      (uu___537_3360.FStar_TypeChecker_Env.try_solve_implicits_hook);
                    FStar_TypeChecker_Env.splice =
                      (uu___537_3360.FStar_TypeChecker_Env.splice);
                    FStar_TypeChecker_Env.mpreprocess =
                      (uu___537_3360.FStar_TypeChecker_Env.mpreprocess);
                    FStar_TypeChecker_Env.postprocess =
                      (uu___537_3360.FStar_TypeChecker_Env.postprocess);
                    FStar_TypeChecker_Env.is_native_tactic =
                      (uu___537_3360.FStar_TypeChecker_Env.is_native_tactic);
                    FStar_TypeChecker_Env.identifier_info =
                      (uu___537_3360.FStar_TypeChecker_Env.identifier_info);
                    FStar_TypeChecker_Env.tc_hooks =
                      (uu___537_3360.FStar_TypeChecker_Env.tc_hooks);
                    FStar_TypeChecker_Env.dsenv =
                      (uu___537_3360.FStar_TypeChecker_Env.dsenv);
                    FStar_TypeChecker_Env.nbe =
                      (uu___537_3360.FStar_TypeChecker_Env.nbe);
                    FStar_TypeChecker_Env.strict_args_tab =
                      (uu___537_3360.FStar_TypeChecker_Env.strict_args_tab);
                    FStar_TypeChecker_Env.erasable_types_tab =
                      (uu___537_3360.FStar_TypeChecker_Env.erasable_types_tab);
                    FStar_TypeChecker_Env.enable_defer_to_tac =
                      (uu___537_3360.FStar_TypeChecker_Env.enable_defer_to_tac)
                  }  in
                try
                  (fun uu___541_3372  ->
                     match () with
                     | () ->
                         let uu____3381 =
                           FStar_TypeChecker_TcTerm.tc_term e2 t  in
                         ret uu____3381) ()
                with
                | FStar_Errors.Err (uu____3408,msg) ->
                    let uu____3412 = tts e2 t  in
                    let uu____3414 =
                      let uu____3416 = FStar_TypeChecker_Env.all_binders e2
                         in
                      FStar_All.pipe_right uu____3416
                        (FStar_Syntax_Print.binders_to_string ", ")
                       in
                    fail3 "Cannot type %s in context (%s). Error = (%s)"
                      uu____3412 uu____3414 msg
                | FStar_Errors.Error (uu____3426,msg,uu____3428) ->
                    let uu____3431 = tts e2 t  in
                    let uu____3433 =
                      let uu____3435 = FStar_TypeChecker_Env.all_binders e2
                         in
                      FStar_All.pipe_right uu____3435
                        (FStar_Syntax_Print.binders_to_string ", ")
                       in
                    fail3 "Cannot type %s in context (%s). Error = (%s)"
                      uu____3431 uu____3433 msg))
  
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
  fun uu____3469  ->
    bind get (fun ps  -> ret ps.FStar_Tactics_Types.guard_policy)
  
let (set_guard_policy : FStar_Tactics_Types.guard_policy -> unit tac) =
  fun pol  ->
    bind get
      (fun ps  ->
         set
           (let uu___562_3488 = ps  in
            {
              FStar_Tactics_Types.main_context =
                (uu___562_3488.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.all_implicits =
                (uu___562_3488.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___562_3488.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (uu___562_3488.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___562_3488.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___562_3488.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___562_3488.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___562_3488.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy = pol;
              FStar_Tactics_Types.freshness =
                (uu___562_3488.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___562_3488.FStar_Tactics_Types.tac_verb_dbg);
              FStar_Tactics_Types.local_state =
                (uu___562_3488.FStar_Tactics_Types.local_state)
            }))
  
let with_policy : 'a . FStar_Tactics_Types.guard_policy -> 'a tac -> 'a tac =
  fun pol  ->
    fun t  ->
      let uu____3513 = get_guard_policy ()  in
      bind uu____3513
        (fun old_pol  ->
           let uu____3519 = set_guard_policy pol  in
           bind uu____3519
             (fun uu____3523  ->
                bind t
                  (fun r  ->
                     let uu____3527 = set_guard_policy old_pol  in
                     bind uu____3527 (fun uu____3531  -> ret r))))
  
let (getopts : FStar_Options.optionstate tac) =
  let uu____3535 = let uu____3540 = cur_goal ()  in trytac uu____3540  in
  bind uu____3535
    (fun uu___0_3547  ->
       match uu___0_3547 with
       | FStar_Pervasives_Native.Some g -> ret g.FStar_Tactics_Types.opts
       | FStar_Pervasives_Native.None  ->
           let uu____3553 = FStar_Options.peek ()  in ret uu____3553)
  
let (proc_guard :
  Prims.string -> env -> FStar_TypeChecker_Common.guard_t -> unit tac) =
  fun reason  ->
    fun e  ->
      fun g  ->
        mlog
          (fun uu____3578  ->
             let uu____3579 = FStar_TypeChecker_Rel.guard_to_string e g  in
             FStar_Util.print2 "Processing guard (%s:%s)\n" reason uu____3579)
          (fun uu____3584  ->
             let uu____3585 =
               add_implicits g.FStar_TypeChecker_Common.implicits  in
             bind uu____3585
               (fun uu____3589  ->
                  bind getopts
                    (fun opts  ->
                       let uu____3593 =
                         let uu____3594 =
                           FStar_TypeChecker_Rel.simplify_guard e g  in
                         uu____3594.FStar_TypeChecker_Common.guard_f  in
                       match uu____3593 with
                       | FStar_TypeChecker_Common.Trivial  -> ret ()
                       | FStar_TypeChecker_Common.NonTrivial f ->
                           let uu____3598 = istrivial e f  in
                           if uu____3598
                           then ret ()
                           else
                             bind get
                               (fun ps  ->
                                  match ps.FStar_Tactics_Types.guard_policy
                                  with
                                  | FStar_Tactics_Types.Drop  ->
                                      ((let uu____3611 =
                                          let uu____3617 =
                                            let uu____3619 =
                                              FStar_TypeChecker_Rel.guard_to_string
                                                e g
                                               in
                                            FStar_Util.format1
                                              "Tactics admitted guard <%s>\n\n"
                                              uu____3619
                                             in
                                          (FStar_Errors.Warning_TacAdmit,
                                            uu____3617)
                                           in
                                        FStar_Errors.log_issue
                                          e.FStar_TypeChecker_Env.range
                                          uu____3611);
                                       ret ())
                                  | FStar_Tactics_Types.Goal  ->
                                      mlog
                                        (fun uu____3625  ->
                                           let uu____3626 =
                                             FStar_TypeChecker_Rel.guard_to_string
                                               e g
                                              in
                                           FStar_Util.print2
                                             "Making guard (%s:%s) into a goal\n"
                                             reason uu____3626)
                                        (fun uu____3631  ->
                                           let uu____3632 =
                                             mk_irrelevant_goal reason e f
                                               opts ""
                                              in
                                           bind uu____3632
                                             (fun goal  ->
                                                let goal1 =
                                                  let uu___591_3640 = goal
                                                     in
                                                  {
                                                    FStar_Tactics_Types.goal_main_env
                                                      =
                                                      (uu___591_3640.FStar_Tactics_Types.goal_main_env);
                                                    FStar_Tactics_Types.goal_ctx_uvar
                                                      =
                                                      (uu___591_3640.FStar_Tactics_Types.goal_ctx_uvar);
                                                    FStar_Tactics_Types.opts
                                                      =
                                                      (uu___591_3640.FStar_Tactics_Types.opts);
                                                    FStar_Tactics_Types.is_guard
                                                      = true;
                                                    FStar_Tactics_Types.label
                                                      =
                                                      (uu___591_3640.FStar_Tactics_Types.label)
                                                  }  in
                                                push_goals [goal1]))
                                  | FStar_Tactics_Types.SMT  ->
                                      mlog
                                        (fun uu____3644  ->
                                           let uu____3645 =
                                             FStar_TypeChecker_Rel.guard_to_string
                                               e g
                                              in
                                           FStar_Util.print2
                                             "Sending guard (%s:%s) to SMT goal\n"
                                             reason uu____3645)
                                        (fun uu____3650  ->
                                           let uu____3651 =
                                             mk_irrelevant_goal reason e f
                                               opts ""
                                              in
                                           bind uu____3651
                                             (fun goal  ->
                                                let goal1 =
                                                  let uu___598_3659 = goal
                                                     in
                                                  {
                                                    FStar_Tactics_Types.goal_main_env
                                                      =
                                                      (uu___598_3659.FStar_Tactics_Types.goal_main_env);
                                                    FStar_Tactics_Types.goal_ctx_uvar
                                                      =
                                                      (uu___598_3659.FStar_Tactics_Types.goal_ctx_uvar);
                                                    FStar_Tactics_Types.opts
                                                      =
                                                      (uu___598_3659.FStar_Tactics_Types.opts);
                                                    FStar_Tactics_Types.is_guard
                                                      = true;
                                                    FStar_Tactics_Types.label
                                                      =
                                                      (uu___598_3659.FStar_Tactics_Types.label)
                                                  }  in
                                                push_smt_goals [goal1]))
                                  | FStar_Tactics_Types.Force  ->
                                      mlog
                                        (fun uu____3663  ->
                                           let uu____3664 =
                                             FStar_TypeChecker_Rel.guard_to_string
                                               e g
                                              in
                                           FStar_Util.print2
                                             "Forcing guard (%s:%s)\n" reason
                                             uu____3664)
                                        (fun uu____3668  ->
                                           try
                                             (fun uu___605_3673  ->
                                                match () with
                                                | () ->
                                                    let uu____3676 =
                                                      let uu____3678 =
                                                        let uu____3680 =
                                                          FStar_TypeChecker_Rel.discharge_guard_no_smt
                                                            e g
                                                           in
                                                        FStar_All.pipe_left
                                                          FStar_TypeChecker_Env.is_trivial
                                                          uu____3680
                                                         in
                                                      Prims.op_Negation
                                                        uu____3678
                                                       in
                                                    if uu____3676
                                                    then
                                                      mlog
                                                        (fun uu____3687  ->
                                                           let uu____3688 =
                                                             FStar_TypeChecker_Rel.guard_to_string
                                                               e g
                                                              in
                                                           FStar_Util.print1
                                                             "guard = %s\n"
                                                             uu____3688)
                                                        (fun uu____3692  ->
                                                           fail1
                                                             "Forcing the guard failed (%s)"
                                                             reason)
                                                    else ret ()) ()
                                           with
                                           | uu___604_3697 ->
                                               mlog
                                                 (fun uu____3702  ->
                                                    let uu____3703 =
                                                      FStar_TypeChecker_Rel.guard_to_string
                                                        e g
                                                       in
                                                    FStar_Util.print1
                                                      "guard = %s\n"
                                                      uu____3703)
                                                 (fun uu____3707  ->
                                                    fail1
                                                      "Forcing the guard failed (%s)"
                                                      reason))))))
  
let (tcc : env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.comp tac) =
  fun e  ->
    fun t  ->
      let uu____3724 =
        let uu____3727 = __tc_lax e t  in
        bind uu____3727
          (fun uu____3747  ->
             match uu____3747 with
             | (uu____3756,lc,uu____3758) ->
                 let uu____3759 =
                   let uu____3760 = FStar_TypeChecker_Common.lcomp_comp lc
                      in
                   FStar_All.pipe_right uu____3760
                     FStar_Pervasives_Native.fst
                    in
                 ret uu____3759)
         in
      FStar_All.pipe_left (wrap_err "tcc") uu____3724
  
let (tc : env -> FStar_Syntax_Syntax.term -> FStar_Reflection_Data.typ tac) =
  fun e  ->
    fun t  ->
      let uu____3789 =
        let uu____3794 = tcc e t  in
        bind uu____3794 (fun c  -> ret (FStar_Syntax_Util.comp_result c))  in
      FStar_All.pipe_left (wrap_err "tc") uu____3789
  
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
            let uu____3846 = mk_irrelevant_goal reason env phi opts label1
               in
            bind uu____3846 (fun goal  -> add_goals [goal])
  
let (trivial : unit -> unit tac) =
  fun uu____3858  ->
    let uu____3861 = cur_goal ()  in
    bind uu____3861
      (fun goal  ->
         let uu____3867 =
           let uu____3869 = FStar_Tactics_Types.goal_env goal  in
           let uu____3870 = FStar_Tactics_Types.goal_type goal  in
           istrivial uu____3869 uu____3870  in
         if uu____3867
         then solve' goal FStar_Syntax_Util.exp_unit
         else
           (let uu____3876 =
              let uu____3878 = FStar_Tactics_Types.goal_env goal  in
              let uu____3879 = FStar_Tactics_Types.goal_type goal  in
              tts uu____3878 uu____3879  in
            fail1 "Not a trivial goal: %s" uu____3876))
  
let divide : 'a 'b . FStar_BigInt.t -> 'a tac -> 'b tac -> ('a * 'b) tac =
  fun n1  ->
    fun l  ->
      fun r  ->
        bind get
          (fun p  ->
             let uu____3930 =
               try
                 (fun uu___664_3953  ->
                    match () with
                    | () ->
                        let uu____3964 =
                          let uu____3973 = FStar_BigInt.to_int_fs n1  in
                          FStar_List.splitAt uu____3973
                            p.FStar_Tactics_Types.goals
                           in
                        ret uu____3964) ()
               with | uu___663_3984 -> fail "divide: not enough goals"  in
             bind uu____3930
               (fun uu____4021  ->
                  match uu____4021 with
                  | (lgs,rgs) ->
                      let lp =
                        let uu___646_4047 = p  in
                        {
                          FStar_Tactics_Types.main_context =
                            (uu___646_4047.FStar_Tactics_Types.main_context);
                          FStar_Tactics_Types.all_implicits =
                            (uu___646_4047.FStar_Tactics_Types.all_implicits);
                          FStar_Tactics_Types.goals = lgs;
                          FStar_Tactics_Types.smt_goals = [];
                          FStar_Tactics_Types.depth =
                            (uu___646_4047.FStar_Tactics_Types.depth);
                          FStar_Tactics_Types.__dump =
                            (uu___646_4047.FStar_Tactics_Types.__dump);
                          FStar_Tactics_Types.psc =
                            (uu___646_4047.FStar_Tactics_Types.psc);
                          FStar_Tactics_Types.entry_range =
                            (uu___646_4047.FStar_Tactics_Types.entry_range);
                          FStar_Tactics_Types.guard_policy =
                            (uu___646_4047.FStar_Tactics_Types.guard_policy);
                          FStar_Tactics_Types.freshness =
                            (uu___646_4047.FStar_Tactics_Types.freshness);
                          FStar_Tactics_Types.tac_verb_dbg =
                            (uu___646_4047.FStar_Tactics_Types.tac_verb_dbg);
                          FStar_Tactics_Types.local_state =
                            (uu___646_4047.FStar_Tactics_Types.local_state)
                        }  in
                      let uu____4048 = set lp  in
                      bind uu____4048
                        (fun uu____4056  ->
                           bind l
                             (fun a  ->
                                bind get
                                  (fun lp'  ->
                                     let rp =
                                       let uu___652_4072 = lp'  in
                                       {
                                         FStar_Tactics_Types.main_context =
                                           (uu___652_4072.FStar_Tactics_Types.main_context);
                                         FStar_Tactics_Types.all_implicits =
                                           (uu___652_4072.FStar_Tactics_Types.all_implicits);
                                         FStar_Tactics_Types.goals = rgs;
                                         FStar_Tactics_Types.smt_goals = [];
                                         FStar_Tactics_Types.depth =
                                           (uu___652_4072.FStar_Tactics_Types.depth);
                                         FStar_Tactics_Types.__dump =
                                           (uu___652_4072.FStar_Tactics_Types.__dump);
                                         FStar_Tactics_Types.psc =
                                           (uu___652_4072.FStar_Tactics_Types.psc);
                                         FStar_Tactics_Types.entry_range =
                                           (uu___652_4072.FStar_Tactics_Types.entry_range);
                                         FStar_Tactics_Types.guard_policy =
                                           (uu___652_4072.FStar_Tactics_Types.guard_policy);
                                         FStar_Tactics_Types.freshness =
                                           (uu___652_4072.FStar_Tactics_Types.freshness);
                                         FStar_Tactics_Types.tac_verb_dbg =
                                           (uu___652_4072.FStar_Tactics_Types.tac_verb_dbg);
                                         FStar_Tactics_Types.local_state =
                                           (uu___652_4072.FStar_Tactics_Types.local_state)
                                       }  in
                                     let uu____4073 = set rp  in
                                     bind uu____4073
                                       (fun uu____4081  ->
                                          bind r
                                            (fun b  ->
                                               bind get
                                                 (fun rp'  ->
                                                    let p' =
                                                      let uu___658_4097 = rp'
                                                         in
                                                      {
                                                        FStar_Tactics_Types.main_context
                                                          =
                                                          (uu___658_4097.FStar_Tactics_Types.main_context);
                                                        FStar_Tactics_Types.all_implicits
                                                          =
                                                          (uu___658_4097.FStar_Tactics_Types.all_implicits);
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
                                                          (uu___658_4097.FStar_Tactics_Types.depth);
                                                        FStar_Tactics_Types.__dump
                                                          =
                                                          (uu___658_4097.FStar_Tactics_Types.__dump);
                                                        FStar_Tactics_Types.psc
                                                          =
                                                          (uu___658_4097.FStar_Tactics_Types.psc);
                                                        FStar_Tactics_Types.entry_range
                                                          =
                                                          (uu___658_4097.FStar_Tactics_Types.entry_range);
                                                        FStar_Tactics_Types.guard_policy
                                                          =
                                                          (uu___658_4097.FStar_Tactics_Types.guard_policy);
                                                        FStar_Tactics_Types.freshness
                                                          =
                                                          (uu___658_4097.FStar_Tactics_Types.freshness);
                                                        FStar_Tactics_Types.tac_verb_dbg
                                                          =
                                                          (uu___658_4097.FStar_Tactics_Types.tac_verb_dbg);
                                                        FStar_Tactics_Types.local_state
                                                          =
                                                          (uu___658_4097.FStar_Tactics_Types.local_state)
                                                      }  in
                                                    let uu____4098 = set p'
                                                       in
                                                    bind uu____4098
                                                      (fun uu____4106  ->
                                                         bind
                                                           remove_solved_goals
                                                           (fun uu____4112 
                                                              -> ret (a, b)))))))))))
  
let focus : 'a . 'a tac -> 'a tac =
  fun f  ->
    let uu____4134 = divide FStar_BigInt.one f idtac  in
    bind uu____4134
      (fun uu____4147  -> match uu____4147 with | (a,()) -> ret a)
  
let rec map : 'a . 'a tac -> 'a Prims.list tac =
  fun tau  ->
    bind get
      (fun p  ->
         match p.FStar_Tactics_Types.goals with
         | [] -> ret []
         | uu____4185::uu____4186 ->
             let uu____4189 =
               let uu____4198 = map tau  in
               divide FStar_BigInt.one tau uu____4198  in
             bind uu____4189
               (fun uu____4216  ->
                  match uu____4216 with | (h,t) -> ret (h :: t)))
  
let (seq : unit tac -> unit tac -> unit tac) =
  fun t1  ->
    fun t2  ->
      let uu____4258 =
        bind t1
          (fun uu____4263  ->
             let uu____4264 = map t2  in
             bind uu____4264 (fun uu____4272  -> ret ()))
         in
      focus uu____4258
  
let (intro : unit -> FStar_Syntax_Syntax.binder tac) =
  fun uu____4282  ->
    let uu____4285 =
      let uu____4288 = cur_goal ()  in
      bind uu____4288
        (fun goal  ->
           let uu____4297 =
             let uu____4304 = FStar_Tactics_Types.goal_type goal  in
             FStar_Syntax_Util.arrow_one uu____4304  in
           match uu____4297 with
           | FStar_Pervasives_Native.Some (b,c) ->
               let uu____4313 =
                 let uu____4315 = FStar_Syntax_Util.is_total_comp c  in
                 Prims.op_Negation uu____4315  in
               if uu____4313
               then fail "Codomain is effectful"
               else
                 (let env' =
                    let uu____4324 = FStar_Tactics_Types.goal_env goal  in
                    FStar_TypeChecker_Env.push_binders uu____4324 [b]  in
                  let typ' = FStar_Syntax_Util.comp_result c  in
                  let uu____4340 = new_uvar "intro" env' typ'  in
                  bind uu____4340
                    (fun uu____4357  ->
                       match uu____4357 with
                       | (body,ctx_uvar) ->
                           let sol =
                             FStar_Syntax_Util.abs [b] body
                               (FStar_Pervasives_Native.Some
                                  (FStar_Syntax_Util.residual_comp_of_comp c))
                              in
                           let uu____4381 = set_solution goal sol  in
                           bind uu____4381
                             (fun uu____4387  ->
                                let g =
                                  FStar_Tactics_Types.mk_goal env' ctx_uvar
                                    goal.FStar_Tactics_Types.opts
                                    goal.FStar_Tactics_Types.is_guard
                                    goal.FStar_Tactics_Types.label
                                   in
                                let uu____4389 =
                                  let uu____4392 = bnorm_goal g  in
                                  replace_cur uu____4392  in
                                bind uu____4389 (fun uu____4394  -> ret b))))
           | FStar_Pervasives_Native.None  ->
               let uu____4399 =
                 let uu____4401 = FStar_Tactics_Types.goal_env goal  in
                 let uu____4402 = FStar_Tactics_Types.goal_type goal  in
                 tts uu____4401 uu____4402  in
               fail1 "goal is not an arrow (%s)" uu____4399)
       in
    FStar_All.pipe_left (wrap_err "intro") uu____4285
  
let (intro_rec :
  unit -> (FStar_Syntax_Syntax.binder * FStar_Syntax_Syntax.binder) tac) =
  fun uu____4420  ->
    let uu____4427 = cur_goal ()  in
    bind uu____4427
      (fun goal  ->
         FStar_Util.print_string
           "WARNING (intro_rec): calling this is known to cause normalizer loops\n";
         FStar_Util.print_string
           "WARNING (intro_rec): proceed at your own risk...\n";
         (let uu____4446 =
            let uu____4453 = FStar_Tactics_Types.goal_type goal  in
            FStar_Syntax_Util.arrow_one uu____4453  in
          match uu____4446 with
          | FStar_Pervasives_Native.Some (b,c) ->
              let uu____4466 =
                let uu____4468 = FStar_Syntax_Util.is_total_comp c  in
                Prims.op_Negation uu____4468  in
              if uu____4466
              then fail "Codomain is effectful"
              else
                (let bv =
                   let uu____4485 = FStar_Tactics_Types.goal_type goal  in
                   FStar_Syntax_Syntax.gen_bv "__recf"
                     FStar_Pervasives_Native.None uu____4485
                    in
                 let bs =
                   let uu____4496 = FStar_Syntax_Syntax.mk_binder bv  in
                   [uu____4496; b]  in
                 let env' =
                   let uu____4522 = FStar_Tactics_Types.goal_env goal  in
                   FStar_TypeChecker_Env.push_binders uu____4522 bs  in
                 let uu____4523 =
                   new_uvar "intro_rec" env'
                     (FStar_Syntax_Util.comp_result c)
                    in
                 bind uu____4523
                   (fun uu____4549  ->
                      match uu____4549 with
                      | (u,ctx_uvar_u) ->
                          let lb =
                            let uu____4563 =
                              FStar_Tactics_Types.goal_type goal  in
                            let uu____4566 =
                              FStar_Syntax_Util.abs [b] u
                                FStar_Pervasives_Native.None
                               in
                            FStar_Syntax_Util.mk_letbinding
                              (FStar_Util.Inl bv) [] uu____4563
                              FStar_Parser_Const.effect_Tot_lid uu____4566 []
                              FStar_Range.dummyRange
                             in
                          let body = FStar_Syntax_Syntax.bv_to_name bv  in
                          let uu____4584 =
                            FStar_Syntax_Subst.close_let_rec [lb] body  in
                          (match uu____4584 with
                           | (lbs,body1) ->
                               let tm =
                                 let uu____4606 =
                                   let uu____4607 =
                                     FStar_Tactics_Types.goal_witness goal
                                      in
                                   uu____4607.FStar_Syntax_Syntax.pos  in
                                 FStar_Syntax_Syntax.mk
                                   (FStar_Syntax_Syntax.Tm_let
                                      ((true, lbs), body1))
                                   FStar_Pervasives_Native.None uu____4606
                                  in
                               let uu____4623 = set_solution goal tm  in
                               bind uu____4623
                                 (fun uu____4632  ->
                                    let uu____4633 =
                                      let uu____4636 =
                                        bnorm_goal
                                          (let uu___729_4639 = goal  in
                                           {
                                             FStar_Tactics_Types.goal_main_env
                                               =
                                               (uu___729_4639.FStar_Tactics_Types.goal_main_env);
                                             FStar_Tactics_Types.goal_ctx_uvar
                                               = ctx_uvar_u;
                                             FStar_Tactics_Types.opts =
                                               (uu___729_4639.FStar_Tactics_Types.opts);
                                             FStar_Tactics_Types.is_guard =
                                               (uu___729_4639.FStar_Tactics_Types.is_guard);
                                             FStar_Tactics_Types.label =
                                               (uu___729_4639.FStar_Tactics_Types.label)
                                           })
                                         in
                                      replace_cur uu____4636  in
                                    bind uu____4633
                                      (fun uu____4646  ->
                                         let uu____4647 =
                                           let uu____4652 =
                                             FStar_Syntax_Syntax.mk_binder bv
                                              in
                                           (uu____4652, b)  in
                                         ret uu____4647)))))
          | FStar_Pervasives_Native.None  ->
              let uu____4661 =
                let uu____4663 = FStar_Tactics_Types.goal_env goal  in
                let uu____4664 = FStar_Tactics_Types.goal_type goal  in
                tts uu____4663 uu____4664  in
              fail1 "intro_rec: goal is not an arrow (%s)" uu____4661))
  
let (norm : FStar_Syntax_Embeddings.norm_step Prims.list -> unit tac) =
  fun s  ->
    let uu____4684 = cur_goal ()  in
    bind uu____4684
      (fun goal  ->
         mlog
           (fun uu____4691  ->
              let uu____4692 =
                let uu____4694 = FStar_Tactics_Types.goal_witness goal  in
                FStar_Syntax_Print.term_to_string uu____4694  in
              FStar_Util.print1 "norm: witness = %s\n" uu____4692)
           (fun uu____4700  ->
              let steps =
                let uu____4704 = FStar_TypeChecker_Normalize.tr_norm_steps s
                   in
                FStar_List.append
                  [FStar_TypeChecker_Env.Reify;
                  FStar_TypeChecker_Env.UnfoldTac] uu____4704
                 in
              let t =
                let uu____4708 = FStar_Tactics_Types.goal_env goal  in
                let uu____4709 = FStar_Tactics_Types.goal_type goal  in
                normalize steps uu____4708 uu____4709  in
              let uu____4710 = FStar_Tactics_Types.goal_with_type goal t  in
              replace_cur uu____4710))
  
let (norm_term_env :
  env ->
    FStar_Syntax_Embeddings.norm_step Prims.list ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term tac)
  =
  fun e  ->
    fun s  ->
      fun t  ->
        let uu____4735 =
          bind get
            (fun ps  ->
               let opts =
                 match ps.FStar_Tactics_Types.goals with
                 | g::uu____4743 -> g.FStar_Tactics_Types.opts
                 | uu____4746 -> FStar_Options.peek ()  in
               mlog
                 (fun uu____4751  ->
                    let uu____4752 = FStar_Syntax_Print.term_to_string t  in
                    FStar_Util.print1 "norm_term_env: t = %s\n" uu____4752)
                 (fun uu____4757  ->
                    let uu____4758 = __tc_lax e t  in
                    bind uu____4758
                      (fun uu____4779  ->
                         match uu____4779 with
                         | (t1,uu____4789,uu____4790) ->
                             let steps =
                               let uu____4794 =
                                 FStar_TypeChecker_Normalize.tr_norm_steps s
                                  in
                               FStar_List.append
                                 [FStar_TypeChecker_Env.Reify;
                                 FStar_TypeChecker_Env.UnfoldTac] uu____4794
                                in
                             let t2 =
                               normalize steps
                                 ps.FStar_Tactics_Types.main_context t1
                                in
                             mlog
                               (fun uu____4800  ->
                                  let uu____4801 =
                                    FStar_Syntax_Print.term_to_string t2  in
                                  FStar_Util.print1
                                    "norm_term_env: t' = %s\n" uu____4801)
                               (fun uu____4805  -> ret t2))))
           in
        FStar_All.pipe_left (wrap_err "norm_term") uu____4735
  
let (refine_intro : unit -> unit tac) =
  fun uu____4818  ->
    let uu____4821 =
      let uu____4824 = cur_goal ()  in
      bind uu____4824
        (fun g  ->
           let uu____4831 =
             let uu____4842 = FStar_Tactics_Types.goal_env g  in
             let uu____4843 = FStar_Tactics_Types.goal_type g  in
             FStar_TypeChecker_Rel.base_and_refinement uu____4842 uu____4843
              in
           match uu____4831 with
           | (uu____4846,FStar_Pervasives_Native.None ) ->
               fail "not a refinement"
           | (t,FStar_Pervasives_Native.Some (bv,phi)) ->
               let g1 = FStar_Tactics_Types.goal_with_type g t  in
               let uu____4872 =
                 let uu____4877 =
                   let uu____4882 =
                     let uu____4883 = FStar_Syntax_Syntax.mk_binder bv  in
                     [uu____4883]  in
                   FStar_Syntax_Subst.open_term uu____4882 phi  in
                 match uu____4877 with
                 | (bvs,phi1) ->
                     let uu____4908 =
                       let uu____4909 = FStar_List.hd bvs  in
                       FStar_Pervasives_Native.fst uu____4909  in
                     (uu____4908, phi1)
                  in
               (match uu____4872 with
                | (bv1,phi1) ->
                    let uu____4928 =
                      let uu____4931 = FStar_Tactics_Types.goal_env g  in
                      let uu____4932 =
                        let uu____4933 =
                          let uu____4936 =
                            let uu____4937 =
                              let uu____4944 =
                                FStar_Tactics_Types.goal_witness g  in
                              (bv1, uu____4944)  in
                            FStar_Syntax_Syntax.NT uu____4937  in
                          [uu____4936]  in
                        FStar_Syntax_Subst.subst uu____4933 phi1  in
                      mk_irrelevant_goal "refine_intro refinement" uu____4931
                        uu____4932 g.FStar_Tactics_Types.opts
                        g.FStar_Tactics_Types.label
                       in
                    bind uu____4928
                      (fun g2  ->
                         bind __dismiss
                           (fun uu____4953  -> add_goals [g1; g2]))))
       in
    FStar_All.pipe_left (wrap_err "refine_intro") uu____4821
  
let (__exact_now : Prims.bool -> FStar_Syntax_Syntax.term -> unit tac) =
  fun set_expected_typ1  ->
    fun t  ->
      let uu____4976 = cur_goal ()  in
      bind uu____4976
        (fun goal  ->
           let env =
             if set_expected_typ1
             then
               let uu____4985 = FStar_Tactics_Types.goal_env goal  in
               let uu____4986 = FStar_Tactics_Types.goal_type goal  in
               FStar_TypeChecker_Env.set_expected_typ uu____4985 uu____4986
             else FStar_Tactics_Types.goal_env goal  in
           let uu____4989 = __tc env t  in
           bind uu____4989
             (fun uu____5008  ->
                match uu____5008 with
                | (t1,typ,guard) ->
                    mlog
                      (fun uu____5023  ->
                         let uu____5024 =
                           FStar_Syntax_Print.term_to_string typ  in
                         let uu____5026 =
                           let uu____5028 = FStar_Tactics_Types.goal_env goal
                              in
                           FStar_TypeChecker_Rel.guard_to_string uu____5028
                             guard
                            in
                         FStar_Util.print2
                           "__exact_now: got type %s\n__exact_now: and guard %s\n"
                           uu____5024 uu____5026)
                      (fun uu____5032  ->
                         let uu____5033 =
                           let uu____5036 = FStar_Tactics_Types.goal_env goal
                              in
                           proc_guard "__exact typing" uu____5036 guard  in
                         bind uu____5033
                           (fun uu____5039  ->
                              mlog
                                (fun uu____5043  ->
                                   let uu____5044 =
                                     FStar_Syntax_Print.term_to_string typ
                                      in
                                   let uu____5046 =
                                     let uu____5048 =
                                       FStar_Tactics_Types.goal_type goal  in
                                     FStar_Syntax_Print.term_to_string
                                       uu____5048
                                      in
                                   FStar_Util.print2
                                     "__exact_now: unifying %s and %s\n"
                                     uu____5044 uu____5046)
                                (fun uu____5052  ->
                                   let uu____5053 =
                                     let uu____5057 =
                                       FStar_Tactics_Types.goal_env goal  in
                                     let uu____5058 =
                                       FStar_Tactics_Types.goal_type goal  in
                                     do_unify uu____5057 typ uu____5058  in
                                   bind uu____5053
                                     (fun b  ->
                                        if b
                                        then solve goal t1
                                        else
                                          (let uu____5068 =
                                             let uu____5075 =
                                               let uu____5081 =
                                                 FStar_Tactics_Types.goal_env
                                                   goal
                                                  in
                                               tts uu____5081  in
                                             let uu____5082 =
                                               FStar_Tactics_Types.goal_type
                                                 goal
                                                in
                                             FStar_TypeChecker_Err.print_discrepancy
                                               uu____5075 typ uu____5082
                                              in
                                           match uu____5068 with
                                           | (typ1,goalt) ->
                                               let uu____5091 =
                                                 let uu____5093 =
                                                   FStar_Tactics_Types.goal_env
                                                     goal
                                                    in
                                                 tts uu____5093 t1  in
                                               let uu____5094 =
                                                 let uu____5096 =
                                                   FStar_Tactics_Types.goal_env
                                                     goal
                                                    in
                                                 let uu____5097 =
                                                   FStar_Tactics_Types.goal_witness
                                                     goal
                                                    in
                                                 tts uu____5096 uu____5097
                                                  in
                                               fail4
                                                 "%s : %s does not exactly solve the goal %s (witness = %s)"
                                                 uu____5091 typ1 goalt
                                                 uu____5094)))))))
  
let (t_exact :
  Prims.bool -> Prims.bool -> FStar_Syntax_Syntax.term -> unit tac) =
  fun try_refine  ->
    fun set_expected_typ1  ->
      fun tm  ->
        let uu____5123 =
          mlog
            (fun uu____5128  ->
               let uu____5129 = FStar_Syntax_Print.term_to_string tm  in
               FStar_Util.print1 "t_exact: tm = %s\n" uu____5129)
            (fun uu____5134  ->
               let uu____5135 =
                 let uu____5142 = __exact_now set_expected_typ1 tm  in
                 catch uu____5142  in
               bind uu____5135
                 (fun uu___2_5151  ->
                    match uu___2_5151 with
                    | FStar_Util.Inr r -> ret ()
                    | FStar_Util.Inl e when Prims.op_Negation try_refine ->
                        traise e
                    | FStar_Util.Inl e ->
                        mlog
                          (fun uu____5162  ->
                             FStar_Util.print_string
                               "__exact_now failed, trying refine...\n")
                          (fun uu____5166  ->
                             let uu____5167 =
                               let uu____5174 =
                                 let uu____5177 =
                                   norm [FStar_Syntax_Embeddings.Delta]  in
                                 bind uu____5177
                                   (fun uu____5182  ->
                                      let uu____5183 = refine_intro ()  in
                                      bind uu____5183
                                        (fun uu____5187  ->
                                           __exact_now set_expected_typ1 tm))
                                  in
                               catch uu____5174  in
                             bind uu____5167
                               (fun uu___1_5194  ->
                                  match uu___1_5194 with
                                  | FStar_Util.Inr r ->
                                      mlog
                                        (fun uu____5203  ->
                                           FStar_Util.print_string
                                             "__exact_now: failed after refining too\n")
                                        (fun uu____5206  -> ret ())
                                  | FStar_Util.Inl uu____5207 ->
                                      mlog
                                        (fun uu____5209  ->
                                           FStar_Util.print_string
                                             "__exact_now: was not a refinement\n")
                                        (fun uu____5212  -> traise e)))))
           in
        FStar_All.pipe_left (wrap_err "exact") uu____5123
  
let rec mapM : 'a 'b . ('a -> 'b tac) -> 'a Prims.list -> 'b Prims.list tac =
  fun f  ->
    fun l  ->
      match l with
      | [] -> ret []
      | x::xs ->
          let uu____5264 = f x  in
          bind uu____5264
            (fun y  ->
               let uu____5272 = mapM f xs  in
               bind uu____5272 (fun ys  -> ret (y :: ys)))
  
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
            let uu____5382 = f e ty2 ty1  in
            bind uu____5382
              (fun uu___3_5396  ->
                 if uu___3_5396
                 then ret acc
                 else
                   (let uu____5416 = FStar_Syntax_Util.arrow_one ty1  in
                    match uu____5416 with
                    | FStar_Pervasives_Native.None  ->
                        let uu____5437 =
                          FStar_Syntax_Print.term_to_string ty1  in
                        let uu____5439 =
                          FStar_Syntax_Print.term_to_string ty2  in
                        fail2 "Could not instantiate, %s to %s" uu____5437
                          uu____5439
                    | FStar_Pervasives_Native.Some (b,c) ->
                        let uu____5456 =
                          let uu____5458 = FStar_Syntax_Util.is_total_comp c
                             in
                          Prims.op_Negation uu____5458  in
                        if uu____5456
                        then fail "Codomain is effectful"
                        else
                          (let uu____5482 =
                             new_uvar "apply arg" e
                               (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                              in
                           bind uu____5482
                             (fun uu____5507  ->
                                match uu____5507 with
                                | (uvt,uv) ->
                                    mlog
                                      (fun uu____5534  ->
                                         let uu____5535 =
                                           FStar_Syntax_Print.ctx_uvar_to_string
                                             uv
                                            in
                                         FStar_Util.print1
                                           "t_apply: generated uvar %s\n"
                                           uu____5535)
                                      (fun uu____5541  ->
                                         let typ =
                                           FStar_Syntax_Util.comp_result c
                                            in
                                         let typ' =
                                           FStar_Syntax_Subst.subst
                                             [FStar_Syntax_Syntax.NT
                                                ((FStar_Pervasives_Native.fst
                                                    b), uvt)] typ
                                            in
                                         __try_unify_by_application
                                           only_match
                                           ((uvt,
                                              (FStar_Pervasives_Native.snd b),
                                              uv) :: acc) e typ' ty2)))))
  
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
        let uu____5631 =
          let uu____5634 = cur_goal ()  in
          bind uu____5634
            (fun goal  ->
               let e = FStar_Tactics_Types.goal_env goal  in
               mlog
                 (fun uu____5645  ->
                    let uu____5646 = FStar_Syntax_Print.term_to_string tm  in
                    let uu____5648 = goal_to_string_verbose goal  in
                    let uu____5650 =
                      FStar_TypeChecker_Env.print_gamma
                        e.FStar_TypeChecker_Env.gamma
                       in
                    FStar_Util.print3
                      "t_apply: tm = %s\nt_apply: goal = %s\nenv.gamma=%s\n"
                      uu____5646 uu____5648 uu____5650)
                 (fun uu____5655  ->
                    let uu____5656 = __tc e tm  in
                    bind uu____5656
                      (fun uu____5677  ->
                         match uu____5677 with
                         | (tm1,typ,guard) ->
                             let typ1 = bnorm e typ  in
                             let uu____5690 =
                               let uu____5701 =
                                 FStar_Tactics_Types.goal_type goal  in
                               try_unify_by_application only_match e typ1
                                 uu____5701
                                in
                             bind uu____5690
                               (fun uvs  ->
                                  mlog
                                    (fun uu____5722  ->
                                       let uu____5723 =
                                         FStar_Common.string_of_list
                                           (fun uu____5735  ->
                                              match uu____5735 with
                                              | (t,uu____5744,uu____5745) ->
                                                  FStar_Syntax_Print.term_to_string
                                                    t) uvs
                                          in
                                       FStar_Util.print1
                                         "t_apply: found args = %s\n"
                                         uu____5723)
                                    (fun uu____5753  ->
                                       let fix_qual q =
                                         match q with
                                         | FStar_Pervasives_Native.Some
                                             (FStar_Syntax_Syntax.Meta
                                             uu____5768) ->
                                             FStar_Pervasives_Native.Some
                                               (FStar_Syntax_Syntax.Implicit
                                                  false)
                                         | uu____5770 -> q  in
                                       let w =
                                         FStar_List.fold_right
                                           (fun uu____5793  ->
                                              fun w  ->
                                                match uu____5793 with
                                                | (uvt,q,uu____5811) ->
                                                    FStar_Syntax_Util.mk_app
                                                      w [(uvt, (fix_qual q))])
                                           uvs tm1
                                          in
                                       let uvset =
                                         let uu____5843 =
                                           FStar_Syntax_Free.new_uv_set ()
                                            in
                                         FStar_List.fold_right
                                           (fun uu____5860  ->
                                              fun s  ->
                                                match uu____5860 with
                                                | (uu____5872,uu____5873,uv)
                                                    ->
                                                    let uu____5875 =
                                                      FStar_Syntax_Free.uvars
                                                        uv.FStar_Syntax_Syntax.ctx_uvar_typ
                                                       in
                                                    FStar_Util.set_union s
                                                      uu____5875) uvs
                                           uu____5843
                                          in
                                       let free_in_some_goal uv =
                                         FStar_Util.set_mem uv uvset  in
                                       let uu____5885 = solve' goal w  in
                                       bind uu____5885
                                         (fun uu____5890  ->
                                            let uu____5891 =
                                              mapM
                                                (fun uu____5908  ->
                                                   match uu____5908 with
                                                   | (uvt,q,uv) ->
                                                       let uu____5920 =
                                                         FStar_Syntax_Unionfind.find
                                                           uv.FStar_Syntax_Syntax.ctx_uvar_head
                                                          in
                                                       (match uu____5920 with
                                                        | FStar_Pervasives_Native.Some
                                                            uu____5925 ->
                                                            ret ()
                                                        | FStar_Pervasives_Native.None
                                                             ->
                                                            let uu____5926 =
                                                              uopt &&
                                                                (free_in_some_goal
                                                                   uv)
                                                               in
                                                            if uu____5926
                                                            then ret ()
                                                            else
                                                              (let uu____5933
                                                                 =
                                                                 let uu____5936
                                                                   =
                                                                   bnorm_goal
                                                                    (let uu___901_5939
                                                                    = goal
                                                                     in
                                                                    {
                                                                    FStar_Tactics_Types.goal_main_env
                                                                    =
                                                                    (uu___901_5939.FStar_Tactics_Types.goal_main_env);
                                                                    FStar_Tactics_Types.goal_ctx_uvar
                                                                    = uv;
                                                                    FStar_Tactics_Types.opts
                                                                    =
                                                                    (uu___901_5939.FStar_Tactics_Types.opts);
                                                                    FStar_Tactics_Types.is_guard
                                                                    = false;
                                                                    FStar_Tactics_Types.label
                                                                    =
                                                                    (uu___901_5939.FStar_Tactics_Types.label)
                                                                    })
                                                                    in
                                                                 [uu____5936]
                                                                  in
                                                               add_goals
                                                                 uu____5933)))
                                                uvs
                                               in
                                            bind uu____5891
                                              (fun uu____5944  ->
                                                 proc_guard "apply guard" e
                                                   guard)))))))
           in
        FStar_All.pipe_left (wrap_err "apply") uu____5631
  
let (lemma_or_sq :
  FStar_Syntax_Syntax.comp ->
    (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.option)
  =
  fun c  ->
    let ct = FStar_Syntax_Util.comp_to_comp_typ_nouniv c  in
    let uu____5972 =
      FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
        FStar_Parser_Const.effect_Lemma_lid
       in
    if uu____5972
    then
      let uu____5981 =
        match ct.FStar_Syntax_Syntax.effect_args with
        | pre::post::uu____5996 ->
            ((FStar_Pervasives_Native.fst pre),
              (FStar_Pervasives_Native.fst post))
        | uu____6049 -> failwith "apply_lemma: impossible: not a lemma"  in
      match uu____5981 with
      | (pre,post) ->
          let post1 =
            let uu____6082 =
              let uu____6093 =
                FStar_Syntax_Syntax.as_arg FStar_Syntax_Util.exp_unit  in
              [uu____6093]  in
            FStar_Syntax_Util.mk_app post uu____6082  in
          FStar_Pervasives_Native.Some (pre, post1)
    else
      (let uu____6124 =
         FStar_Syntax_Util.is_pure_effect ct.FStar_Syntax_Syntax.effect_name
          in
       if uu____6124
       then
         let uu____6133 =
           FStar_Syntax_Util.un_squash ct.FStar_Syntax_Syntax.result_typ  in
         FStar_Util.map_opt uu____6133
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
            let uu____6212 = f x e  in
            bind uu____6212 (fun e'  -> fold_left f e' xs1)
  
let (apply_lemma : FStar_Syntax_Syntax.term -> unit tac) =
  fun tm  ->
    let uu____6227 =
      let uu____6230 =
        bind get
          (fun ps  ->
             mlog
               (fun uu____6237  ->
                  let uu____6238 = FStar_Syntax_Print.term_to_string tm  in
                  FStar_Util.print1 "apply_lemma: tm = %s\n" uu____6238)
               (fun uu____6244  ->
                  let is_unit_t t =
                    let uu____6252 =
                      let uu____6253 = FStar_Syntax_Subst.compress t  in
                      uu____6253.FStar_Syntax_Syntax.n  in
                    match uu____6252 with
                    | FStar_Syntax_Syntax.Tm_fvar fv when
                        FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.unit_lid
                        -> true
                    | uu____6259 -> false  in
                  let uu____6261 = cur_goal ()  in
                  bind uu____6261
                    (fun goal  ->
                       let uu____6267 =
                         let uu____6276 = FStar_Tactics_Types.goal_env goal
                            in
                         __tc uu____6276 tm  in
                       bind uu____6267
                         (fun uu____6291  ->
                            match uu____6291 with
                            | (tm1,t,guard) ->
                                let uu____6303 =
                                  FStar_Syntax_Util.arrow_formals_comp t  in
                                (match uu____6303 with
                                 | (bs,comp) ->
                                     let uu____6312 = lemma_or_sq comp  in
                                     (match uu____6312 with
                                      | FStar_Pervasives_Native.None  ->
                                          fail
                                            "not a lemma or squashed function"
                                      | FStar_Pervasives_Native.Some
                                          (pre,post) ->
                                          let uu____6332 =
                                            fold_left
                                              (fun uu____6394  ->
                                                 fun uu____6395  ->
                                                   match (uu____6394,
                                                           uu____6395)
                                                   with
                                                   | ((b,aq),(uvs,imps,subst1))
                                                       ->
                                                       let b_t =
                                                         FStar_Syntax_Subst.subst
                                                           subst1
                                                           b.FStar_Syntax_Syntax.sort
                                                          in
                                                       let uu____6546 =
                                                         is_unit_t b_t  in
                                                       if uu____6546
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
                                                         (let uu____6669 =
                                                            let uu____6676 =
                                                              FStar_Tactics_Types.goal_env
                                                                goal
                                                               in
                                                            new_uvar
                                                              "apply_lemma"
                                                              uu____6676 b_t
                                                             in
                                                          bind uu____6669
                                                            (fun uu____6707 
                                                               ->
                                                               match uu____6707
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
                                          bind uu____6332
                                            (fun uu____6893  ->
                                               match uu____6893 with
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
                                                   let uu____6981 =
                                                     let uu____6985 =
                                                       FStar_Tactics_Types.goal_env
                                                         goal
                                                        in
                                                     let uu____6986 =
                                                       FStar_Syntax_Util.mk_squash
                                                         FStar_Syntax_Syntax.U_zero
                                                         post1
                                                        in
                                                     let uu____6987 =
                                                       FStar_Tactics_Types.goal_type
                                                         goal
                                                        in
                                                     do_unify uu____6985
                                                       uu____6986 uu____6987
                                                      in
                                                   bind uu____6981
                                                     (fun b  ->
                                                        if
                                                          Prims.op_Negation b
                                                        then
                                                          let uu____6999 =
                                                            let uu____7006 =
                                                              let uu____7012
                                                                =
                                                                FStar_Tactics_Types.goal_env
                                                                  goal
                                                                 in
                                                              tts uu____7012
                                                               in
                                                            let uu____7013 =
                                                              FStar_Syntax_Util.mk_squash
                                                                FStar_Syntax_Syntax.U_zero
                                                                post1
                                                               in
                                                            let uu____7014 =
                                                              FStar_Tactics_Types.goal_type
                                                                goal
                                                               in
                                                            FStar_TypeChecker_Err.print_discrepancy
                                                              uu____7006
                                                              uu____7013
                                                              uu____7014
                                                             in
                                                          match uu____6999
                                                          with
                                                          | (post2,goalt) ->
                                                              let uu____7023
                                                                =
                                                                let uu____7025
                                                                  =
                                                                  FStar_Tactics_Types.goal_env
                                                                    goal
                                                                   in
                                                                tts
                                                                  uu____7025
                                                                  tm1
                                                                 in
                                                              fail3
                                                                "Cannot instantiate lemma %s (with postcondition: %s) to match goal (%s)"
                                                                uu____7023
                                                                post2 goalt
                                                        else
                                                          (let uu____7029 =
                                                             solve' goal
                                                               FStar_Syntax_Util.exp_unit
                                                              in
                                                           bind uu____7029
                                                             (fun uu____7037 
                                                                ->
                                                                let is_free_uvar
                                                                  uv t1 =
                                                                  let free_uvars
                                                                    =
                                                                    let uu____7063
                                                                    =
                                                                    let uu____7066
                                                                    =
                                                                    FStar_Syntax_Free.uvars
                                                                    t1  in
                                                                    FStar_Util.set_elements
                                                                    uu____7066
                                                                     in
                                                                    FStar_List.map
                                                                    (fun x 
                                                                    ->
                                                                    x.FStar_Syntax_Syntax.ctx_uvar_head)
                                                                    uu____7063
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
                                                                    let uu____7102
                                                                    =
                                                                    FStar_Tactics_Types.goal_type
                                                                    g'  in
                                                                    is_free_uvar
                                                                    uv
                                                                    uu____7102)
                                                                    goals
                                                                   in
                                                                let checkone
                                                                  t1 goals =
                                                                  let uu____7119
                                                                    =
                                                                    FStar_Syntax_Util.head_and_args
                                                                    t1  in
                                                                  match uu____7119
                                                                  with
                                                                  | (hd1,uu____7138)
                                                                    ->
                                                                    (match 
                                                                    hd1.FStar_Syntax_Syntax.n
                                                                    with
                                                                    | 
                                                                    FStar_Syntax_Syntax.Tm_uvar
                                                                    (uv,uu____7165)
                                                                    ->
                                                                    appears
                                                                    uv.FStar_Syntax_Syntax.ctx_uvar_head
                                                                    goals
                                                                    | 
                                                                    uu____7182
                                                                    -> false)
                                                                   in
                                                                let uu____7184
                                                                  =
                                                                  FStar_All.pipe_right
                                                                    implicits1
                                                                    (
                                                                    mapM
                                                                    (fun imp 
                                                                    ->
                                                                    let uu____7225
                                                                    = imp  in
                                                                    match uu____7225
                                                                    with
                                                                    | 
                                                                    (term,ctx_uvar)
                                                                    ->
                                                                    let uu____7236
                                                                    =
                                                                    FStar_Syntax_Util.head_and_args
                                                                    term  in
                                                                    (match uu____7236
                                                                    with
                                                                    | 
                                                                    (hd1,uu____7258)
                                                                    ->
                                                                    let uu____7283
                                                                    =
                                                                    let uu____7284
                                                                    =
                                                                    FStar_Syntax_Subst.compress
                                                                    hd1  in
                                                                    uu____7284.FStar_Syntax_Syntax.n
                                                                     in
                                                                    (match uu____7283
                                                                    with
                                                                    | 
                                                                    FStar_Syntax_Syntax.Tm_uvar
                                                                    (ctx_uvar1,uu____7292)
                                                                    ->
                                                                    let goal1
                                                                    =
                                                                    bnorm_goal
                                                                    (let uu___1018_7312
                                                                    = goal
                                                                     in
                                                                    {
                                                                    FStar_Tactics_Types.goal_main_env
                                                                    =
                                                                    (uu___1018_7312.FStar_Tactics_Types.goal_main_env);
                                                                    FStar_Tactics_Types.goal_ctx_uvar
                                                                    =
                                                                    ctx_uvar1;
                                                                    FStar_Tactics_Types.opts
                                                                    =
                                                                    (uu___1018_7312.FStar_Tactics_Types.opts);
                                                                    FStar_Tactics_Types.is_guard
                                                                    =
                                                                    (uu___1018_7312.FStar_Tactics_Types.is_guard);
                                                                    FStar_Tactics_Types.label
                                                                    =
                                                                    (uu___1018_7312.FStar_Tactics_Types.label)
                                                                    })  in
                                                                    ret
                                                                    [goal1]
                                                                    | 
                                                                    uu____7315
                                                                    ->
                                                                    mlog
                                                                    (fun
                                                                    uu____7321
                                                                     ->
                                                                    let uu____7322
                                                                    =
                                                                    FStar_Syntax_Print.uvar_to_string
                                                                    ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_head
                                                                     in
                                                                    let uu____7324
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    term  in
                                                                    FStar_Util.print2
                                                                    "apply_lemma: arg %s unified to (%s)\n"
                                                                    uu____7322
                                                                    uu____7324)
                                                                    (fun
                                                                    uu____7330
                                                                     ->
                                                                    let g_typ
                                                                    =
                                                                    let uu____7332
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    goal  in
                                                                    FStar_TypeChecker_TcTerm.check_type_of_well_typed_term'
                                                                    true
                                                                    uu____7332
                                                                    term
                                                                    ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_typ
                                                                     in
                                                                    let uu____7334
                                                                    =
                                                                    let uu____7337
                                                                    =
                                                                    if
                                                                    ps.FStar_Tactics_Types.tac_verb_dbg
                                                                    then
                                                                    let uu____7341
                                                                    =
                                                                    FStar_Syntax_Print.ctx_uvar_to_string
                                                                    ctx_uvar
                                                                     in
                                                                    let uu____7343
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    term  in
                                                                    FStar_Util.format2
                                                                    "apply_lemma solved arg %s to %s\n"
                                                                    uu____7341
                                                                    uu____7343
                                                                    else
                                                                    "apply_lemma solved arg"
                                                                     in
                                                                    let uu____7349
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    goal  in
                                                                    proc_guard
                                                                    uu____7337
                                                                    uu____7349
                                                                    g_typ  in
                                                                    bind
                                                                    uu____7334
                                                                    (fun
                                                                    uu____7353
                                                                     ->
                                                                    ret []))))))
                                                                   in
                                                                bind
                                                                  uu____7184
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
                                                                    let uu____7417
                                                                    = f x xs1
                                                                     in
                                                                    if
                                                                    uu____7417
                                                                    then
                                                                    let uu____7422
                                                                    =
                                                                    filter' f
                                                                    xs1  in x
                                                                    ::
                                                                    uu____7422
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
                                                                    let uu____7437
                                                                    =
                                                                    let uu____7439
                                                                    =
                                                                    FStar_Tactics_Types.goal_witness
                                                                    g  in
                                                                    checkone
                                                                    uu____7439
                                                                    goals  in
                                                                    Prims.op_Negation
                                                                    uu____7437)
                                                                    sub_goals1
                                                                     in
                                                                    let uu____7440
                                                                    =
                                                                    let uu____7443
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    goal  in
                                                                    proc_guard
                                                                    "apply_lemma guard"
                                                                    uu____7443
                                                                    guard  in
                                                                    bind
                                                                    uu____7440
                                                                    (fun
                                                                    uu____7447
                                                                     ->
                                                                    let uu____7448
                                                                    =
                                                                    let uu____7451
                                                                    =
                                                                    let uu____7453
                                                                    =
                                                                    let uu____7455
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    goal  in
                                                                    let uu____7456
                                                                    =
                                                                    FStar_Syntax_Util.mk_squash
                                                                    FStar_Syntax_Syntax.U_zero
                                                                    pre1  in
                                                                    istrivial
                                                                    uu____7455
                                                                    uu____7456
                                                                     in
                                                                    Prims.op_Negation
                                                                    uu____7453
                                                                     in
                                                                    if
                                                                    uu____7451
                                                                    then
                                                                    let uu____7460
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    goal  in
                                                                    add_irrelevant_goal
                                                                    "apply_lemma precondition"
                                                                    uu____7460
                                                                    pre1
                                                                    goal.FStar_Tactics_Types.opts
                                                                    goal.FStar_Tactics_Types.label
                                                                    else
                                                                    ret ()
                                                                     in
                                                                    bind
                                                                    uu____7448
                                                                    (fun
                                                                    uu____7465
                                                                     ->
                                                                    add_goals
                                                                    sub_goals2)))))))))))))
         in
      focus uu____6230  in
    FStar_All.pipe_left (wrap_err "apply_lemma") uu____6227
  
let (destruct_eq' :
  FStar_Reflection_Data.typ ->
    (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.option)
  =
  fun typ  ->
    let uu____7489 = FStar_Syntax_Util.destruct_typ_as_formula typ  in
    match uu____7489 with
    | FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn
        (l,uu____7499::(e1,FStar_Pervasives_Native.None )::(e2,FStar_Pervasives_Native.None
                                                            )::[]))
        when
        (FStar_Ident.lid_equals l FStar_Parser_Const.eq2_lid) ||
          (FStar_Ident.lid_equals l FStar_Parser_Const.c_eq2_lid)
        -> FStar_Pervasives_Native.Some (e1, e2)
    | FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn
        (l,uu____7559::uu____7560::(e1,uu____7562)::(e2,uu____7564)::[]))
        when FStar_Ident.lid_equals l FStar_Parser_Const.eq3_lid ->
        FStar_Pervasives_Native.Some (e1, e2)
    | uu____7641 ->
        let uu____7644 = FStar_Syntax_Util.unb2t typ  in
        (match uu____7644 with
         | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
         | FStar_Pervasives_Native.Some t ->
             let uu____7658 = FStar_Syntax_Util.head_and_args t  in
             (match uu____7658 with
              | (hd1,args) ->
                  let uu____7707 =
                    let uu____7722 =
                      let uu____7723 = FStar_Syntax_Subst.compress hd1  in
                      uu____7723.FStar_Syntax_Syntax.n  in
                    (uu____7722, args)  in
                  (match uu____7707 with
                   | (FStar_Syntax_Syntax.Tm_fvar
                      fv,(uu____7743,FStar_Pervasives_Native.Some
                          (FStar_Syntax_Syntax.Implicit uu____7744))::
                      (e1,FStar_Pervasives_Native.None )::(e2,FStar_Pervasives_Native.None
                                                           )::[])
                       when
                       FStar_Syntax_Syntax.fv_eq_lid fv
                         FStar_Parser_Const.op_Eq
                       -> FStar_Pervasives_Native.Some (e1, e2)
                   | uu____7812 -> FStar_Pervasives_Native.None)))
  
let (destruct_eq :
  FStar_Reflection_Data.typ ->
    (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.option)
  =
  fun typ  ->
    let uu____7849 = destruct_eq' typ  in
    match uu____7849 with
    | FStar_Pervasives_Native.Some t -> FStar_Pervasives_Native.Some t
    | FStar_Pervasives_Native.None  ->
        let uu____7879 = FStar_Syntax_Util.un_squash typ  in
        (match uu____7879 with
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
        let uu____7948 = FStar_TypeChecker_Env.pop_bv e1  in
        match uu____7948 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (bv',e') ->
            if FStar_Syntax_Syntax.bv_eq bvar bv'
            then FStar_Pervasives_Native.Some (e', bv', [])
            else
              (let uu____8006 = aux e'  in
               FStar_Util.map_opt uu____8006
                 (fun uu____8037  ->
                    match uu____8037 with
                    | (e'',bv,bvs) -> (e'', bv, (bv' :: bvs))))
         in
      let uu____8063 = aux e  in
      FStar_Util.map_opt uu____8063
        (fun uu____8094  ->
           match uu____8094 with
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
          FStar_Tactics_Types.goal FStar_Pervasives_Native.option tac)
  =
  fun b1  ->
    fun b2  ->
      fun s  ->
        fun g  ->
          let uu____8172 =
            let uu____8183 = FStar_Tactics_Types.goal_env g  in
            split_env b1 uu____8183  in
          match uu____8172 with
          | FStar_Pervasives_Native.Some (e0,b11,bvs) ->
              let s1 bv =
                let uu___1129_8209 = bv  in
                let uu____8210 =
                  FStar_Syntax_Subst.subst s bv.FStar_Syntax_Syntax.sort  in
                {
                  FStar_Syntax_Syntax.ppname =
                    (uu___1129_8209.FStar_Syntax_Syntax.ppname);
                  FStar_Syntax_Syntax.index =
                    (uu___1129_8209.FStar_Syntax_Syntax.index);
                  FStar_Syntax_Syntax.sort = uu____8210
                }  in
              let bvs' = FStar_List.map s1 bvs  in
              let new_env = push_bvs e0 (b2 :: bvs')  in
              let new_goal_ty =
                let uu____8218 = FStar_Tactics_Types.goal_type g  in
                FStar_Syntax_Subst.subst s uu____8218  in
              let uu____8219 = __tc_lax new_env new_goal_ty  in
              bind uu____8219
                (fun uu____8241  ->
                   match uu____8241 with
                   | (new_goal_ty1,uu____8253,uu____8254) ->
                       let uu____8255 =
                         new_uvar "subst_goal" new_env new_goal_ty1  in
                       bind uu____8255
                         (fun uu____8275  ->
                            match uu____8275 with
                            | (uvt,uv) ->
                                let goal' =
                                  FStar_Tactics_Types.mk_goal new_env uv
                                    g.FStar_Tactics_Types.opts
                                    g.FStar_Tactics_Types.is_guard
                                    g.FStar_Tactics_Types.label
                                   in
                                let sol =
                                  let uu____8290 =
                                    let uu____8293 =
                                      FStar_List.map
                                        FStar_Syntax_Syntax.mk_binder (b2 ::
                                        bvs')
                                       in
                                    FStar_Syntax_Util.abs uu____8293 uvt
                                      FStar_Pervasives_Native.None
                                     in
                                  let uu____8300 =
                                    FStar_List.map
                                      (fun bv  ->
                                         let uu____8314 =
                                           FStar_Syntax_Syntax.bv_to_name bv
                                            in
                                         FStar_Syntax_Syntax.as_arg
                                           uu____8314) (b11 :: bvs)
                                     in
                                  FStar_Syntax_Util.mk_app uu____8290
                                    uu____8300
                                   in
                                let uu____8315 =
                                  let uu____8324 =
                                    FStar_Tactics_Types.goal_env g  in
                                  __tc_lax uu____8324 sol  in
                                bind uu____8315
                                  (fun uu____8338  ->
                                     match uu____8338 with
                                     | (sol1,uu____8350,uu____8351) ->
                                         let uu____8352 = set_solution g sol1
                                            in
                                         bind uu____8352
                                           (fun uu____8358  ->
                                              ret
                                                (FStar_Pervasives_Native.Some
                                                   goal')))))
          | FStar_Pervasives_Native.None  -> ret FStar_Pervasives_Native.None
  
let (rewrite : FStar_Syntax_Syntax.binder -> unit tac) =
  fun h  ->
    let uu____8381 =
      let uu____8384 = cur_goal ()  in
      bind uu____8384
        (fun goal  ->
           let uu____8392 = h  in
           match uu____8392 with
           | (bv,uu____8396) ->
               mlog
                 (fun uu____8404  ->
                    let uu____8405 = FStar_Syntax_Print.bv_to_string bv  in
                    let uu____8407 =
                      FStar_Syntax_Print.term_to_string
                        bv.FStar_Syntax_Syntax.sort
                       in
                    FStar_Util.print2 "+++Rewrite %s : %s\n" uu____8405
                      uu____8407)
                 (fun uu____8412  ->
                    let uu____8413 =
                      let uu____8424 = FStar_Tactics_Types.goal_env goal  in
                      split_env bv uu____8424  in
                    match uu____8413 with
                    | FStar_Pervasives_Native.None  ->
                        fail "binder not found in environment"
                    | FStar_Pervasives_Native.Some (e0,bv1,bvs) ->
                        let uu____8451 =
                          destruct_eq bv1.FStar_Syntax_Syntax.sort  in
                        (match uu____8451 with
                         | FStar_Pervasives_Native.Some (x,e) ->
                             let uu____8466 =
                               let uu____8467 = FStar_Syntax_Subst.compress x
                                  in
                               uu____8467.FStar_Syntax_Syntax.n  in
                             (match uu____8466 with
                              | FStar_Syntax_Syntax.Tm_name x1 ->
                                  let s = [FStar_Syntax_Syntax.NT (x1, e)]
                                     in
                                  let s1 bv2 =
                                    let uu___1171_8484 = bv2  in
                                    let uu____8485 =
                                      FStar_Syntax_Subst.subst s
                                        bv2.FStar_Syntax_Syntax.sort
                                       in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___1171_8484.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___1171_8484.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = uu____8485
                                    }  in
                                  let bvs' = FStar_List.map s1 bvs  in
                                  let new_env = push_bvs e0 (bv1 :: bvs')  in
                                  let new_goal_ty =
                                    let uu____8493 =
                                      FStar_Tactics_Types.goal_type goal  in
                                    FStar_Syntax_Subst.subst s uu____8493  in
                                  let uu____8494 =
                                    __tc_lax new_env new_goal_ty  in
                                  bind uu____8494
                                    (fun uu____8514  ->
                                       match uu____8514 with
                                       | (new_goal_ty1,uu____8524,uu____8525)
                                           ->
                                           let uu____8526 =
                                             new_uvar "rewrite" new_env
                                               new_goal_ty1
                                              in
                                           bind uu____8526
                                             (fun uu____8544  ->
                                                match uu____8544 with
                                                | (uvt,uv) ->
                                                    let goal' =
                                                      FStar_Tactics_Types.mk_goal
                                                        new_env uv
                                                        goal.FStar_Tactics_Types.opts
                                                        goal.FStar_Tactics_Types.is_guard
                                                        goal.FStar_Tactics_Types.label
                                                       in
                                                    let sol =
                                                      let uu____8557 =
                                                        let uu____8560 =
                                                          FStar_List.map
                                                            FStar_Syntax_Syntax.mk_binder
                                                            bvs'
                                                           in
                                                        FStar_Syntax_Util.abs
                                                          uu____8560 uvt
                                                          FStar_Pervasives_Native.None
                                                         in
                                                      let uu____8567 =
                                                        FStar_List.map
                                                          (fun bv2  ->
                                                             let uu____8581 =
                                                               FStar_Syntax_Syntax.bv_to_name
                                                                 bv2
                                                                in
                                                             FStar_Syntax_Syntax.as_arg
                                                               uu____8581)
                                                          bvs
                                                         in
                                                      FStar_Syntax_Util.mk_app
                                                        uu____8557 uu____8567
                                                       in
                                                    let uu____8582 =
                                                      let uu____8591 =
                                                        FStar_Tactics_Types.goal_env
                                                          goal
                                                         in
                                                      __tc_lax uu____8591 sol
                                                       in
                                                    bind uu____8582
                                                      (fun uu____8603  ->
                                                         match uu____8603
                                                         with
                                                         | (sol1,uu____8613,uu____8614)
                                                             ->
                                                             let uu____8615 =
                                                               set_solution
                                                                 goal sol1
                                                                in
                                                             bind uu____8615
                                                               (fun
                                                                  uu____8619 
                                                                  ->
                                                                  replace_cur
                                                                    goal'))))
                              | uu____8620 ->
                                  fail
                                    "Not an equality hypothesis with a variable on the LHS")
                         | uu____8622 -> fail "Not an equality hypothesis")))
       in
    FStar_All.pipe_left (wrap_err "rewrite") uu____8381
  
let (rename_to :
  FStar_Syntax_Syntax.binder ->
    Prims.string -> FStar_Syntax_Syntax.binder tac)
  =
  fun b  ->
    fun s  ->
      let uu____8652 =
        let uu____8661 = cur_goal ()  in
        bind uu____8661
          (fun goal  ->
             let uu____8678 = b  in
             match uu____8678 with
             | (bv,q) ->
                 let bv' =
                   let uu____8694 =
                     let uu___1200_8695 = bv  in
                     let uu____8696 =
                       FStar_Ident.mk_ident
                         (s,
                           ((bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange))
                        in
                     {
                       FStar_Syntax_Syntax.ppname = uu____8696;
                       FStar_Syntax_Syntax.index =
                         (uu___1200_8695.FStar_Syntax_Syntax.index);
                       FStar_Syntax_Syntax.sort =
                         (uu___1200_8695.FStar_Syntax_Syntax.sort)
                     }  in
                   FStar_Syntax_Syntax.freshen_bv uu____8694  in
                 let s1 =
                   let uu____8701 =
                     let uu____8702 =
                       let uu____8709 = FStar_Syntax_Syntax.bv_to_name bv'
                          in
                       (bv, uu____8709)  in
                     FStar_Syntax_Syntax.NT uu____8702  in
                   [uu____8701]  in
                 let uu____8714 = subst_goal bv bv' s1 goal  in
                 bind uu____8714
                   (fun uu___4_8728  ->
                      match uu___4_8728 with
                      | FStar_Pervasives_Native.None  ->
                          fail "binder not found in environment"
                      | FStar_Pervasives_Native.Some goal1 ->
                          let uu____8747 = replace_cur goal1  in
                          bind uu____8747 (fun uu____8757  -> ret (bv', q))))
         in
      FStar_All.pipe_left (wrap_err "rename_to") uu____8652
  
let (binder_retype : FStar_Syntax_Syntax.binder -> unit tac) =
  fun b  ->
    let uu____8793 =
      let uu____8796 = cur_goal ()  in
      bind uu____8796
        (fun goal  ->
           let uu____8805 = b  in
           match uu____8805 with
           | (bv,uu____8809) ->
               let uu____8814 =
                 let uu____8825 = FStar_Tactics_Types.goal_env goal  in
                 split_env bv uu____8825  in
               (match uu____8814 with
                | FStar_Pervasives_Native.None  ->
                    fail "binder is not present in environment"
                | FStar_Pervasives_Native.Some (e0,bv1,bvs) ->
                    let uu____8852 = FStar_Syntax_Util.type_u ()  in
                    (match uu____8852 with
                     | (ty,u) ->
                         let uu____8861 = new_uvar "binder_retype" e0 ty  in
                         bind uu____8861
                           (fun uu____8880  ->
                              match uu____8880 with
                              | (t',u_t') ->
                                  let bv'' =
                                    let uu___1226_8890 = bv1  in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___1226_8890.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___1226_8890.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = t'
                                    }  in
                                  let s =
                                    let uu____8894 =
                                      let uu____8895 =
                                        let uu____8902 =
                                          FStar_Syntax_Syntax.bv_to_name bv''
                                           in
                                        (bv1, uu____8902)  in
                                      FStar_Syntax_Syntax.NT uu____8895  in
                                    [uu____8894]  in
                                  let bvs1 =
                                    FStar_List.map
                                      (fun b1  ->
                                         let uu___1231_8914 = b1  in
                                         let uu____8915 =
                                           FStar_Syntax_Subst.subst s
                                             b1.FStar_Syntax_Syntax.sort
                                            in
                                         {
                                           FStar_Syntax_Syntax.ppname =
                                             (uu___1231_8914.FStar_Syntax_Syntax.ppname);
                                           FStar_Syntax_Syntax.index =
                                             (uu___1231_8914.FStar_Syntax_Syntax.index);
                                           FStar_Syntax_Syntax.sort =
                                             uu____8915
                                         }) bvs
                                     in
                                  let env' = push_bvs e0 (bv'' :: bvs1)  in
                                  bind __dismiss
                                    (fun uu____8922  ->
                                       let new_goal =
                                         let uu____8924 =
                                           FStar_Tactics_Types.goal_with_env
                                             goal env'
                                            in
                                         let uu____8925 =
                                           let uu____8926 =
                                             FStar_Tactics_Types.goal_type
                                               goal
                                              in
                                           FStar_Syntax_Subst.subst s
                                             uu____8926
                                            in
                                         FStar_Tactics_Types.goal_with_type
                                           uu____8924 uu____8925
                                          in
                                       let uu____8927 = add_goals [new_goal]
                                          in
                                       bind uu____8927
                                         (fun uu____8932  ->
                                            let uu____8933 =
                                              FStar_Syntax_Util.mk_eq2
                                                (FStar_Syntax_Syntax.U_succ u)
                                                ty
                                                bv1.FStar_Syntax_Syntax.sort
                                                t'
                                               in
                                            add_irrelevant_goal
                                              "binder_retype equation" e0
                                              uu____8933
                                              goal.FStar_Tactics_Types.opts
                                              goal.FStar_Tactics_Types.label))))))
       in
    FStar_All.pipe_left (wrap_err "binder_retype") uu____8793
  
let (norm_binder_type :
  FStar_Syntax_Embeddings.norm_step Prims.list ->
    FStar_Syntax_Syntax.binder -> unit tac)
  =
  fun s  ->
    fun b  ->
      let uu____8959 =
        let uu____8962 = cur_goal ()  in
        bind uu____8962
          (fun goal  ->
             let uu____8971 = b  in
             match uu____8971 with
             | (bv,uu____8975) ->
                 let uu____8980 =
                   let uu____8991 = FStar_Tactics_Types.goal_env goal  in
                   split_env bv uu____8991  in
                 (match uu____8980 with
                  | FStar_Pervasives_Native.None  ->
                      fail "binder is not present in environment"
                  | FStar_Pervasives_Native.Some (e0,bv1,bvs) ->
                      let steps =
                        let uu____9021 =
                          FStar_TypeChecker_Normalize.tr_norm_steps s  in
                        FStar_List.append
                          [FStar_TypeChecker_Env.Reify;
                          FStar_TypeChecker_Env.UnfoldTac] uu____9021
                         in
                      let sort' =
                        normalize steps e0 bv1.FStar_Syntax_Syntax.sort  in
                      let bv' =
                        let uu___1252_9026 = bv1  in
                        {
                          FStar_Syntax_Syntax.ppname =
                            (uu___1252_9026.FStar_Syntax_Syntax.ppname);
                          FStar_Syntax_Syntax.index =
                            (uu___1252_9026.FStar_Syntax_Syntax.index);
                          FStar_Syntax_Syntax.sort = sort'
                        }  in
                      let env' = push_bvs e0 (bv' :: bvs)  in
                      let uu____9028 =
                        FStar_Tactics_Types.goal_with_env goal env'  in
                      replace_cur uu____9028))
         in
      FStar_All.pipe_left (wrap_err "norm_binder_type") uu____8959
  
let (revert : unit -> unit tac) =
  fun uu____9041  ->
    let uu____9044 = cur_goal ()  in
    bind uu____9044
      (fun goal  ->
         let uu____9050 =
           let uu____9057 = FStar_Tactics_Types.goal_env goal  in
           FStar_TypeChecker_Env.pop_bv uu____9057  in
         match uu____9050 with
         | FStar_Pervasives_Native.None  ->
             fail "Cannot revert; empty context"
         | FStar_Pervasives_Native.Some (x,env') ->
             let typ' =
               let uu____9074 =
                 let uu____9077 = FStar_Tactics_Types.goal_type goal  in
                 FStar_Syntax_Syntax.mk_Total uu____9077  in
               FStar_Syntax_Util.arrow [(x, FStar_Pervasives_Native.None)]
                 uu____9074
                in
             let uu____9092 = new_uvar "revert" env' typ'  in
             bind uu____9092
               (fun uu____9108  ->
                  match uu____9108 with
                  | (r,u_r) ->
                      let uu____9117 =
                        let uu____9120 =
                          let uu____9121 =
                            let uu____9122 =
                              FStar_Tactics_Types.goal_type goal  in
                            uu____9122.FStar_Syntax_Syntax.pos  in
                          let uu____9125 =
                            let uu____9130 =
                              let uu____9131 =
                                let uu____9140 =
                                  FStar_Syntax_Syntax.bv_to_name x  in
                                FStar_Syntax_Syntax.as_arg uu____9140  in
                              [uu____9131]  in
                            FStar_Syntax_Syntax.mk_Tm_app r uu____9130  in
                          uu____9125 FStar_Pervasives_Native.None uu____9121
                           in
                        set_solution goal uu____9120  in
                      bind uu____9117
                        (fun uu____9159  ->
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
      let uu____9173 = FStar_Syntax_Free.names t  in
      FStar_Util.set_mem bv uu____9173
  
let (clear : FStar_Syntax_Syntax.binder -> unit tac) =
  fun b  ->
    let bv = FStar_Pervasives_Native.fst b  in
    let uu____9189 = cur_goal ()  in
    bind uu____9189
      (fun goal  ->
         mlog
           (fun uu____9197  ->
              let uu____9198 = FStar_Syntax_Print.binder_to_string b  in
              let uu____9200 =
                let uu____9202 =
                  let uu____9204 =
                    let uu____9213 = FStar_Tactics_Types.goal_env goal  in
                    FStar_TypeChecker_Env.all_binders uu____9213  in
                  FStar_All.pipe_right uu____9204 FStar_List.length  in
                FStar_All.pipe_right uu____9202 FStar_Util.string_of_int  in
              FStar_Util.print2 "Clear of (%s), env has %s binders\n"
                uu____9198 uu____9200)
           (fun uu____9234  ->
              let uu____9235 =
                let uu____9246 = FStar_Tactics_Types.goal_env goal  in
                split_env bv uu____9246  in
              match uu____9235 with
              | FStar_Pervasives_Native.None  ->
                  fail "Cannot clear; binder not in environment"
              | FStar_Pervasives_Native.Some (e',bv1,bvs) ->
                  let rec check1 bvs1 =
                    match bvs1 with
                    | [] -> ret ()
                    | bv'::bvs2 ->
                        let uu____9291 =
                          free_in bv1 bv'.FStar_Syntax_Syntax.sort  in
                        if uu____9291
                        then
                          let uu____9296 =
                            let uu____9298 =
                              FStar_Syntax_Print.bv_to_string bv'  in
                            FStar_Util.format1
                              "Cannot clear; binder present in the type of %s"
                              uu____9298
                             in
                          fail uu____9296
                        else check1 bvs2
                     in
                  let uu____9303 =
                    let uu____9305 = FStar_Tactics_Types.goal_type goal  in
                    free_in bv1 uu____9305  in
                  if uu____9303
                  then fail "Cannot clear; binder present in goal"
                  else
                    (let uu____9312 = check1 bvs  in
                     bind uu____9312
                       (fun uu____9318  ->
                          let env' = push_bvs e' bvs  in
                          let uu____9320 =
                            let uu____9327 =
                              FStar_Tactics_Types.goal_type goal  in
                            new_uvar "clear.witness" env' uu____9327  in
                          bind uu____9320
                            (fun uu____9337  ->
                               match uu____9337 with
                               | (ut,uvar_ut) ->
                                   let uu____9346 = set_solution goal ut  in
                                   bind uu____9346
                                     (fun uu____9351  ->
                                        let uu____9352 =
                                          FStar_Tactics_Types.mk_goal env'
                                            uvar_ut
                                            goal.FStar_Tactics_Types.opts
                                            goal.FStar_Tactics_Types.is_guard
                                            goal.FStar_Tactics_Types.label
                                           in
                                        replace_cur uu____9352))))))
  
let (clear_top : unit -> unit tac) =
  fun uu____9360  ->
    let uu____9363 = cur_goal ()  in
    bind uu____9363
      (fun goal  ->
         let uu____9369 =
           let uu____9376 = FStar_Tactics_Types.goal_env goal  in
           FStar_TypeChecker_Env.pop_bv uu____9376  in
         match uu____9369 with
         | FStar_Pervasives_Native.None  ->
             fail "Cannot clear; empty context"
         | FStar_Pervasives_Native.Some (x,uu____9385) ->
             let uu____9390 = FStar_Syntax_Syntax.mk_binder x  in
             clear uu____9390)
  
let (prune : Prims.string -> unit tac) =
  fun s  ->
    let uu____9403 = cur_goal ()  in
    bind uu____9403
      (fun g  ->
         let ctx = FStar_Tactics_Types.goal_env g  in
         let ctx' =
           let uu____9413 = FStar_Ident.path_of_text s  in
           FStar_TypeChecker_Env.rem_proof_ns ctx uu____9413  in
         let g' = FStar_Tactics_Types.goal_with_env g ctx'  in replace_cur g')
  
let (addns : Prims.string -> unit tac) =
  fun s  ->
    let uu____9427 = cur_goal ()  in
    bind uu____9427
      (fun g  ->
         let ctx = FStar_Tactics_Types.goal_env g  in
         let ctx' =
           let uu____9437 = FStar_Ident.path_of_text s  in
           FStar_TypeChecker_Env.add_proof_ns ctx uu____9437  in
         let g' = FStar_Tactics_Types.goal_with_env g ctx'  in replace_cur g')
  
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
            let uu____9479 = FStar_Syntax_Subst.compress t  in
            uu____9479.FStar_Syntax_Syntax.n  in
          let uu____9482 =
            if d = FStar_Tactics_Types.TopDown
            then
              f env
                (let uu___1434_9489 = t  in
                 {
                   FStar_Syntax_Syntax.n = tn;
                   FStar_Syntax_Syntax.pos =
                     (uu___1434_9489.FStar_Syntax_Syntax.pos);
                   FStar_Syntax_Syntax.vars =
                     (uu___1434_9489.FStar_Syntax_Syntax.vars)
                 })
            else ret t  in
          bind uu____9482
            (fun t1  ->
               let ff = tac_fold_env d f env  in
               let tn1 =
                 let uu____9506 =
                   let uu____9507 = FStar_Syntax_Subst.compress t1  in
                   uu____9507.FStar_Syntax_Syntax.n  in
                 match uu____9506 with
                 | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
                     let uu____9538 = ff hd1  in
                     bind uu____9538
                       (fun hd2  ->
                          let fa uu____9564 =
                            match uu____9564 with
                            | (a,q) ->
                                let uu____9585 = ff a  in
                                bind uu____9585 (fun a1  -> ret (a1, q))
                             in
                          let uu____9604 = mapM fa args  in
                          bind uu____9604
                            (fun args1  ->
                               ret (FStar_Syntax_Syntax.Tm_app (hd2, args1))))
                 | FStar_Syntax_Syntax.Tm_abs (bs,t2,k) ->
                     let uu____9686 = FStar_Syntax_Subst.open_term bs t2  in
                     (match uu____9686 with
                      | (bs1,t') ->
                          let uu____9695 =
                            let uu____9698 =
                              FStar_TypeChecker_Env.push_binders env bs1  in
                            tac_fold_env d f uu____9698 t'  in
                          bind uu____9695
                            (fun t''  ->
                               let uu____9702 =
                                 let uu____9703 =
                                   let uu____9722 =
                                     FStar_Syntax_Subst.close_binders bs1  in
                                   let uu____9731 =
                                     FStar_Syntax_Subst.close bs1 t''  in
                                   (uu____9722, uu____9731, k)  in
                                 FStar_Syntax_Syntax.Tm_abs uu____9703  in
                               ret uu____9702))
                 | FStar_Syntax_Syntax.Tm_arrow (bs,k) -> ret tn
                 | FStar_Syntax_Syntax.Tm_match (hd1,brs) ->
                     let uu____9806 = ff hd1  in
                     bind uu____9806
                       (fun hd2  ->
                          let ffb br =
                            let uu____9821 =
                              FStar_Syntax_Subst.open_branch br  in
                            match uu____9821 with
                            | (pat,w,e) ->
                                let bvs = FStar_Syntax_Syntax.pat_bvs pat  in
                                let ff1 =
                                  let uu____9853 =
                                    FStar_TypeChecker_Env.push_bvs env bvs
                                     in
                                  tac_fold_env d f uu____9853  in
                                let uu____9854 = ff1 e  in
                                bind uu____9854
                                  (fun e1  ->
                                     let br1 =
                                       FStar_Syntax_Subst.close_branch
                                         (pat, w, e1)
                                        in
                                     ret br1)
                             in
                          let uu____9869 = mapM ffb brs  in
                          bind uu____9869
                            (fun brs1  ->
                               ret (FStar_Syntax_Syntax.Tm_match (hd2, brs1))))
                 | FStar_Syntax_Syntax.Tm_let
                     ((false
                       ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inl bv;
                          FStar_Syntax_Syntax.lbunivs = uu____9913;
                          FStar_Syntax_Syntax.lbtyp = uu____9914;
                          FStar_Syntax_Syntax.lbeff = uu____9915;
                          FStar_Syntax_Syntax.lbdef = def;
                          FStar_Syntax_Syntax.lbattrs = uu____9917;
                          FStar_Syntax_Syntax.lbpos = uu____9918;_}::[]),e)
                     ->
                     let lb =
                       let uu____9946 =
                         let uu____9947 = FStar_Syntax_Subst.compress t1  in
                         uu____9947.FStar_Syntax_Syntax.n  in
                       match uu____9946 with
                       | FStar_Syntax_Syntax.Tm_let
                           ((false ,lb::[]),uu____9951) -> lb
                       | uu____9967 -> failwith "impossible"  in
                     let fflb lb1 =
                       let uu____9977 = ff lb1.FStar_Syntax_Syntax.lbdef  in
                       bind uu____9977
                         (fun def1  ->
                            ret
                              (let uu___1387_9983 = lb1  in
                               {
                                 FStar_Syntax_Syntax.lbname =
                                   (uu___1387_9983.FStar_Syntax_Syntax.lbname);
                                 FStar_Syntax_Syntax.lbunivs =
                                   (uu___1387_9983.FStar_Syntax_Syntax.lbunivs);
                                 FStar_Syntax_Syntax.lbtyp =
                                   (uu___1387_9983.FStar_Syntax_Syntax.lbtyp);
                                 FStar_Syntax_Syntax.lbeff =
                                   (uu___1387_9983.FStar_Syntax_Syntax.lbeff);
                                 FStar_Syntax_Syntax.lbdef = def1;
                                 FStar_Syntax_Syntax.lbattrs =
                                   (uu___1387_9983.FStar_Syntax_Syntax.lbattrs);
                                 FStar_Syntax_Syntax.lbpos =
                                   (uu___1387_9983.FStar_Syntax_Syntax.lbpos)
                               }))
                        in
                     let uu____9984 = fflb lb  in
                     bind uu____9984
                       (fun lb1  ->
                          let uu____9994 =
                            let uu____9999 =
                              let uu____10000 =
                                FStar_Syntax_Syntax.mk_binder bv  in
                              [uu____10000]  in
                            FStar_Syntax_Subst.open_term uu____9999 e  in
                          match uu____9994 with
                          | (bs,e1) ->
                              let ff1 =
                                let uu____10030 =
                                  FStar_TypeChecker_Env.push_binders env bs
                                   in
                                tac_fold_env d f uu____10030  in
                              let uu____10031 = ff1 e1  in
                              bind uu____10031
                                (fun e2  ->
                                   let e3 = FStar_Syntax_Subst.close bs e2
                                      in
                                   ret
                                     (FStar_Syntax_Syntax.Tm_let
                                        ((false, [lb1]), e3))))
                 | FStar_Syntax_Syntax.Tm_let ((true ,lbs),e) ->
                     let fflb lb =
                       let uu____10078 = ff lb.FStar_Syntax_Syntax.lbdef  in
                       bind uu____10078
                         (fun def  ->
                            ret
                              (let uu___1405_10084 = lb  in
                               {
                                 FStar_Syntax_Syntax.lbname =
                                   (uu___1405_10084.FStar_Syntax_Syntax.lbname);
                                 FStar_Syntax_Syntax.lbunivs =
                                   (uu___1405_10084.FStar_Syntax_Syntax.lbunivs);
                                 FStar_Syntax_Syntax.lbtyp =
                                   (uu___1405_10084.FStar_Syntax_Syntax.lbtyp);
                                 FStar_Syntax_Syntax.lbeff =
                                   (uu___1405_10084.FStar_Syntax_Syntax.lbeff);
                                 FStar_Syntax_Syntax.lbdef = def;
                                 FStar_Syntax_Syntax.lbattrs =
                                   (uu___1405_10084.FStar_Syntax_Syntax.lbattrs);
                                 FStar_Syntax_Syntax.lbpos =
                                   (uu___1405_10084.FStar_Syntax_Syntax.lbpos)
                               }))
                        in
                     let uu____10085 = FStar_Syntax_Subst.open_let_rec lbs e
                        in
                     (match uu____10085 with
                      | (lbs1,e1) ->
                          let uu____10100 = mapM fflb lbs1  in
                          bind uu____10100
                            (fun lbs2  ->
                               let uu____10112 = ff e1  in
                               bind uu____10112
                                 (fun e2  ->
                                    let uu____10120 =
                                      FStar_Syntax_Subst.close_let_rec lbs2
                                        e2
                                       in
                                    match uu____10120 with
                                    | (lbs3,e3) ->
                                        ret
                                          (FStar_Syntax_Syntax.Tm_let
                                             ((true, lbs3), e3)))))
                 | FStar_Syntax_Syntax.Tm_ascribed (t2,asc,eff) ->
                     let uu____10191 = ff t2  in
                     bind uu____10191
                       (fun t3  ->
                          ret
                            (FStar_Syntax_Syntax.Tm_ascribed (t3, asc, eff)))
                 | FStar_Syntax_Syntax.Tm_meta (t2,m) ->
                     let uu____10222 = ff t2  in
                     bind uu____10222
                       (fun t3  -> ret (FStar_Syntax_Syntax.Tm_meta (t3, m)))
                 | uu____10229 -> ret tn  in
               bind tn1
                 (fun tn2  ->
                    let t' =
                      let uu___1429_10236 = t1  in
                      {
                        FStar_Syntax_Syntax.n = tn2;
                        FStar_Syntax_Syntax.pos =
                          (uu___1429_10236.FStar_Syntax_Syntax.pos);
                        FStar_Syntax_Syntax.vars =
                          (uu___1429_10236.FStar_Syntax_Syntax.vars)
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
              let uu____10283 =
                FStar_TypeChecker_TcTerm.tc_term
                  (let uu___1442_10292 = env  in
                   {
                     FStar_TypeChecker_Env.solver =
                       (uu___1442_10292.FStar_TypeChecker_Env.solver);
                     FStar_TypeChecker_Env.range =
                       (uu___1442_10292.FStar_TypeChecker_Env.range);
                     FStar_TypeChecker_Env.curmodule =
                       (uu___1442_10292.FStar_TypeChecker_Env.curmodule);
                     FStar_TypeChecker_Env.gamma =
                       (uu___1442_10292.FStar_TypeChecker_Env.gamma);
                     FStar_TypeChecker_Env.gamma_sig =
                       (uu___1442_10292.FStar_TypeChecker_Env.gamma_sig);
                     FStar_TypeChecker_Env.gamma_cache =
                       (uu___1442_10292.FStar_TypeChecker_Env.gamma_cache);
                     FStar_TypeChecker_Env.modules =
                       (uu___1442_10292.FStar_TypeChecker_Env.modules);
                     FStar_TypeChecker_Env.expected_typ =
                       (uu___1442_10292.FStar_TypeChecker_Env.expected_typ);
                     FStar_TypeChecker_Env.sigtab =
                       (uu___1442_10292.FStar_TypeChecker_Env.sigtab);
                     FStar_TypeChecker_Env.attrtab =
                       (uu___1442_10292.FStar_TypeChecker_Env.attrtab);
                     FStar_TypeChecker_Env.instantiate_imp =
                       (uu___1442_10292.FStar_TypeChecker_Env.instantiate_imp);
                     FStar_TypeChecker_Env.effects =
                       (uu___1442_10292.FStar_TypeChecker_Env.effects);
                     FStar_TypeChecker_Env.generalize =
                       (uu___1442_10292.FStar_TypeChecker_Env.generalize);
                     FStar_TypeChecker_Env.letrecs =
                       (uu___1442_10292.FStar_TypeChecker_Env.letrecs);
                     FStar_TypeChecker_Env.top_level =
                       (uu___1442_10292.FStar_TypeChecker_Env.top_level);
                     FStar_TypeChecker_Env.check_uvars =
                       (uu___1442_10292.FStar_TypeChecker_Env.check_uvars);
                     FStar_TypeChecker_Env.use_eq =
                       (uu___1442_10292.FStar_TypeChecker_Env.use_eq);
                     FStar_TypeChecker_Env.use_eq_strict =
                       (uu___1442_10292.FStar_TypeChecker_Env.use_eq_strict);
                     FStar_TypeChecker_Env.is_iface =
                       (uu___1442_10292.FStar_TypeChecker_Env.is_iface);
                     FStar_TypeChecker_Env.admit =
                       (uu___1442_10292.FStar_TypeChecker_Env.admit);
                     FStar_TypeChecker_Env.lax = true;
                     FStar_TypeChecker_Env.lax_universes =
                       (uu___1442_10292.FStar_TypeChecker_Env.lax_universes);
                     FStar_TypeChecker_Env.phase1 =
                       (uu___1442_10292.FStar_TypeChecker_Env.phase1);
                     FStar_TypeChecker_Env.failhard =
                       (uu___1442_10292.FStar_TypeChecker_Env.failhard);
                     FStar_TypeChecker_Env.nosynth =
                       (uu___1442_10292.FStar_TypeChecker_Env.nosynth);
                     FStar_TypeChecker_Env.uvar_subtyping =
                       (uu___1442_10292.FStar_TypeChecker_Env.uvar_subtyping);
                     FStar_TypeChecker_Env.tc_term =
                       (uu___1442_10292.FStar_TypeChecker_Env.tc_term);
                     FStar_TypeChecker_Env.type_of =
                       (uu___1442_10292.FStar_TypeChecker_Env.type_of);
                     FStar_TypeChecker_Env.universe_of =
                       (uu___1442_10292.FStar_TypeChecker_Env.universe_of);
                     FStar_TypeChecker_Env.check_type_of =
                       (uu___1442_10292.FStar_TypeChecker_Env.check_type_of);
                     FStar_TypeChecker_Env.use_bv_sorts =
                       (uu___1442_10292.FStar_TypeChecker_Env.use_bv_sorts);
                     FStar_TypeChecker_Env.qtbl_name_and_index =
                       (uu___1442_10292.FStar_TypeChecker_Env.qtbl_name_and_index);
                     FStar_TypeChecker_Env.normalized_eff_names =
                       (uu___1442_10292.FStar_TypeChecker_Env.normalized_eff_names);
                     FStar_TypeChecker_Env.fv_delta_depths =
                       (uu___1442_10292.FStar_TypeChecker_Env.fv_delta_depths);
                     FStar_TypeChecker_Env.proof_ns =
                       (uu___1442_10292.FStar_TypeChecker_Env.proof_ns);
                     FStar_TypeChecker_Env.synth_hook =
                       (uu___1442_10292.FStar_TypeChecker_Env.synth_hook);
                     FStar_TypeChecker_Env.try_solve_implicits_hook =
                       (uu___1442_10292.FStar_TypeChecker_Env.try_solve_implicits_hook);
                     FStar_TypeChecker_Env.splice =
                       (uu___1442_10292.FStar_TypeChecker_Env.splice);
                     FStar_TypeChecker_Env.mpreprocess =
                       (uu___1442_10292.FStar_TypeChecker_Env.mpreprocess);
                     FStar_TypeChecker_Env.postprocess =
                       (uu___1442_10292.FStar_TypeChecker_Env.postprocess);
                     FStar_TypeChecker_Env.is_native_tactic =
                       (uu___1442_10292.FStar_TypeChecker_Env.is_native_tactic);
                     FStar_TypeChecker_Env.identifier_info =
                       (uu___1442_10292.FStar_TypeChecker_Env.identifier_info);
                     FStar_TypeChecker_Env.tc_hooks =
                       (uu___1442_10292.FStar_TypeChecker_Env.tc_hooks);
                     FStar_TypeChecker_Env.dsenv =
                       (uu___1442_10292.FStar_TypeChecker_Env.dsenv);
                     FStar_TypeChecker_Env.nbe =
                       (uu___1442_10292.FStar_TypeChecker_Env.nbe);
                     FStar_TypeChecker_Env.strict_args_tab =
                       (uu___1442_10292.FStar_TypeChecker_Env.strict_args_tab);
                     FStar_TypeChecker_Env.erasable_types_tab =
                       (uu___1442_10292.FStar_TypeChecker_Env.erasable_types_tab);
                     FStar_TypeChecker_Env.enable_defer_to_tac =
                       (uu___1442_10292.FStar_TypeChecker_Env.enable_defer_to_tac)
                   }) t
                 in
              match uu____10283 with
              | (uu____10296,lcomp,g) ->
                  let uu____10299 =
                    (let uu____10303 =
                       FStar_TypeChecker_Common.is_pure_or_ghost_lcomp lcomp
                        in
                     Prims.op_Negation uu____10303) ||
                      (let uu____10306 = FStar_TypeChecker_Env.is_trivial g
                          in
                       Prims.op_Negation uu____10306)
                     in
                  if uu____10299
                  then ret t
                  else
                    (let rewrite_eq =
                       let typ = lcomp.FStar_TypeChecker_Common.res_typ  in
                       let uu____10317 = new_uvar "pointwise_rec" env typ  in
                       bind uu____10317
                         (fun uu____10334  ->
                            match uu____10334 with
                            | (ut,uvar_ut) ->
                                (log ps
                                   (fun uu____10347  ->
                                      let uu____10348 =
                                        FStar_Syntax_Print.term_to_string t
                                         in
                                      let uu____10350 =
                                        FStar_Syntax_Print.term_to_string ut
                                         in
                                      FStar_Util.print2
                                        "Pointwise_rec: making equality\n\t%s ==\n\t%s\n"
                                        uu____10348 uu____10350);
                                 (let uu____10353 =
                                    let uu____10356 =
                                      let uu____10357 =
                                        FStar_TypeChecker_TcTerm.universe_of
                                          env typ
                                         in
                                      FStar_Syntax_Util.mk_eq2 uu____10357
                                        typ t ut
                                       in
                                    add_irrelevant_goal
                                      "pointwise_rec equation" env
                                      uu____10356 opts label1
                                     in
                                  bind uu____10353
                                    (fun uu____10361  ->
                                       let uu____10362 =
                                         bind tau
                                           (fun uu____10368  ->
                                              let ut1 =
                                                FStar_TypeChecker_Normalize.reduce_uvar_solutions
                                                  env ut
                                                 in
                                              log ps
                                                (fun uu____10374  ->
                                                   let uu____10375 =
                                                     FStar_Syntax_Print.term_to_string
                                                       t
                                                      in
                                                   let uu____10377 =
                                                     FStar_Syntax_Print.term_to_string
                                                       ut1
                                                      in
                                                   FStar_Util.print2
                                                     "pointwise_rec: succeeded rewriting\n\t%s to\n\t%s\n"
                                                     uu____10375 uu____10377);
                                              ret ut1)
                                          in
                                       focus uu____10362))))
                        in
                     let uu____10380 = catch rewrite_eq  in
                     bind uu____10380
                       (fun uu___5_10392  ->
                          match uu___5_10392 with
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
          let uu____10592 = FStar_Syntax_Subst.compress t  in
          maybe_continue ctrl uu____10592
            (fun t1  ->
               let uu____10600 =
                 f env
                   (let uu___1519_10608 = t1  in
                    {
                      FStar_Syntax_Syntax.n = (t1.FStar_Syntax_Syntax.n);
                      FStar_Syntax_Syntax.pos =
                        (uu___1519_10608.FStar_Syntax_Syntax.pos);
                      FStar_Syntax_Syntax.vars =
                        (uu___1519_10608.FStar_Syntax_Syntax.vars)
                    })
                  in
               bind uu____10600
                 (fun uu____10624  ->
                    match uu____10624 with
                    | (t2,ctrl1) ->
                        maybe_continue ctrl1 t2
                          (fun t3  ->
                             let uu____10647 =
                               let uu____10648 =
                                 FStar_Syntax_Subst.compress t3  in
                               uu____10648.FStar_Syntax_Syntax.n  in
                             match uu____10647 with
                             | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
                                 let uu____10685 =
                                   ctrl_tac_fold f env ctrl1 hd1  in
                                 bind uu____10685
                                   (fun uu____10707  ->
                                      match uu____10707 with
                                      | (hd2,ctrl2) ->
                                          let ctrl3 = keep_going ctrl2  in
                                          let uu____10723 =
                                            ctrl_tac_fold_args f env ctrl3
                                              args
                                             in
                                          bind uu____10723
                                            (fun uu____10747  ->
                                               match uu____10747 with
                                               | (args1,ctrl4) ->
                                                   ret
                                                     ((let uu___1499_10777 =
                                                         t3  in
                                                       {
                                                         FStar_Syntax_Syntax.n
                                                           =
                                                           (FStar_Syntax_Syntax.Tm_app
                                                              (hd2, args1));
                                                         FStar_Syntax_Syntax.pos
                                                           =
                                                           (uu___1499_10777.FStar_Syntax_Syntax.pos);
                                                         FStar_Syntax_Syntax.vars
                                                           =
                                                           (uu___1499_10777.FStar_Syntax_Syntax.vars)
                                                       }), ctrl4)))
                             | FStar_Syntax_Syntax.Tm_abs (bs,t4,k) ->
                                 let uu____10819 =
                                   FStar_Syntax_Subst.open_term bs t4  in
                                 (match uu____10819 with
                                  | (bs1,t') ->
                                      let uu____10834 =
                                        let uu____10841 =
                                          FStar_TypeChecker_Env.push_binders
                                            env bs1
                                           in
                                        ctrl_tac_fold f uu____10841 ctrl1 t'
                                         in
                                      bind uu____10834
                                        (fun uu____10856  ->
                                           match uu____10856 with
                                           | (t'',ctrl2) ->
                                               let uu____10871 =
                                                 let uu____10878 =
                                                   let uu___1512_10881 = t4
                                                      in
                                                   let uu____10884 =
                                                     let uu____10885 =
                                                       let uu____10904 =
                                                         FStar_Syntax_Subst.close_binders
                                                           bs1
                                                          in
                                                       let uu____10913 =
                                                         FStar_Syntax_Subst.close
                                                           bs1 t''
                                                          in
                                                       (uu____10904,
                                                         uu____10913, k)
                                                        in
                                                     FStar_Syntax_Syntax.Tm_abs
                                                       uu____10885
                                                      in
                                                   {
                                                     FStar_Syntax_Syntax.n =
                                                       uu____10884;
                                                     FStar_Syntax_Syntax.pos
                                                       =
                                                       (uu___1512_10881.FStar_Syntax_Syntax.pos);
                                                     FStar_Syntax_Syntax.vars
                                                       =
                                                       (uu___1512_10881.FStar_Syntax_Syntax.vars)
                                                   }  in
                                                 (uu____10878, ctrl2)  in
                                               ret uu____10871))
                             | FStar_Syntax_Syntax.Tm_arrow (bs,k) ->
                                 ret (t3, ctrl1)
                             | uu____10966 -> ret (t3, ctrl1))))

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
              let uu____11012 = ctrl_tac_fold f env ctrl t  in
              bind uu____11012
                (fun uu____11033  ->
                   match uu____11033 with
                   | (t1,ctrl1) ->
                       let uu____11048 = ctrl_tac_fold_args f env ctrl1 ts1
                          in
                       bind uu____11048
                         (fun uu____11072  ->
                            match uu____11072 with
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
                let uu____11163 =
                  let uu____11171 =
                    add_irrelevant_goal "dummy" env FStar_Syntax_Util.t_true
                      opts label1
                     in
                  bind uu____11171
                    (fun uu____11182  ->
                       let uu____11183 = ctrl t1  in
                       bind uu____11183
                         (fun res  ->
                            let uu____11209 = trivial ()  in
                            bind uu____11209 (fun uu____11218  -> ret res)))
                   in
                bind uu____11163
                  (fun uu____11236  ->
                     match uu____11236 with
                     | (should_rewrite,ctrl1) ->
                         if Prims.op_Negation should_rewrite
                         then ret (t1, ctrl1)
                         else
                           (let uu____11265 =
                              FStar_TypeChecker_TcTerm.tc_term
                                (let uu___1549_11274 = env  in
                                 {
                                   FStar_TypeChecker_Env.solver =
                                     (uu___1549_11274.FStar_TypeChecker_Env.solver);
                                   FStar_TypeChecker_Env.range =
                                     (uu___1549_11274.FStar_TypeChecker_Env.range);
                                   FStar_TypeChecker_Env.curmodule =
                                     (uu___1549_11274.FStar_TypeChecker_Env.curmodule);
                                   FStar_TypeChecker_Env.gamma =
                                     (uu___1549_11274.FStar_TypeChecker_Env.gamma);
                                   FStar_TypeChecker_Env.gamma_sig =
                                     (uu___1549_11274.FStar_TypeChecker_Env.gamma_sig);
                                   FStar_TypeChecker_Env.gamma_cache =
                                     (uu___1549_11274.FStar_TypeChecker_Env.gamma_cache);
                                   FStar_TypeChecker_Env.modules =
                                     (uu___1549_11274.FStar_TypeChecker_Env.modules);
                                   FStar_TypeChecker_Env.expected_typ =
                                     (uu___1549_11274.FStar_TypeChecker_Env.expected_typ);
                                   FStar_TypeChecker_Env.sigtab =
                                     (uu___1549_11274.FStar_TypeChecker_Env.sigtab);
                                   FStar_TypeChecker_Env.attrtab =
                                     (uu___1549_11274.FStar_TypeChecker_Env.attrtab);
                                   FStar_TypeChecker_Env.instantiate_imp =
                                     (uu___1549_11274.FStar_TypeChecker_Env.instantiate_imp);
                                   FStar_TypeChecker_Env.effects =
                                     (uu___1549_11274.FStar_TypeChecker_Env.effects);
                                   FStar_TypeChecker_Env.generalize =
                                     (uu___1549_11274.FStar_TypeChecker_Env.generalize);
                                   FStar_TypeChecker_Env.letrecs =
                                     (uu___1549_11274.FStar_TypeChecker_Env.letrecs);
                                   FStar_TypeChecker_Env.top_level =
                                     (uu___1549_11274.FStar_TypeChecker_Env.top_level);
                                   FStar_TypeChecker_Env.check_uvars =
                                     (uu___1549_11274.FStar_TypeChecker_Env.check_uvars);
                                   FStar_TypeChecker_Env.use_eq =
                                     (uu___1549_11274.FStar_TypeChecker_Env.use_eq);
                                   FStar_TypeChecker_Env.use_eq_strict =
                                     (uu___1549_11274.FStar_TypeChecker_Env.use_eq_strict);
                                   FStar_TypeChecker_Env.is_iface =
                                     (uu___1549_11274.FStar_TypeChecker_Env.is_iface);
                                   FStar_TypeChecker_Env.admit =
                                     (uu___1549_11274.FStar_TypeChecker_Env.admit);
                                   FStar_TypeChecker_Env.lax = true;
                                   FStar_TypeChecker_Env.lax_universes =
                                     (uu___1549_11274.FStar_TypeChecker_Env.lax_universes);
                                   FStar_TypeChecker_Env.phase1 =
                                     (uu___1549_11274.FStar_TypeChecker_Env.phase1);
                                   FStar_TypeChecker_Env.failhard =
                                     (uu___1549_11274.FStar_TypeChecker_Env.failhard);
                                   FStar_TypeChecker_Env.nosynth =
                                     (uu___1549_11274.FStar_TypeChecker_Env.nosynth);
                                   FStar_TypeChecker_Env.uvar_subtyping =
                                     (uu___1549_11274.FStar_TypeChecker_Env.uvar_subtyping);
                                   FStar_TypeChecker_Env.tc_term =
                                     (uu___1549_11274.FStar_TypeChecker_Env.tc_term);
                                   FStar_TypeChecker_Env.type_of =
                                     (uu___1549_11274.FStar_TypeChecker_Env.type_of);
                                   FStar_TypeChecker_Env.universe_of =
                                     (uu___1549_11274.FStar_TypeChecker_Env.universe_of);
                                   FStar_TypeChecker_Env.check_type_of =
                                     (uu___1549_11274.FStar_TypeChecker_Env.check_type_of);
                                   FStar_TypeChecker_Env.use_bv_sorts =
                                     (uu___1549_11274.FStar_TypeChecker_Env.use_bv_sorts);
                                   FStar_TypeChecker_Env.qtbl_name_and_index
                                     =
                                     (uu___1549_11274.FStar_TypeChecker_Env.qtbl_name_and_index);
                                   FStar_TypeChecker_Env.normalized_eff_names
                                     =
                                     (uu___1549_11274.FStar_TypeChecker_Env.normalized_eff_names);
                                   FStar_TypeChecker_Env.fv_delta_depths =
                                     (uu___1549_11274.FStar_TypeChecker_Env.fv_delta_depths);
                                   FStar_TypeChecker_Env.proof_ns =
                                     (uu___1549_11274.FStar_TypeChecker_Env.proof_ns);
                                   FStar_TypeChecker_Env.synth_hook =
                                     (uu___1549_11274.FStar_TypeChecker_Env.synth_hook);
                                   FStar_TypeChecker_Env.try_solve_implicits_hook
                                     =
                                     (uu___1549_11274.FStar_TypeChecker_Env.try_solve_implicits_hook);
                                   FStar_TypeChecker_Env.splice =
                                     (uu___1549_11274.FStar_TypeChecker_Env.splice);
                                   FStar_TypeChecker_Env.mpreprocess =
                                     (uu___1549_11274.FStar_TypeChecker_Env.mpreprocess);
                                   FStar_TypeChecker_Env.postprocess =
                                     (uu___1549_11274.FStar_TypeChecker_Env.postprocess);
                                   FStar_TypeChecker_Env.is_native_tactic =
                                     (uu___1549_11274.FStar_TypeChecker_Env.is_native_tactic);
                                   FStar_TypeChecker_Env.identifier_info =
                                     (uu___1549_11274.FStar_TypeChecker_Env.identifier_info);
                                   FStar_TypeChecker_Env.tc_hooks =
                                     (uu___1549_11274.FStar_TypeChecker_Env.tc_hooks);
                                   FStar_TypeChecker_Env.dsenv =
                                     (uu___1549_11274.FStar_TypeChecker_Env.dsenv);
                                   FStar_TypeChecker_Env.nbe =
                                     (uu___1549_11274.FStar_TypeChecker_Env.nbe);
                                   FStar_TypeChecker_Env.strict_args_tab =
                                     (uu___1549_11274.FStar_TypeChecker_Env.strict_args_tab);
                                   FStar_TypeChecker_Env.erasable_types_tab =
                                     (uu___1549_11274.FStar_TypeChecker_Env.erasable_types_tab);
                                   FStar_TypeChecker_Env.enable_defer_to_tac
                                     =
                                     (uu___1549_11274.FStar_TypeChecker_Env.enable_defer_to_tac)
                                 }) t1
                               in
                            match uu____11265 with
                            | (t2,lcomp,g) ->
                                let uu____11285 =
                                  (let uu____11289 =
                                     FStar_TypeChecker_Common.is_pure_or_ghost_lcomp
                                       lcomp
                                      in
                                   Prims.op_Negation uu____11289) ||
                                    (let uu____11292 =
                                       FStar_TypeChecker_Env.is_trivial g  in
                                     Prims.op_Negation uu____11292)
                                   in
                                if uu____11285
                                then ret (t2, globalStop)
                                else
                                  (let typ =
                                     lcomp.FStar_TypeChecker_Common.res_typ
                                      in
                                   let uu____11308 =
                                     new_uvar "pointwise_rec" env typ  in
                                   bind uu____11308
                                     (fun uu____11329  ->
                                        match uu____11329 with
                                        | (ut,uvar_ut) ->
                                            (log ps
                                               (fun uu____11346  ->
                                                  let uu____11347 =
                                                    FStar_Syntax_Print.term_to_string
                                                      t2
                                                     in
                                                  let uu____11349 =
                                                    FStar_Syntax_Print.term_to_string
                                                      ut
                                                     in
                                                  FStar_Util.print2
                                                    "Pointwise_rec: making equality\n\t%s ==\n\t%s\n"
                                                    uu____11347 uu____11349);
                                             (let uu____11352 =
                                                let uu____11355 =
                                                  let uu____11356 =
                                                    FStar_TypeChecker_TcTerm.universe_of
                                                      env typ
                                                     in
                                                  FStar_Syntax_Util.mk_eq2
                                                    uu____11356 typ t2 ut
                                                   in
                                                add_irrelevant_goal
                                                  "rewrite_rec equation" env
                                                  uu____11355 opts label1
                                                 in
                                              bind uu____11352
                                                (fun uu____11364  ->
                                                   let uu____11365 =
                                                     bind rewriter
                                                       (fun uu____11379  ->
                                                          let ut1 =
                                                            FStar_TypeChecker_Normalize.reduce_uvar_solutions
                                                              env ut
                                                             in
                                                          log ps
                                                            (fun uu____11385 
                                                               ->
                                                               let uu____11386
                                                                 =
                                                                 FStar_Syntax_Print.term_to_string
                                                                   t2
                                                                  in
                                                               let uu____11388
                                                                 =
                                                                 FStar_Syntax_Print.term_to_string
                                                                   ut1
                                                                  in
                                                               FStar_Util.print2
                                                                 "rewrite_rec: succeeded rewriting\n\t%s to\n\t%s\n"
                                                                 uu____11386
                                                                 uu____11388);
                                                          ret (ut1, ctrl1))
                                                      in
                                                   focus uu____11365)))))))
  
let (topdown_rewrite :
  (FStar_Syntax_Syntax.term -> (Prims.bool * FStar_BigInt.t) tac) ->
    unit tac -> unit tac)
  =
  fun ctrl  ->
    fun rewriter  ->
      let uu____11433 =
        bind get
          (fun ps  ->
             let uu____11443 =
               match ps.FStar_Tactics_Types.goals with
               | g::gs -> (g, gs)
               | [] -> failwith "no goals"  in
             match uu____11443 with
             | (g,gs) ->
                 let gt1 = FStar_Tactics_Types.goal_type g  in
                 (log ps
                    (fun uu____11481  ->
                       let uu____11482 =
                         FStar_Syntax_Print.term_to_string gt1  in
                       FStar_Util.print1 "Topdown_rewrite starting with %s\n"
                         uu____11482);
                  bind dismiss_all
                    (fun uu____11487  ->
                       let uu____11488 =
                         let uu____11495 = FStar_Tactics_Types.goal_env g  in
                         ctrl_tac_fold
                           (rewrite_rec ps ctrl rewriter
                              g.FStar_Tactics_Types.opts
                              g.FStar_Tactics_Types.label) uu____11495
                           keepGoing gt1
                          in
                       bind uu____11488
                         (fun uu____11505  ->
                            match uu____11505 with
                            | (gt',uu____11513) ->
                                (log ps
                                   (fun uu____11517  ->
                                      let uu____11518 =
                                        FStar_Syntax_Print.term_to_string gt'
                                         in
                                      FStar_Util.print1
                                        "Topdown_rewrite seems to have succeded with %s\n"
                                        uu____11518);
                                 (let uu____11521 = push_goals gs  in
                                  bind uu____11521
                                    (fun uu____11526  ->
                                       let uu____11527 =
                                         let uu____11530 =
                                           let uu____11531 =
                                             FStar_Tactics_Types.goal_with_type
                                               g gt'
                                              in
                                           FStar_All.pipe_right uu____11531
                                             bnorm_goal
                                            in
                                         [uu____11530]  in
                                       add_goals uu____11527)))))))
         in
      FStar_All.pipe_left (wrap_err "topdown_rewrite") uu____11433
  
let (t_pointwise : FStar_Tactics_Types.direction -> unit tac -> unit tac) =
  fun d  ->
    fun tau  ->
      let uu____11556 =
        bind get
          (fun ps  ->
             let uu____11566 =
               match ps.FStar_Tactics_Types.goals with
               | g::gs -> (g, gs)
               | [] -> failwith "no goals"  in
             match uu____11566 with
             | (g,gs) ->
                 let gt1 = FStar_Tactics_Types.goal_type g  in
                 (log ps
                    (fun uu____11604  ->
                       let uu____11605 =
                         FStar_Syntax_Print.term_to_string gt1  in
                       FStar_Util.print1 "Pointwise starting with %s\n"
                         uu____11605);
                  bind dismiss_all
                    (fun uu____11610  ->
                       let uu____11611 =
                         let uu____11614 = FStar_Tactics_Types.goal_env g  in
                         tac_fold_env d
                           (pointwise_rec ps tau g.FStar_Tactics_Types.opts
                              g.FStar_Tactics_Types.label) uu____11614 gt1
                          in
                       bind uu____11611
                         (fun gt'  ->
                            log ps
                              (fun uu____11622  ->
                                 let uu____11623 =
                                   FStar_Syntax_Print.term_to_string gt'  in
                                 FStar_Util.print1
                                   "Pointwise seems to have succeded with %s\n"
                                   uu____11623);
                            (let uu____11626 = push_goals gs  in
                             bind uu____11626
                               (fun uu____11631  ->
                                  let uu____11632 =
                                    let uu____11635 =
                                      let uu____11636 =
                                        FStar_Tactics_Types.goal_with_type g
                                          gt'
                                         in
                                      FStar_All.pipe_right uu____11636
                                        bnorm_goal
                                       in
                                    [uu____11635]  in
                                  add_goals uu____11632))))))
         in
      FStar_All.pipe_left (wrap_err "t_pointwise") uu____11556
  
let (_trefl :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> unit tac) =
  fun l  ->
    fun r  ->
      let uu____11657 = cur_goal ()  in
      bind uu____11657
        (fun g  ->
           let uu____11663 =
             let uu____11667 = FStar_Tactics_Types.goal_env g  in
             do_unify uu____11667 l r  in
           bind uu____11663
             (fun b  ->
                if b
                then solve' g FStar_Syntax_Util.exp_unit
                else
                  (let l1 =
                     let uu____11678 = FStar_Tactics_Types.goal_env g  in
                     FStar_TypeChecker_Normalize.normalize
                       [FStar_TypeChecker_Env.UnfoldUntil
                          FStar_Syntax_Syntax.delta_constant;
                       FStar_TypeChecker_Env.Primops;
                       FStar_TypeChecker_Env.UnfoldTac] uu____11678 l
                      in
                   let r1 =
                     let uu____11680 = FStar_Tactics_Types.goal_env g  in
                     FStar_TypeChecker_Normalize.normalize
                       [FStar_TypeChecker_Env.UnfoldUntil
                          FStar_Syntax_Syntax.delta_constant;
                       FStar_TypeChecker_Env.Primops;
                       FStar_TypeChecker_Env.UnfoldTac] uu____11680 r
                      in
                   let uu____11681 =
                     let uu____11685 = FStar_Tactics_Types.goal_env g  in
                     do_unify uu____11685 l1 r1  in
                   bind uu____11681
                     (fun b1  ->
                        if b1
                        then solve' g FStar_Syntax_Util.exp_unit
                        else
                          (let uu____11695 =
                             let uu____11702 =
                               let uu____11708 =
                                 FStar_Tactics_Types.goal_env g  in
                               tts uu____11708  in
                             FStar_TypeChecker_Err.print_discrepancy
                               uu____11702 l1 r1
                              in
                           match uu____11695 with
                           | (ls,rs) ->
                               fail2 "not a trivial equality ((%s) vs (%s))"
                                 ls rs)))))
  
let (trefl : unit -> unit tac) =
  fun uu____11725  ->
    let uu____11728 =
      let uu____11731 = cur_goal ()  in
      bind uu____11731
        (fun g  ->
           let uu____11739 =
             let uu____11746 =
               let uu____11747 = FStar_Tactics_Types.goal_env g  in
               let uu____11748 = FStar_Tactics_Types.goal_type g  in
               bnorm uu____11747 uu____11748  in
             destruct_eq uu____11746  in
           match uu____11739 with
           | FStar_Pervasives_Native.Some (l,r) -> _trefl l r
           | FStar_Pervasives_Native.None  ->
               let uu____11761 =
                 let uu____11763 = FStar_Tactics_Types.goal_env g  in
                 let uu____11764 = FStar_Tactics_Types.goal_type g  in
                 tts uu____11763 uu____11764  in
               fail1 "not an equality (%s)" uu____11761)
       in
    FStar_All.pipe_left (wrap_err "trefl") uu____11728
  
let (dup : unit -> unit tac) =
  fun uu____11778  ->
    let uu____11781 = cur_goal ()  in
    bind uu____11781
      (fun g  ->
         let uu____11787 =
           let uu____11794 = FStar_Tactics_Types.goal_env g  in
           let uu____11795 = FStar_Tactics_Types.goal_type g  in
           new_uvar "dup" uu____11794 uu____11795  in
         bind uu____11787
           (fun uu____11805  ->
              match uu____11805 with
              | (u,u_uvar) ->
                  let g' =
                    let uu___1632_11815 = g  in
                    {
                      FStar_Tactics_Types.goal_main_env =
                        (uu___1632_11815.FStar_Tactics_Types.goal_main_env);
                      FStar_Tactics_Types.goal_ctx_uvar = u_uvar;
                      FStar_Tactics_Types.opts =
                        (uu___1632_11815.FStar_Tactics_Types.opts);
                      FStar_Tactics_Types.is_guard =
                        (uu___1632_11815.FStar_Tactics_Types.is_guard);
                      FStar_Tactics_Types.label =
                        (uu___1632_11815.FStar_Tactics_Types.label)
                    }  in
                  bind __dismiss
                    (fun uu____11818  ->
                       let uu____11819 =
                         let uu____11822 = FStar_Tactics_Types.goal_env g  in
                         let uu____11823 =
                           let uu____11824 =
                             let uu____11825 = FStar_Tactics_Types.goal_env g
                                in
                             let uu____11826 =
                               FStar_Tactics_Types.goal_type g  in
                             FStar_TypeChecker_TcTerm.universe_of uu____11825
                               uu____11826
                              in
                           let uu____11827 = FStar_Tactics_Types.goal_type g
                              in
                           let uu____11828 =
                             FStar_Tactics_Types.goal_witness g  in
                           FStar_Syntax_Util.mk_eq2 uu____11824 uu____11827 u
                             uu____11828
                            in
                         add_irrelevant_goal "dup equation" uu____11822
                           uu____11823 g.FStar_Tactics_Types.opts
                           g.FStar_Tactics_Types.label
                          in
                       bind uu____11819
                         (fun uu____11832  ->
                            let uu____11833 = add_goals [g']  in
                            bind uu____11833 (fun uu____11837  -> ret ())))))
  
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
              let uu____11963 = f x y  in
              if uu____11963 then aux (x :: acc) xs ys else (acc, xs, ys)
          | uu____11986 -> (acc, l11, l21)  in
        let uu____12001 = aux [] l1 l2  in
        match uu____12001 with | (pr,t1,t2) -> ((FStar_List.rev pr), t1, t2)
  
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
      let uu____12107 = get_phi g1  in
      match uu____12107 with
      | FStar_Pervasives_Native.None  -> fail "goal 1 is not irrelevant"
      | FStar_Pervasives_Native.Some phi1 ->
          let uu____12114 = get_phi g2  in
          (match uu____12114 with
           | FStar_Pervasives_Native.None  -> fail "goal 2 is not irrelevant"
           | FStar_Pervasives_Native.Some phi2 ->
               let gamma1 =
                 (g1.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_gamma
                  in
               let gamma2 =
                 (g2.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_gamma
                  in
               let uu____12127 =
                 longest_prefix FStar_Syntax_Syntax.eq_binding
                   (FStar_List.rev gamma1) (FStar_List.rev gamma2)
                  in
               (match uu____12127 with
                | (gamma,r1,r2) ->
                    let t1 =
                      let uu____12158 =
                        FStar_TypeChecker_Env.binders_of_bindings
                          (FStar_List.rev r1)
                         in
                      close_forall_no_univs1 uu____12158 phi1  in
                    let t2 =
                      let uu____12168 =
                        FStar_TypeChecker_Env.binders_of_bindings
                          (FStar_List.rev r2)
                         in
                      close_forall_no_univs1 uu____12168 phi2  in
                    let uu____12177 =
                      set_solution g1 FStar_Syntax_Util.exp_unit  in
                    bind uu____12177
                      (fun uu____12182  ->
                         let uu____12183 =
                           set_solution g2 FStar_Syntax_Util.exp_unit  in
                         bind uu____12183
                           (fun uu____12190  ->
                              let ng = FStar_Syntax_Util.mk_conj t1 t2  in
                              let nenv =
                                let uu___1683_12195 =
                                  FStar_Tactics_Types.goal_env g1  in
                                let uu____12196 =
                                  FStar_Util.smap_create (Prims.of_int (100))
                                   in
                                {
                                  FStar_TypeChecker_Env.solver =
                                    (uu___1683_12195.FStar_TypeChecker_Env.solver);
                                  FStar_TypeChecker_Env.range =
                                    (uu___1683_12195.FStar_TypeChecker_Env.range);
                                  FStar_TypeChecker_Env.curmodule =
                                    (uu___1683_12195.FStar_TypeChecker_Env.curmodule);
                                  FStar_TypeChecker_Env.gamma =
                                    (FStar_List.rev gamma);
                                  FStar_TypeChecker_Env.gamma_sig =
                                    (uu___1683_12195.FStar_TypeChecker_Env.gamma_sig);
                                  FStar_TypeChecker_Env.gamma_cache =
                                    uu____12196;
                                  FStar_TypeChecker_Env.modules =
                                    (uu___1683_12195.FStar_TypeChecker_Env.modules);
                                  FStar_TypeChecker_Env.expected_typ =
                                    (uu___1683_12195.FStar_TypeChecker_Env.expected_typ);
                                  FStar_TypeChecker_Env.sigtab =
                                    (uu___1683_12195.FStar_TypeChecker_Env.sigtab);
                                  FStar_TypeChecker_Env.attrtab =
                                    (uu___1683_12195.FStar_TypeChecker_Env.attrtab);
                                  FStar_TypeChecker_Env.instantiate_imp =
                                    (uu___1683_12195.FStar_TypeChecker_Env.instantiate_imp);
                                  FStar_TypeChecker_Env.effects =
                                    (uu___1683_12195.FStar_TypeChecker_Env.effects);
                                  FStar_TypeChecker_Env.generalize =
                                    (uu___1683_12195.FStar_TypeChecker_Env.generalize);
                                  FStar_TypeChecker_Env.letrecs =
                                    (uu___1683_12195.FStar_TypeChecker_Env.letrecs);
                                  FStar_TypeChecker_Env.top_level =
                                    (uu___1683_12195.FStar_TypeChecker_Env.top_level);
                                  FStar_TypeChecker_Env.check_uvars =
                                    (uu___1683_12195.FStar_TypeChecker_Env.check_uvars);
                                  FStar_TypeChecker_Env.use_eq =
                                    (uu___1683_12195.FStar_TypeChecker_Env.use_eq);
                                  FStar_TypeChecker_Env.use_eq_strict =
                                    (uu___1683_12195.FStar_TypeChecker_Env.use_eq_strict);
                                  FStar_TypeChecker_Env.is_iface =
                                    (uu___1683_12195.FStar_TypeChecker_Env.is_iface);
                                  FStar_TypeChecker_Env.admit =
                                    (uu___1683_12195.FStar_TypeChecker_Env.admit);
                                  FStar_TypeChecker_Env.lax =
                                    (uu___1683_12195.FStar_TypeChecker_Env.lax);
                                  FStar_TypeChecker_Env.lax_universes =
                                    (uu___1683_12195.FStar_TypeChecker_Env.lax_universes);
                                  FStar_TypeChecker_Env.phase1 =
                                    (uu___1683_12195.FStar_TypeChecker_Env.phase1);
                                  FStar_TypeChecker_Env.failhard =
                                    (uu___1683_12195.FStar_TypeChecker_Env.failhard);
                                  FStar_TypeChecker_Env.nosynth =
                                    (uu___1683_12195.FStar_TypeChecker_Env.nosynth);
                                  FStar_TypeChecker_Env.uvar_subtyping =
                                    (uu___1683_12195.FStar_TypeChecker_Env.uvar_subtyping);
                                  FStar_TypeChecker_Env.tc_term =
                                    (uu___1683_12195.FStar_TypeChecker_Env.tc_term);
                                  FStar_TypeChecker_Env.type_of =
                                    (uu___1683_12195.FStar_TypeChecker_Env.type_of);
                                  FStar_TypeChecker_Env.universe_of =
                                    (uu___1683_12195.FStar_TypeChecker_Env.universe_of);
                                  FStar_TypeChecker_Env.check_type_of =
                                    (uu___1683_12195.FStar_TypeChecker_Env.check_type_of);
                                  FStar_TypeChecker_Env.use_bv_sorts =
                                    (uu___1683_12195.FStar_TypeChecker_Env.use_bv_sorts);
                                  FStar_TypeChecker_Env.qtbl_name_and_index =
                                    (uu___1683_12195.FStar_TypeChecker_Env.qtbl_name_and_index);
                                  FStar_TypeChecker_Env.normalized_eff_names
                                    =
                                    (uu___1683_12195.FStar_TypeChecker_Env.normalized_eff_names);
                                  FStar_TypeChecker_Env.fv_delta_depths =
                                    (uu___1683_12195.FStar_TypeChecker_Env.fv_delta_depths);
                                  FStar_TypeChecker_Env.proof_ns =
                                    (uu___1683_12195.FStar_TypeChecker_Env.proof_ns);
                                  FStar_TypeChecker_Env.synth_hook =
                                    (uu___1683_12195.FStar_TypeChecker_Env.synth_hook);
                                  FStar_TypeChecker_Env.try_solve_implicits_hook
                                    =
                                    (uu___1683_12195.FStar_TypeChecker_Env.try_solve_implicits_hook);
                                  FStar_TypeChecker_Env.splice =
                                    (uu___1683_12195.FStar_TypeChecker_Env.splice);
                                  FStar_TypeChecker_Env.mpreprocess =
                                    (uu___1683_12195.FStar_TypeChecker_Env.mpreprocess);
                                  FStar_TypeChecker_Env.postprocess =
                                    (uu___1683_12195.FStar_TypeChecker_Env.postprocess);
                                  FStar_TypeChecker_Env.is_native_tactic =
                                    (uu___1683_12195.FStar_TypeChecker_Env.is_native_tactic);
                                  FStar_TypeChecker_Env.identifier_info =
                                    (uu___1683_12195.FStar_TypeChecker_Env.identifier_info);
                                  FStar_TypeChecker_Env.tc_hooks =
                                    (uu___1683_12195.FStar_TypeChecker_Env.tc_hooks);
                                  FStar_TypeChecker_Env.dsenv =
                                    (uu___1683_12195.FStar_TypeChecker_Env.dsenv);
                                  FStar_TypeChecker_Env.nbe =
                                    (uu___1683_12195.FStar_TypeChecker_Env.nbe);
                                  FStar_TypeChecker_Env.strict_args_tab =
                                    (uu___1683_12195.FStar_TypeChecker_Env.strict_args_tab);
                                  FStar_TypeChecker_Env.erasable_types_tab =
                                    (uu___1683_12195.FStar_TypeChecker_Env.erasable_types_tab);
                                  FStar_TypeChecker_Env.enable_defer_to_tac =
                                    (uu___1683_12195.FStar_TypeChecker_Env.enable_defer_to_tac)
                                }  in
                              let uu____12200 =
                                mk_irrelevant_goal "joined" nenv ng
                                  g1.FStar_Tactics_Types.opts
                                  g1.FStar_Tactics_Types.label
                                 in
                              bind uu____12200
                                (fun goal  ->
                                   mlog
                                     (fun uu____12210  ->
                                        let uu____12211 =
                                          goal_to_string_verbose g1  in
                                        let uu____12213 =
                                          goal_to_string_verbose g2  in
                                        let uu____12215 =
                                          goal_to_string_verbose goal  in
                                        FStar_Util.print3
                                          "join_goals of\n(%s)\nand\n(%s)\n= (%s)\n"
                                          uu____12211 uu____12213 uu____12215)
                                     (fun uu____12219  -> ret goal))))))
  
let (join : unit -> unit tac) =
  fun uu____12227  ->
    bind get
      (fun ps  ->
         match ps.FStar_Tactics_Types.goals with
         | g1::g2::gs ->
             let uu____12243 =
               set
                 (let uu___1698_12248 = ps  in
                  {
                    FStar_Tactics_Types.main_context =
                      (uu___1698_12248.FStar_Tactics_Types.main_context);
                    FStar_Tactics_Types.all_implicits =
                      (uu___1698_12248.FStar_Tactics_Types.all_implicits);
                    FStar_Tactics_Types.goals = gs;
                    FStar_Tactics_Types.smt_goals =
                      (uu___1698_12248.FStar_Tactics_Types.smt_goals);
                    FStar_Tactics_Types.depth =
                      (uu___1698_12248.FStar_Tactics_Types.depth);
                    FStar_Tactics_Types.__dump =
                      (uu___1698_12248.FStar_Tactics_Types.__dump);
                    FStar_Tactics_Types.psc =
                      (uu___1698_12248.FStar_Tactics_Types.psc);
                    FStar_Tactics_Types.entry_range =
                      (uu___1698_12248.FStar_Tactics_Types.entry_range);
                    FStar_Tactics_Types.guard_policy =
                      (uu___1698_12248.FStar_Tactics_Types.guard_policy);
                    FStar_Tactics_Types.freshness =
                      (uu___1698_12248.FStar_Tactics_Types.freshness);
                    FStar_Tactics_Types.tac_verb_dbg =
                      (uu___1698_12248.FStar_Tactics_Types.tac_verb_dbg);
                    FStar_Tactics_Types.local_state =
                      (uu___1698_12248.FStar_Tactics_Types.local_state)
                  })
                in
             bind uu____12243
               (fun uu____12251  ->
                  let uu____12252 = join_goals g1 g2  in
                  bind uu____12252 (fun g12  -> add_goals [g12]))
         | uu____12257 -> fail "join: less than 2 goals")
  
let (set_options : Prims.string -> unit tac) =
  fun s  ->
    let uu____12273 =
      let uu____12276 = cur_goal ()  in
      bind uu____12276
        (fun g  ->
           FStar_Options.push ();
           (let uu____12289 = FStar_Util.smap_copy g.FStar_Tactics_Types.opts
               in
            FStar_Options.set uu____12289);
           (let res = FStar_Options.set_options s  in
            let opts' = FStar_Options.peek ()  in
            FStar_Options.pop ();
            (match res with
             | FStar_Getopt.Success  ->
                 let g' =
                   let uu___1709_12296 = g  in
                   {
                     FStar_Tactics_Types.goal_main_env =
                       (uu___1709_12296.FStar_Tactics_Types.goal_main_env);
                     FStar_Tactics_Types.goal_ctx_uvar =
                       (uu___1709_12296.FStar_Tactics_Types.goal_ctx_uvar);
                     FStar_Tactics_Types.opts = opts';
                     FStar_Tactics_Types.is_guard =
                       (uu___1709_12296.FStar_Tactics_Types.is_guard);
                     FStar_Tactics_Types.label =
                       (uu___1709_12296.FStar_Tactics_Types.label)
                   }  in
                 replace_cur g'
             | FStar_Getopt.Error err ->
                 fail2 "Setting options `%s` failed: %s" s err
             | FStar_Getopt.Help  ->
                 fail1 "Setting options `%s` failed (got `Help`?)" s)))
       in
    FStar_All.pipe_left (wrap_err "set_options") uu____12273
  
let (top_env : unit -> env tac) =
  fun uu____12313  ->
    bind get
      (fun ps  -> FStar_All.pipe_left ret ps.FStar_Tactics_Types.main_context)
  
let (lax_on : unit -> Prims.bool tac) =
  fun uu____12328  ->
    let uu____12332 = cur_goal ()  in
    bind uu____12332
      (fun g  ->
         let uu____12339 =
           (FStar_Options.lax ()) ||
             (let uu____12342 = FStar_Tactics_Types.goal_env g  in
              uu____12342.FStar_TypeChecker_Env.lax)
            in
         ret uu____12339)
  
let (unquote :
  FStar_Reflection_Data.typ ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term tac)
  =
  fun ty  ->
    fun tm  ->
      let uu____12359 =
        mlog
          (fun uu____12364  ->
             let uu____12365 = FStar_Syntax_Print.term_to_string tm  in
             FStar_Util.print1 "unquote: tm = %s\n" uu____12365)
          (fun uu____12370  ->
             let uu____12371 = cur_goal ()  in
             bind uu____12371
               (fun goal  ->
                  let env =
                    let uu____12379 = FStar_Tactics_Types.goal_env goal  in
                    FStar_TypeChecker_Env.set_expected_typ uu____12379 ty  in
                  let uu____12380 = __tc_ghost env tm  in
                  bind uu____12380
                    (fun uu____12399  ->
                       match uu____12399 with
                       | (tm1,typ,guard) ->
                           mlog
                             (fun uu____12413  ->
                                let uu____12414 =
                                  FStar_Syntax_Print.term_to_string tm1  in
                                FStar_Util.print1 "unquote: tm' = %s\n"
                                  uu____12414)
                             (fun uu____12418  ->
                                mlog
                                  (fun uu____12421  ->
                                     let uu____12422 =
                                       FStar_Syntax_Print.term_to_string typ
                                        in
                                     FStar_Util.print1 "unquote: typ = %s\n"
                                       uu____12422)
                                  (fun uu____12427  ->
                                     let uu____12428 =
                                       proc_guard "unquote" env guard  in
                                     bind uu____12428
                                       (fun uu____12433  -> ret tm1))))))
         in
      FStar_All.pipe_left (wrap_err "unquote") uu____12359
  
let (uvar_env :
  env ->
    FStar_Reflection_Data.typ FStar_Pervasives_Native.option ->
      FStar_Syntax_Syntax.term tac)
  =
  fun env  ->
    fun ty  ->
      let uu____12458 =
        match ty with
        | FStar_Pervasives_Native.Some ty1 -> ret ty1
        | FStar_Pervasives_Native.None  ->
            let uu____12464 =
              let uu____12471 =
                let uu____12472 = FStar_Syntax_Util.type_u ()  in
                FStar_All.pipe_left FStar_Pervasives_Native.fst uu____12472
                 in
              new_uvar "uvar_env.2" env uu____12471  in
            bind uu____12464
              (fun uu____12489  ->
                 match uu____12489 with | (typ,uvar_typ) -> ret typ)
         in
      bind uu____12458
        (fun typ  ->
           let uu____12501 = new_uvar "uvar_env" env typ  in
           bind uu____12501
             (fun uu____12516  ->
                match uu____12516 with | (t,uvar_t) -> ret t))
  
let (unshelve : FStar_Syntax_Syntax.term -> unit tac) =
  fun t  ->
    let uu____12535 =
      bind get
        (fun ps  ->
           let env = ps.FStar_Tactics_Types.main_context  in
           let opts =
             match ps.FStar_Tactics_Types.goals with
             | g::uu____12554 -> g.FStar_Tactics_Types.opts
             | uu____12557 -> FStar_Options.peek ()  in
           let uu____12560 = FStar_Syntax_Util.head_and_args t  in
           match uu____12560 with
           | ({
                FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                  (ctx_uvar,uu____12580);
                FStar_Syntax_Syntax.pos = uu____12581;
                FStar_Syntax_Syntax.vars = uu____12582;_},uu____12583)
               ->
               let env1 =
                 let uu___1763_12625 = env  in
                 {
                   FStar_TypeChecker_Env.solver =
                     (uu___1763_12625.FStar_TypeChecker_Env.solver);
                   FStar_TypeChecker_Env.range =
                     (uu___1763_12625.FStar_TypeChecker_Env.range);
                   FStar_TypeChecker_Env.curmodule =
                     (uu___1763_12625.FStar_TypeChecker_Env.curmodule);
                   FStar_TypeChecker_Env.gamma =
                     (ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_gamma);
                   FStar_TypeChecker_Env.gamma_sig =
                     (uu___1763_12625.FStar_TypeChecker_Env.gamma_sig);
                   FStar_TypeChecker_Env.gamma_cache =
                     (uu___1763_12625.FStar_TypeChecker_Env.gamma_cache);
                   FStar_TypeChecker_Env.modules =
                     (uu___1763_12625.FStar_TypeChecker_Env.modules);
                   FStar_TypeChecker_Env.expected_typ =
                     (uu___1763_12625.FStar_TypeChecker_Env.expected_typ);
                   FStar_TypeChecker_Env.sigtab =
                     (uu___1763_12625.FStar_TypeChecker_Env.sigtab);
                   FStar_TypeChecker_Env.attrtab =
                     (uu___1763_12625.FStar_TypeChecker_Env.attrtab);
                   FStar_TypeChecker_Env.instantiate_imp =
                     (uu___1763_12625.FStar_TypeChecker_Env.instantiate_imp);
                   FStar_TypeChecker_Env.effects =
                     (uu___1763_12625.FStar_TypeChecker_Env.effects);
                   FStar_TypeChecker_Env.generalize =
                     (uu___1763_12625.FStar_TypeChecker_Env.generalize);
                   FStar_TypeChecker_Env.letrecs =
                     (uu___1763_12625.FStar_TypeChecker_Env.letrecs);
                   FStar_TypeChecker_Env.top_level =
                     (uu___1763_12625.FStar_TypeChecker_Env.top_level);
                   FStar_TypeChecker_Env.check_uvars =
                     (uu___1763_12625.FStar_TypeChecker_Env.check_uvars);
                   FStar_TypeChecker_Env.use_eq =
                     (uu___1763_12625.FStar_TypeChecker_Env.use_eq);
                   FStar_TypeChecker_Env.use_eq_strict =
                     (uu___1763_12625.FStar_TypeChecker_Env.use_eq_strict);
                   FStar_TypeChecker_Env.is_iface =
                     (uu___1763_12625.FStar_TypeChecker_Env.is_iface);
                   FStar_TypeChecker_Env.admit =
                     (uu___1763_12625.FStar_TypeChecker_Env.admit);
                   FStar_TypeChecker_Env.lax =
                     (uu___1763_12625.FStar_TypeChecker_Env.lax);
                   FStar_TypeChecker_Env.lax_universes =
                     (uu___1763_12625.FStar_TypeChecker_Env.lax_universes);
                   FStar_TypeChecker_Env.phase1 =
                     (uu___1763_12625.FStar_TypeChecker_Env.phase1);
                   FStar_TypeChecker_Env.failhard =
                     (uu___1763_12625.FStar_TypeChecker_Env.failhard);
                   FStar_TypeChecker_Env.nosynth =
                     (uu___1763_12625.FStar_TypeChecker_Env.nosynth);
                   FStar_TypeChecker_Env.uvar_subtyping =
                     (uu___1763_12625.FStar_TypeChecker_Env.uvar_subtyping);
                   FStar_TypeChecker_Env.tc_term =
                     (uu___1763_12625.FStar_TypeChecker_Env.tc_term);
                   FStar_TypeChecker_Env.type_of =
                     (uu___1763_12625.FStar_TypeChecker_Env.type_of);
                   FStar_TypeChecker_Env.universe_of =
                     (uu___1763_12625.FStar_TypeChecker_Env.universe_of);
                   FStar_TypeChecker_Env.check_type_of =
                     (uu___1763_12625.FStar_TypeChecker_Env.check_type_of);
                   FStar_TypeChecker_Env.use_bv_sorts =
                     (uu___1763_12625.FStar_TypeChecker_Env.use_bv_sorts);
                   FStar_TypeChecker_Env.qtbl_name_and_index =
                     (uu___1763_12625.FStar_TypeChecker_Env.qtbl_name_and_index);
                   FStar_TypeChecker_Env.normalized_eff_names =
                     (uu___1763_12625.FStar_TypeChecker_Env.normalized_eff_names);
                   FStar_TypeChecker_Env.fv_delta_depths =
                     (uu___1763_12625.FStar_TypeChecker_Env.fv_delta_depths);
                   FStar_TypeChecker_Env.proof_ns =
                     (uu___1763_12625.FStar_TypeChecker_Env.proof_ns);
                   FStar_TypeChecker_Env.synth_hook =
                     (uu___1763_12625.FStar_TypeChecker_Env.synth_hook);
                   FStar_TypeChecker_Env.try_solve_implicits_hook =
                     (uu___1763_12625.FStar_TypeChecker_Env.try_solve_implicits_hook);
                   FStar_TypeChecker_Env.splice =
                     (uu___1763_12625.FStar_TypeChecker_Env.splice);
                   FStar_TypeChecker_Env.mpreprocess =
                     (uu___1763_12625.FStar_TypeChecker_Env.mpreprocess);
                   FStar_TypeChecker_Env.postprocess =
                     (uu___1763_12625.FStar_TypeChecker_Env.postprocess);
                   FStar_TypeChecker_Env.is_native_tactic =
                     (uu___1763_12625.FStar_TypeChecker_Env.is_native_tactic);
                   FStar_TypeChecker_Env.identifier_info =
                     (uu___1763_12625.FStar_TypeChecker_Env.identifier_info);
                   FStar_TypeChecker_Env.tc_hooks =
                     (uu___1763_12625.FStar_TypeChecker_Env.tc_hooks);
                   FStar_TypeChecker_Env.dsenv =
                     (uu___1763_12625.FStar_TypeChecker_Env.dsenv);
                   FStar_TypeChecker_Env.nbe =
                     (uu___1763_12625.FStar_TypeChecker_Env.nbe);
                   FStar_TypeChecker_Env.strict_args_tab =
                     (uu___1763_12625.FStar_TypeChecker_Env.strict_args_tab);
                   FStar_TypeChecker_Env.erasable_types_tab =
                     (uu___1763_12625.FStar_TypeChecker_Env.erasable_types_tab);
                   FStar_TypeChecker_Env.enable_defer_to_tac =
                     (uu___1763_12625.FStar_TypeChecker_Env.enable_defer_to_tac)
                 }  in
               let g =
                 FStar_Tactics_Types.mk_goal env1 ctx_uvar opts false ""  in
               let uu____12629 =
                 let uu____12632 = bnorm_goal g  in [uu____12632]  in
               add_goals uu____12629
           | uu____12633 -> fail "not a uvar")
       in
    FStar_All.pipe_left (wrap_err "unshelve") uu____12535
  
let (tac_and : Prims.bool tac -> Prims.bool tac -> Prims.bool tac) =
  fun t1  ->
    fun t2  ->
      let comp =
        bind t1
          (fun b  ->
             let uu____12695 = if b then t2 else ret false  in
             bind uu____12695 (fun b'  -> if b' then ret b' else fail ""))
         in
      let uu____12721 = trytac comp  in
      bind uu____12721
        (fun uu___6_12733  ->
           match uu___6_12733 with
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
        let uu____12775 =
          bind get
            (fun ps  ->
               let uu____12783 = __tc e t1  in
               bind uu____12783
                 (fun uu____12804  ->
                    match uu____12804 with
                    | (t11,ty1,g1) ->
                        let uu____12817 = __tc e t2  in
                        bind uu____12817
                          (fun uu____12838  ->
                             match uu____12838 with
                             | (t21,ty2,g2) ->
                                 let uu____12851 =
                                   proc_guard "unify_env g1" e g1  in
                                 bind uu____12851
                                   (fun uu____12858  ->
                                      let uu____12859 =
                                        proc_guard "unify_env g2" e g2  in
                                      bind uu____12859
                                        (fun uu____12867  ->
                                           let uu____12868 =
                                             do_unify e ty1 ty2  in
                                           let uu____12872 =
                                             do_unify e t11 t21  in
                                           tac_and uu____12868 uu____12872)))))
           in
        FStar_All.pipe_left (wrap_err "unify_env") uu____12775
  
let (launch_process :
  Prims.string -> Prims.string Prims.list -> Prims.string -> Prims.string tac)
  =
  fun prog  ->
    fun args  ->
      fun input  ->
        bind idtac
          (fun uu____12920  ->
             let uu____12921 = FStar_Options.unsafe_tactic_exec ()  in
             if uu____12921
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
        (fun uu____12955  ->
           let uu____12956 =
             FStar_Syntax_Syntax.gen_bv nm FStar_Pervasives_Native.None t  in
           ret uu____12956)
  
let (change : FStar_Reflection_Data.typ -> unit tac) =
  fun ty  ->
    let uu____12967 =
      mlog
        (fun uu____12972  ->
           let uu____12973 = FStar_Syntax_Print.term_to_string ty  in
           FStar_Util.print1 "change: ty = %s\n" uu____12973)
        (fun uu____12978  ->
           let uu____12979 = cur_goal ()  in
           bind uu____12979
             (fun g  ->
                let uu____12985 =
                  let uu____12994 = FStar_Tactics_Types.goal_env g  in
                  __tc uu____12994 ty  in
                bind uu____12985
                  (fun uu____13006  ->
                     match uu____13006 with
                     | (ty1,uu____13016,guard) ->
                         let uu____13018 =
                           let uu____13021 = FStar_Tactics_Types.goal_env g
                              in
                           proc_guard "change" uu____13021 guard  in
                         bind uu____13018
                           (fun uu____13025  ->
                              let uu____13026 =
                                let uu____13030 =
                                  FStar_Tactics_Types.goal_env g  in
                                let uu____13031 =
                                  FStar_Tactics_Types.goal_type g  in
                                do_unify uu____13030 uu____13031 ty1  in
                              bind uu____13026
                                (fun bb  ->
                                   if bb
                                   then
                                     let uu____13040 =
                                       FStar_Tactics_Types.goal_with_type g
                                         ty1
                                        in
                                     replace_cur uu____13040
                                   else
                                     (let steps =
                                        [FStar_TypeChecker_Env.AllowUnboundUniverses;
                                        FStar_TypeChecker_Env.UnfoldUntil
                                          FStar_Syntax_Syntax.delta_constant;
                                        FStar_TypeChecker_Env.Primops]  in
                                      let ng =
                                        let uu____13047 =
                                          FStar_Tactics_Types.goal_env g  in
                                        let uu____13048 =
                                          FStar_Tactics_Types.goal_type g  in
                                        normalize steps uu____13047
                                          uu____13048
                                         in
                                      let nty =
                                        let uu____13050 =
                                          FStar_Tactics_Types.goal_env g  in
                                        normalize steps uu____13050 ty1  in
                                      let uu____13051 =
                                        let uu____13055 =
                                          FStar_Tactics_Types.goal_env g  in
                                        do_unify uu____13055 ng nty  in
                                      bind uu____13051
                                        (fun b  ->
                                           if b
                                           then
                                             let uu____13064 =
                                               FStar_Tactics_Types.goal_with_type
                                                 g ty1
                                                in
                                             replace_cur uu____13064
                                           else fail "not convertible")))))))
       in
    FStar_All.pipe_left (wrap_err "change") uu____12967
  
let failwhen : 'a . Prims.bool -> Prims.string -> (unit -> 'a tac) -> 'a tac
  = fun b  -> fun msg  -> fun k  -> if b then fail msg else k () 
let (t_destruct :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.fv * FStar_BigInt.t) Prims.list tac)
  =
  fun s_tm  ->
    let uu____13138 =
      let uu____13147 = cur_goal ()  in
      bind uu____13147
        (fun g  ->
           let uu____13159 =
             let uu____13168 = FStar_Tactics_Types.goal_env g  in
             __tc uu____13168 s_tm  in
           bind uu____13159
             (fun uu____13186  ->
                match uu____13186 with
                | (s_tm1,s_ty,guard) ->
                    let uu____13204 =
                      let uu____13207 = FStar_Tactics_Types.goal_env g  in
                      proc_guard "destruct" uu____13207 guard  in
                    bind uu____13204
                      (fun uu____13221  ->
                         let s_ty1 =
                           let uu____13223 = FStar_Tactics_Types.goal_env g
                              in
                           FStar_TypeChecker_Normalize.normalize
                             [FStar_TypeChecker_Env.UnfoldTac;
                             FStar_TypeChecker_Env.Weak;
                             FStar_TypeChecker_Env.HNF;
                             FStar_TypeChecker_Env.UnfoldUntil
                               FStar_Syntax_Syntax.delta_constant]
                             uu____13223 s_ty
                            in
                         let uu____13224 =
                           FStar_Syntax_Util.head_and_args' s_ty1  in
                         match uu____13224 with
                         | (h,args) ->
                             let uu____13269 =
                               let uu____13276 =
                                 let uu____13277 =
                                   FStar_Syntax_Subst.compress h  in
                                 uu____13277.FStar_Syntax_Syntax.n  in
                               match uu____13276 with
                               | FStar_Syntax_Syntax.Tm_fvar fv ->
                                   ret (fv, [])
                               | FStar_Syntax_Syntax.Tm_uinst
                                   ({
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.Tm_fvar fv;
                                      FStar_Syntax_Syntax.pos = uu____13292;
                                      FStar_Syntax_Syntax.vars = uu____13293;_},us)
                                   -> ret (fv, us)
                               | uu____13303 -> fail "type is not an fv"  in
                             bind uu____13269
                               (fun uu____13324  ->
                                  match uu____13324 with
                                  | (fv,a_us) ->
                                      let t_lid =
                                        FStar_Syntax_Syntax.lid_of_fv fv  in
                                      let uu____13340 =
                                        let uu____13343 =
                                          FStar_Tactics_Types.goal_env g  in
                                        FStar_TypeChecker_Env.lookup_sigelt
                                          uu____13343 t_lid
                                         in
                                      (match uu____13340 with
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
                                                let uu____13384 =
                                                  erasable &&
                                                    (let uu____13387 =
                                                       is_irrelevant g  in
                                                     Prims.op_Negation
                                                       uu____13387)
                                                   in
                                                failwhen uu____13384
                                                  "cannot destruct erasable type to solve proof-relevant goal"
                                                  (fun uu____13397  ->
                                                     failwhen
                                                       ((FStar_List.length
                                                           a_us)
                                                          <>
                                                          (FStar_List.length
                                                             t_us))
                                                       "t_us don't match?"
                                                       (fun uu____13410  ->
                                                          let uu____13411 =
                                                            FStar_Syntax_Subst.open_term
                                                              t_ps t_ty
                                                             in
                                                          match uu____13411
                                                          with
                                                          | (t_ps1,t_ty1) ->
                                                              let uu____13426
                                                                =
                                                                mapM
                                                                  (fun c_lid 
                                                                    ->
                                                                    let uu____13454
                                                                    =
                                                                    let uu____13457
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    g  in
                                                                    FStar_TypeChecker_Env.lookup_sigelt
                                                                    uu____13457
                                                                    c_lid  in
                                                                    match uu____13454
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
                                                                    uu____13534
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
                                                                    let uu____13539
                                                                    =
                                                                    FStar_TypeChecker_Env.inst_tscheme
                                                                    (c_us,
                                                                    c_ty1)
                                                                     in
                                                                    match uu____13539
                                                                    with
                                                                    | 
                                                                    (c_us1,c_ty2)
                                                                    ->
                                                                    let uu____13562
                                                                    =
                                                                    FStar_Syntax_Util.arrow_formals_comp
                                                                    c_ty2  in
                                                                    (match uu____13562
                                                                    with
                                                                    | 
                                                                    (bs,comp)
                                                                    ->
                                                                    let uu____13581
                                                                    =
                                                                    let rename_bv
                                                                    bv =
                                                                    let ppname
                                                                    =
                                                                    bv.FStar_Syntax_Syntax.ppname
                                                                     in
                                                                    let ppname1
                                                                    =
                                                                    let uu___1890_13604
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
                                                                    (uu___1890_13604.FStar_Ident.idRange)
                                                                    }  in
                                                                    FStar_Syntax_Syntax.freshen_bv
                                                                    (let uu___1893_13608
                                                                    = bv  in
                                                                    {
                                                                    FStar_Syntax_Syntax.ppname
                                                                    = ppname1;
                                                                    FStar_Syntax_Syntax.index
                                                                    =
                                                                    (uu___1893_13608.FStar_Syntax_Syntax.index);
                                                                    FStar_Syntax_Syntax.sort
                                                                    =
                                                                    (uu___1893_13608.FStar_Syntax_Syntax.sort)
                                                                    })  in
                                                                    let bs' =
                                                                    FStar_List.map
                                                                    (fun
                                                                    uu____13634
                                                                     ->
                                                                    match uu____13634
                                                                    with
                                                                    | 
                                                                    (bv,aq)
                                                                    ->
                                                                    let uu____13653
                                                                    =
                                                                    rename_bv
                                                                    bv  in
                                                                    (uu____13653,
                                                                    aq)) bs
                                                                     in
                                                                    let subst1
                                                                    =
                                                                    FStar_List.map2
                                                                    (fun
                                                                    uu____13678
                                                                     ->
                                                                    fun
                                                                    uu____13679
                                                                     ->
                                                                    match 
                                                                    (uu____13678,
                                                                    uu____13679)
                                                                    with
                                                                    | 
                                                                    ((bv,uu____13705),
                                                                    (bv',uu____13707))
                                                                    ->
                                                                    let uu____13728
                                                                    =
                                                                    let uu____13735
                                                                    =
                                                                    FStar_Syntax_Syntax.bv_to_name
                                                                    bv'  in
                                                                    (bv,
                                                                    uu____13735)
                                                                     in
                                                                    FStar_Syntax_Syntax.NT
                                                                    uu____13728)
                                                                    bs bs'
                                                                     in
                                                                    let uu____13740
                                                                    =
                                                                    FStar_Syntax_Subst.subst_binders
                                                                    subst1
                                                                    bs'  in
                                                                    let uu____13749
                                                                    =
                                                                    FStar_Syntax_Subst.subst_comp
                                                                    subst1
                                                                    comp  in
                                                                    (uu____13740,
                                                                    uu____13749)
                                                                     in
                                                                    (match uu____13581
                                                                    with
                                                                    | 
                                                                    (bs1,comp1)
                                                                    ->
                                                                    let uu____13796
                                                                    =
                                                                    FStar_List.splitAt
                                                                    nparam
                                                                    bs1  in
                                                                    (match uu____13796
                                                                    with
                                                                    | 
                                                                    (d_ps,bs2)
                                                                    ->
                                                                    let uu____13869
                                                                    =
                                                                    let uu____13871
                                                                    =
                                                                    FStar_Syntax_Util.is_total_comp
                                                                    comp1  in
                                                                    Prims.op_Negation
                                                                    uu____13871
                                                                     in
                                                                    failwhen
                                                                    uu____13869
                                                                    "not total?"
                                                                    (fun
                                                                    uu____13890
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
                                                                    uu___7_13907
                                                                    =
                                                                    match uu___7_13907
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    (FStar_Syntax_Syntax.Implicit
                                                                    uu____13911)
                                                                    -> true
                                                                    | 
                                                                    uu____13914
                                                                    -> false
                                                                     in
                                                                    let uu____13918
                                                                    =
                                                                    FStar_List.splitAt
                                                                    nparam
                                                                    args  in
                                                                    match uu____13918
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
                                                                    uu____14054
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
                                                                    uu____14116
                                                                     ->
                                                                    match uu____14116
                                                                    with
                                                                    | 
                                                                    ((bv,uu____14136),
                                                                    (t,uu____14138))
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
                                                                    uu____14208
                                                                     ->
                                                                    match uu____14208
                                                                    with
                                                                    | 
                                                                    ((bv,uu____14235),
                                                                    (t,uu____14237))
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
                                                                    uu____14296
                                                                     ->
                                                                    match uu____14296
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
                                                                    let uu____14351
                                                                    =
                                                                    FStar_TypeChecker_TcTerm.tc_pat
                                                                    (let uu___1952_14375
                                                                    = env  in
                                                                    {
                                                                    FStar_TypeChecker_Env.solver
                                                                    =
                                                                    (uu___1952_14375.FStar_TypeChecker_Env.solver);
                                                                    FStar_TypeChecker_Env.range
                                                                    =
                                                                    (uu___1952_14375.FStar_TypeChecker_Env.range);
                                                                    FStar_TypeChecker_Env.curmodule
                                                                    =
                                                                    (uu___1952_14375.FStar_TypeChecker_Env.curmodule);
                                                                    FStar_TypeChecker_Env.gamma
                                                                    =
                                                                    (uu___1952_14375.FStar_TypeChecker_Env.gamma);
                                                                    FStar_TypeChecker_Env.gamma_sig
                                                                    =
                                                                    (uu___1952_14375.FStar_TypeChecker_Env.gamma_sig);
                                                                    FStar_TypeChecker_Env.gamma_cache
                                                                    =
                                                                    (uu___1952_14375.FStar_TypeChecker_Env.gamma_cache);
                                                                    FStar_TypeChecker_Env.modules
                                                                    =
                                                                    (uu___1952_14375.FStar_TypeChecker_Env.modules);
                                                                    FStar_TypeChecker_Env.expected_typ
                                                                    =
                                                                    (uu___1952_14375.FStar_TypeChecker_Env.expected_typ);
                                                                    FStar_TypeChecker_Env.sigtab
                                                                    =
                                                                    (uu___1952_14375.FStar_TypeChecker_Env.sigtab);
                                                                    FStar_TypeChecker_Env.attrtab
                                                                    =
                                                                    (uu___1952_14375.FStar_TypeChecker_Env.attrtab);
                                                                    FStar_TypeChecker_Env.instantiate_imp
                                                                    =
                                                                    (uu___1952_14375.FStar_TypeChecker_Env.instantiate_imp);
                                                                    FStar_TypeChecker_Env.effects
                                                                    =
                                                                    (uu___1952_14375.FStar_TypeChecker_Env.effects);
                                                                    FStar_TypeChecker_Env.generalize
                                                                    =
                                                                    (uu___1952_14375.FStar_TypeChecker_Env.generalize);
                                                                    FStar_TypeChecker_Env.letrecs
                                                                    =
                                                                    (uu___1952_14375.FStar_TypeChecker_Env.letrecs);
                                                                    FStar_TypeChecker_Env.top_level
                                                                    =
                                                                    (uu___1952_14375.FStar_TypeChecker_Env.top_level);
                                                                    FStar_TypeChecker_Env.check_uvars
                                                                    =
                                                                    (uu___1952_14375.FStar_TypeChecker_Env.check_uvars);
                                                                    FStar_TypeChecker_Env.use_eq
                                                                    =
                                                                    (uu___1952_14375.FStar_TypeChecker_Env.use_eq);
                                                                    FStar_TypeChecker_Env.use_eq_strict
                                                                    =
                                                                    (uu___1952_14375.FStar_TypeChecker_Env.use_eq_strict);
                                                                    FStar_TypeChecker_Env.is_iface
                                                                    =
                                                                    (uu___1952_14375.FStar_TypeChecker_Env.is_iface);
                                                                    FStar_TypeChecker_Env.admit
                                                                    =
                                                                    (uu___1952_14375.FStar_TypeChecker_Env.admit);
                                                                    FStar_TypeChecker_Env.lax
                                                                    = true;
                                                                    FStar_TypeChecker_Env.lax_universes
                                                                    =
                                                                    (uu___1952_14375.FStar_TypeChecker_Env.lax_universes);
                                                                    FStar_TypeChecker_Env.phase1
                                                                    =
                                                                    (uu___1952_14375.FStar_TypeChecker_Env.phase1);
                                                                    FStar_TypeChecker_Env.failhard
                                                                    =
                                                                    (uu___1952_14375.FStar_TypeChecker_Env.failhard);
                                                                    FStar_TypeChecker_Env.nosynth
                                                                    =
                                                                    (uu___1952_14375.FStar_TypeChecker_Env.nosynth);
                                                                    FStar_TypeChecker_Env.uvar_subtyping
                                                                    =
                                                                    (uu___1952_14375.FStar_TypeChecker_Env.uvar_subtyping);
                                                                    FStar_TypeChecker_Env.tc_term
                                                                    =
                                                                    (uu___1952_14375.FStar_TypeChecker_Env.tc_term);
                                                                    FStar_TypeChecker_Env.type_of
                                                                    =
                                                                    (uu___1952_14375.FStar_TypeChecker_Env.type_of);
                                                                    FStar_TypeChecker_Env.universe_of
                                                                    =
                                                                    (uu___1952_14375.FStar_TypeChecker_Env.universe_of);
                                                                    FStar_TypeChecker_Env.check_type_of
                                                                    =
                                                                    (uu___1952_14375.FStar_TypeChecker_Env.check_type_of);
                                                                    FStar_TypeChecker_Env.use_bv_sorts
                                                                    =
                                                                    (uu___1952_14375.FStar_TypeChecker_Env.use_bv_sorts);
                                                                    FStar_TypeChecker_Env.qtbl_name_and_index
                                                                    =
                                                                    (uu___1952_14375.FStar_TypeChecker_Env.qtbl_name_and_index);
                                                                    FStar_TypeChecker_Env.normalized_eff_names
                                                                    =
                                                                    (uu___1952_14375.FStar_TypeChecker_Env.normalized_eff_names);
                                                                    FStar_TypeChecker_Env.fv_delta_depths
                                                                    =
                                                                    (uu___1952_14375.FStar_TypeChecker_Env.fv_delta_depths);
                                                                    FStar_TypeChecker_Env.proof_ns
                                                                    =
                                                                    (uu___1952_14375.FStar_TypeChecker_Env.proof_ns);
                                                                    FStar_TypeChecker_Env.synth_hook
                                                                    =
                                                                    (uu___1952_14375.FStar_TypeChecker_Env.synth_hook);
                                                                    FStar_TypeChecker_Env.try_solve_implicits_hook
                                                                    =
                                                                    (uu___1952_14375.FStar_TypeChecker_Env.try_solve_implicits_hook);
                                                                    FStar_TypeChecker_Env.splice
                                                                    =
                                                                    (uu___1952_14375.FStar_TypeChecker_Env.splice);
                                                                    FStar_TypeChecker_Env.mpreprocess
                                                                    =
                                                                    (uu___1952_14375.FStar_TypeChecker_Env.mpreprocess);
                                                                    FStar_TypeChecker_Env.postprocess
                                                                    =
                                                                    (uu___1952_14375.FStar_TypeChecker_Env.postprocess);
                                                                    FStar_TypeChecker_Env.is_native_tactic
                                                                    =
                                                                    (uu___1952_14375.FStar_TypeChecker_Env.is_native_tactic);
                                                                    FStar_TypeChecker_Env.identifier_info
                                                                    =
                                                                    (uu___1952_14375.FStar_TypeChecker_Env.identifier_info);
                                                                    FStar_TypeChecker_Env.tc_hooks
                                                                    =
                                                                    (uu___1952_14375.FStar_TypeChecker_Env.tc_hooks);
                                                                    FStar_TypeChecker_Env.dsenv
                                                                    =
                                                                    (uu___1952_14375.FStar_TypeChecker_Env.dsenv);
                                                                    FStar_TypeChecker_Env.nbe
                                                                    =
                                                                    (uu___1952_14375.FStar_TypeChecker_Env.nbe);
                                                                    FStar_TypeChecker_Env.strict_args_tab
                                                                    =
                                                                    (uu___1952_14375.FStar_TypeChecker_Env.strict_args_tab);
                                                                    FStar_TypeChecker_Env.erasable_types_tab
                                                                    =
                                                                    (uu___1952_14375.FStar_TypeChecker_Env.erasable_types_tab);
                                                                    FStar_TypeChecker_Env.enable_defer_to_tac
                                                                    =
                                                                    (uu___1952_14375.FStar_TypeChecker_Env.enable_defer_to_tac)
                                                                    }) s_ty1
                                                                    pat  in
                                                                    match uu____14351
                                                                    with
                                                                    | 
                                                                    (uu____14389,uu____14390,uu____14391,uu____14392,pat_t,uu____14394,_guard_pat,_erasable)
                                                                    ->
                                                                    let eq_b
                                                                    =
                                                                    let uu____14408
                                                                    =
                                                                    let uu____14409
                                                                    =
                                                                    FStar_Syntax_Util.mk_eq2
                                                                    equ s_ty1
                                                                    s_tm1
                                                                    pat_t  in
                                                                    FStar_Syntax_Util.mk_squash
                                                                    equ
                                                                    uu____14409
                                                                     in
                                                                    FStar_Syntax_Syntax.gen_bv
                                                                    "breq"
                                                                    FStar_Pervasives_Native.None
                                                                    uu____14408
                                                                     in
                                                                    let cod1
                                                                    =
                                                                    let uu____14414
                                                                    =
                                                                    let uu____14423
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_binder
                                                                    eq_b  in
                                                                    [uu____14423]
                                                                     in
                                                                    let uu____14442
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Total
                                                                    cod  in
                                                                    FStar_Syntax_Util.arrow
                                                                    uu____14414
                                                                    uu____14442
                                                                     in
                                                                    let nty =
                                                                    let uu____14448
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Total
                                                                    cod1  in
                                                                    FStar_Syntax_Util.arrow
                                                                    bs3
                                                                    uu____14448
                                                                     in
                                                                    let uu____14451
                                                                    =
                                                                    new_uvar
                                                                    "destruct branch"
                                                                    env nty
                                                                     in
                                                                    bind
                                                                    uu____14451
                                                                    (fun
                                                                    uu____14481
                                                                     ->
                                                                    match uu____14481
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
                                                                    let uu____14508
                                                                    =
                                                                    let uu____14519
                                                                    =
                                                                    FStar_Syntax_Syntax.as_arg
                                                                    FStar_Syntax_Util.exp_unit
                                                                     in
                                                                    [uu____14519]
                                                                     in
                                                                    FStar_Syntax_Util.mk_app
                                                                    brt
                                                                    uu____14508
                                                                     in
                                                                    let br =
                                                                    FStar_Syntax_Subst.close_branch
                                                                    (pat,
                                                                    FStar_Pervasives_Native.None,
                                                                    brt1)  in
                                                                    let uu____14555
                                                                    =
                                                                    let uu____14566
                                                                    =
                                                                    let uu____14571
                                                                    =
                                                                    FStar_BigInt.of_int_fs
                                                                    (FStar_List.length
                                                                    bs3)  in
                                                                    (fv1,
                                                                    uu____14571)
                                                                     in
                                                                    (g', br,
                                                                    uu____14566)
                                                                     in
                                                                    ret
                                                                    uu____14555)))))))
                                                                    | 
                                                                    uu____14592
                                                                    ->
                                                                    fail
                                                                    "impossible: not a ctor"))
                                                                  c_lids
                                                                 in
                                                              bind
                                                                uu____13426
                                                                (fun goal_brs
                                                                    ->
                                                                   let uu____14642
                                                                    =
                                                                    FStar_List.unzip3
                                                                    goal_brs
                                                                     in
                                                                   match uu____14642
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
                                                                    let uu____14715
                                                                    =
                                                                    solve' g
                                                                    w  in
                                                                    bind
                                                                    uu____14715
                                                                    (fun
                                                                    uu____14726
                                                                     ->
                                                                    let uu____14727
                                                                    =
                                                                    add_goals
                                                                    goals  in
                                                                    bind
                                                                    uu____14727
                                                                    (fun
                                                                    uu____14737
                                                                     ->
                                                                    ret infos)))))
                                            | uu____14744 ->
                                                fail "not an inductive type"))))))
       in
    FStar_All.pipe_left (wrap_err "destruct") uu____13138
  
let rec last : 'a . 'a Prims.list -> 'a =
  fun l  ->
    match l with
    | [] -> failwith "last: empty list"
    | x::[] -> x
    | uu____14793::xs -> last xs
  
let rec init : 'a . 'a Prims.list -> 'a Prims.list =
  fun l  ->
    match l with
    | [] -> failwith "init: empty list"
    | x::[] -> []
    | x::xs -> let uu____14823 = init xs  in x :: uu____14823
  
let rec (inspect :
  FStar_Syntax_Syntax.term -> FStar_Reflection_Data.term_view tac) =
  fun t  ->
    let uu____14836 =
      let t1 = FStar_Syntax_Util.unascribe t  in
      let t2 = FStar_Syntax_Util.un_uinst t1  in
      let t3 = FStar_Syntax_Util.unlazy_emb t2  in
      match t3.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_meta (t4,uu____14845) -> inspect t4
      | FStar_Syntax_Syntax.Tm_name bv ->
          FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_Var bv)
      | FStar_Syntax_Syntax.Tm_bvar bv ->
          FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_BVar bv)
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_FVar fv)
      | FStar_Syntax_Syntax.Tm_app (hd1,[]) ->
          failwith "empty arguments on Tm_app"
      | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
          let uu____14911 = last args  in
          (match uu____14911 with
           | (a,q) ->
               let q' = FStar_Reflection_Basic.inspect_aqual q  in
               let uu____14941 =
                 let uu____14942 =
                   let uu____14947 =
                     let uu____14948 =
                       let uu____14953 = init args  in
                       FStar_Syntax_Syntax.mk_Tm_app hd1 uu____14953  in
                     uu____14948 FStar_Pervasives_Native.None
                       t3.FStar_Syntax_Syntax.pos
                      in
                   (uu____14947, (a, q'))  in
                 FStar_Reflection_Data.Tv_App uu____14942  in
               FStar_All.pipe_left ret uu____14941)
      | FStar_Syntax_Syntax.Tm_abs ([],uu____14964,uu____14965) ->
          failwith "empty arguments on Tm_abs"
      | FStar_Syntax_Syntax.Tm_abs (bs,t4,k) ->
          let uu____15018 = FStar_Syntax_Subst.open_term bs t4  in
          (match uu____15018 with
           | (bs1,t5) ->
               (match bs1 with
                | [] -> failwith "impossible"
                | b::bs2 ->
                    let uu____15060 =
                      let uu____15061 =
                        let uu____15066 = FStar_Syntax_Util.abs bs2 t5 k  in
                        (b, uu____15066)  in
                      FStar_Reflection_Data.Tv_Abs uu____15061  in
                    FStar_All.pipe_left ret uu____15060))
      | FStar_Syntax_Syntax.Tm_type uu____15069 ->
          FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_Type ())
      | FStar_Syntax_Syntax.Tm_arrow ([],k) ->
          failwith "empty binders on arrow"
      | FStar_Syntax_Syntax.Tm_arrow uu____15094 ->
          let uu____15109 = FStar_Syntax_Util.arrow_one t3  in
          (match uu____15109 with
           | FStar_Pervasives_Native.Some (b,c) ->
               FStar_All.pipe_left ret
                 (FStar_Reflection_Data.Tv_Arrow (b, c))
           | FStar_Pervasives_Native.None  -> failwith "impossible")
      | FStar_Syntax_Syntax.Tm_refine (bv,t4) ->
          let b = FStar_Syntax_Syntax.mk_binder bv  in
          let uu____15140 = FStar_Syntax_Subst.open_term [b] t4  in
          (match uu____15140 with
           | (b',t5) ->
               let b1 =
                 match b' with
                 | b'1::[] -> b'1
                 | uu____15193 -> failwith "impossible"  in
               FStar_All.pipe_left ret
                 (FStar_Reflection_Data.Tv_Refine
                    ((FStar_Pervasives_Native.fst b1), t5)))
      | FStar_Syntax_Syntax.Tm_constant c ->
          let uu____15206 =
            let uu____15207 = FStar_Reflection_Basic.inspect_const c  in
            FStar_Reflection_Data.Tv_Const uu____15207  in
          FStar_All.pipe_left ret uu____15206
      | FStar_Syntax_Syntax.Tm_uvar (ctx_u,s) ->
          let uu____15228 =
            let uu____15229 =
              let uu____15234 =
                let uu____15235 =
                  FStar_Syntax_Unionfind.uvar_id
                    ctx_u.FStar_Syntax_Syntax.ctx_uvar_head
                   in
                FStar_BigInt.of_int_fs uu____15235  in
              (uu____15234, (ctx_u, s))  in
            FStar_Reflection_Data.Tv_Uvar uu____15229  in
          FStar_All.pipe_left ret uu____15228
      | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),t21) ->
          if lb.FStar_Syntax_Syntax.lbunivs <> []
          then FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown
          else
            (match lb.FStar_Syntax_Syntax.lbname with
             | FStar_Util.Inr uu____15275 ->
                 FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown
             | FStar_Util.Inl bv ->
                 let b = FStar_Syntax_Syntax.mk_binder bv  in
                 let uu____15280 = FStar_Syntax_Subst.open_term [b] t21  in
                 (match uu____15280 with
                  | (bs,t22) ->
                      let b1 =
                        match bs with
                        | b1::[] -> b1
                        | uu____15333 ->
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
             | FStar_Util.Inr uu____15377 ->
                 FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown
             | FStar_Util.Inl bv ->
                 let uu____15381 = FStar_Syntax_Subst.open_let_rec [lb] t21
                    in
                 (match uu____15381 with
                  | (lbs,t22) ->
                      (match lbs with
                       | lb1::[] ->
                           (match lb1.FStar_Syntax_Syntax.lbname with
                            | FStar_Util.Inr uu____15401 ->
                                ret FStar_Reflection_Data.Tv_Unknown
                            | FStar_Util.Inl bv1 ->
                                FStar_All.pipe_left ret
                                  (FStar_Reflection_Data.Tv_Let
                                     (true,
                                       (lb1.FStar_Syntax_Syntax.lbattrs),
                                       bv1, (lb1.FStar_Syntax_Syntax.lbdef),
                                       t22)))
                       | uu____15409 ->
                           failwith
                             "impossible: open_term returned different amount of binders")))
      | FStar_Syntax_Syntax.Tm_match (t4,brs) ->
          let rec inspect_pat p =
            match p.FStar_Syntax_Syntax.v with
            | FStar_Syntax_Syntax.Pat_constant c ->
                let uu____15464 = FStar_Reflection_Basic.inspect_const c  in
                FStar_Reflection_Data.Pat_Constant uu____15464
            | FStar_Syntax_Syntax.Pat_cons (fv,ps) ->
                let uu____15485 =
                  let uu____15497 =
                    FStar_List.map
                      (fun uu____15521  ->
                         match uu____15521 with
                         | (p1,b) ->
                             let uu____15542 = inspect_pat p1  in
                             (uu____15542, b)) ps
                     in
                  (fv, uu____15497)  in
                FStar_Reflection_Data.Pat_Cons uu____15485
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
              (fun uu___8_15638  ->
                 match uu___8_15638 with
                 | (pat,uu____15660,t5) ->
                     let uu____15678 = inspect_pat pat  in (uu____15678, t5))
              brs1
             in
          FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_Match (t4, brs2))
      | FStar_Syntax_Syntax.Tm_unknown  ->
          FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown
      | uu____15687 ->
          ((let uu____15689 =
              let uu____15695 =
                let uu____15697 = FStar_Syntax_Print.tag_of_term t3  in
                let uu____15699 = FStar_Syntax_Print.term_to_string t3  in
                FStar_Util.format2
                  "inspect: outside of expected syntax (%s, %s)\n"
                  uu____15697 uu____15699
                 in
              (FStar_Errors.Warning_CantInspect, uu____15695)  in
            FStar_Errors.log_issue t3.FStar_Syntax_Syntax.pos uu____15689);
           FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown)
       in
    wrap_err "inspect" uu____14836
  
let (pack : FStar_Reflection_Data.term_view -> FStar_Syntax_Syntax.term tac)
  =
  fun tv  ->
    match tv with
    | FStar_Reflection_Data.Tv_Var bv ->
        let uu____15717 = FStar_Syntax_Syntax.bv_to_name bv  in
        FStar_All.pipe_left ret uu____15717
    | FStar_Reflection_Data.Tv_BVar bv ->
        let uu____15721 = FStar_Syntax_Syntax.bv_to_tm bv  in
        FStar_All.pipe_left ret uu____15721
    | FStar_Reflection_Data.Tv_FVar fv ->
        let uu____15725 = FStar_Syntax_Syntax.fv_to_tm fv  in
        FStar_All.pipe_left ret uu____15725
    | FStar_Reflection_Data.Tv_App (l,(r,q)) ->
        let q' = FStar_Reflection_Basic.pack_aqual q  in
        let uu____15732 = FStar_Syntax_Util.mk_app l [(r, q')]  in
        FStar_All.pipe_left ret uu____15732
    | FStar_Reflection_Data.Tv_Abs (b,t) ->
        let uu____15757 =
          FStar_Syntax_Util.abs [b] t FStar_Pervasives_Native.None  in
        FStar_All.pipe_left ret uu____15757
    | FStar_Reflection_Data.Tv_Arrow (b,c) ->
        let uu____15774 = FStar_Syntax_Util.arrow [b] c  in
        FStar_All.pipe_left ret uu____15774
    | FStar_Reflection_Data.Tv_Type () ->
        FStar_All.pipe_left ret FStar_Syntax_Util.ktype
    | FStar_Reflection_Data.Tv_Refine (bv,t) ->
        let uu____15793 = FStar_Syntax_Util.refine bv t  in
        FStar_All.pipe_left ret uu____15793
    | FStar_Reflection_Data.Tv_Const c ->
        let uu____15797 =
          let uu____15798 =
            let uu____15805 =
              let uu____15806 = FStar_Reflection_Basic.pack_const c  in
              FStar_Syntax_Syntax.Tm_constant uu____15806  in
            FStar_Syntax_Syntax.mk uu____15805  in
          uu____15798 FStar_Pervasives_Native.None FStar_Range.dummyRange  in
        FStar_All.pipe_left ret uu____15797
    | FStar_Reflection_Data.Tv_Uvar (_u,ctx_u_s) ->
        let uu____15811 =
          FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_uvar ctx_u_s)
            FStar_Pervasives_Native.None FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____15811
    | FStar_Reflection_Data.Tv_Let (false ,attrs,bv,t1,t2) ->
        let lb =
          FStar_Syntax_Util.mk_letbinding (FStar_Util.Inl bv) []
            bv.FStar_Syntax_Syntax.sort FStar_Parser_Const.effect_Tot_lid t1
            attrs FStar_Range.dummyRange
           in
        let uu____15825 =
          let uu____15826 =
            let uu____15833 =
              let uu____15834 =
                let uu____15848 =
                  let uu____15851 =
                    let uu____15852 = FStar_Syntax_Syntax.mk_binder bv  in
                    [uu____15852]  in
                  FStar_Syntax_Subst.close uu____15851 t2  in
                ((false, [lb]), uu____15848)  in
              FStar_Syntax_Syntax.Tm_let uu____15834  in
            FStar_Syntax_Syntax.mk uu____15833  in
          uu____15826 FStar_Pervasives_Native.None FStar_Range.dummyRange  in
        FStar_All.pipe_left ret uu____15825
    | FStar_Reflection_Data.Tv_Let (true ,attrs,bv,t1,t2) ->
        let lb =
          FStar_Syntax_Util.mk_letbinding (FStar_Util.Inl bv) []
            bv.FStar_Syntax_Syntax.sort FStar_Parser_Const.effect_Tot_lid t1
            attrs FStar_Range.dummyRange
           in
        let uu____15897 = FStar_Syntax_Subst.close_let_rec [lb] t2  in
        (match uu____15897 with
         | (lbs,body) ->
             let uu____15912 =
               FStar_Syntax_Syntax.mk
                 (FStar_Syntax_Syntax.Tm_let ((true, lbs), body))
                 FStar_Pervasives_Native.None FStar_Range.dummyRange
                in
             FStar_All.pipe_left ret uu____15912)
    | FStar_Reflection_Data.Tv_Match (t,brs) ->
        let wrap v1 =
          {
            FStar_Syntax_Syntax.v = v1;
            FStar_Syntax_Syntax.p = FStar_Range.dummyRange
          }  in
        let rec pack_pat p =
          match p with
          | FStar_Reflection_Data.Pat_Constant c ->
              let uu____15949 =
                let uu____15950 = FStar_Reflection_Basic.pack_const c  in
                FStar_Syntax_Syntax.Pat_constant uu____15950  in
              FStar_All.pipe_left wrap uu____15949
          | FStar_Reflection_Data.Pat_Cons (fv,ps) ->
              let uu____15967 =
                let uu____15968 =
                  let uu____15982 =
                    FStar_List.map
                      (fun uu____16006  ->
                         match uu____16006 with
                         | (p1,b) ->
                             let uu____16021 = pack_pat p1  in
                             (uu____16021, b)) ps
                     in
                  (fv, uu____15982)  in
                FStar_Syntax_Syntax.Pat_cons uu____15968  in
              FStar_All.pipe_left wrap uu____15967
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
            (fun uu___9_16069  ->
               match uu___9_16069 with
               | (pat,t1) ->
                   let uu____16086 = pack_pat pat  in
                   (uu____16086, FStar_Pervasives_Native.None, t1)) brs
           in
        let brs2 = FStar_List.map FStar_Syntax_Subst.close_branch brs1  in
        let uu____16134 =
          FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_match (t, brs2))
            FStar_Pervasives_Native.None FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____16134
    | FStar_Reflection_Data.Tv_AscribedT (e,t,tacopt) ->
        let uu____16162 =
          FStar_Syntax_Syntax.mk
            (FStar_Syntax_Syntax.Tm_ascribed
               (e, ((FStar_Util.Inl t), tacopt),
                 FStar_Pervasives_Native.None)) FStar_Pervasives_Native.None
            FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____16162
    | FStar_Reflection_Data.Tv_AscribedC (e,c,tacopt) ->
        let uu____16208 =
          FStar_Syntax_Syntax.mk
            (FStar_Syntax_Syntax.Tm_ascribed
               (e, ((FStar_Util.Inr c), tacopt),
                 FStar_Pervasives_Native.None)) FStar_Pervasives_Native.None
            FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____16208
    | FStar_Reflection_Data.Tv_Unknown  ->
        let uu____16247 =
          FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown
            FStar_Pervasives_Native.None FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____16247
  
let (lget :
  FStar_Reflection_Data.typ -> Prims.string -> FStar_Syntax_Syntax.term tac)
  =
  fun ty  ->
    fun k  ->
      let uu____16267 =
        bind get
          (fun ps  ->
             let uu____16273 =
               FStar_Util.psmap_try_find ps.FStar_Tactics_Types.local_state k
                in
             match uu____16273 with
             | FStar_Pervasives_Native.None  -> fail "not found"
             | FStar_Pervasives_Native.Some t -> unquote ty t)
         in
      FStar_All.pipe_left (wrap_err "lget") uu____16267
  
let (lset :
  FStar_Reflection_Data.typ ->
    Prims.string -> FStar_Syntax_Syntax.term -> unit tac)
  =
  fun _ty  ->
    fun k  ->
      fun t  ->
        let uu____16307 =
          bind get
            (fun ps  ->
               let ps1 =
                 let uu___2256_16314 = ps  in
                 let uu____16315 =
                   FStar_Util.psmap_add ps.FStar_Tactics_Types.local_state k
                     t
                    in
                 {
                   FStar_Tactics_Types.main_context =
                     (uu___2256_16314.FStar_Tactics_Types.main_context);
                   FStar_Tactics_Types.all_implicits =
                     (uu___2256_16314.FStar_Tactics_Types.all_implicits);
                   FStar_Tactics_Types.goals =
                     (uu___2256_16314.FStar_Tactics_Types.goals);
                   FStar_Tactics_Types.smt_goals =
                     (uu___2256_16314.FStar_Tactics_Types.smt_goals);
                   FStar_Tactics_Types.depth =
                     (uu___2256_16314.FStar_Tactics_Types.depth);
                   FStar_Tactics_Types.__dump =
                     (uu___2256_16314.FStar_Tactics_Types.__dump);
                   FStar_Tactics_Types.psc =
                     (uu___2256_16314.FStar_Tactics_Types.psc);
                   FStar_Tactics_Types.entry_range =
                     (uu___2256_16314.FStar_Tactics_Types.entry_range);
                   FStar_Tactics_Types.guard_policy =
                     (uu___2256_16314.FStar_Tactics_Types.guard_policy);
                   FStar_Tactics_Types.freshness =
                     (uu___2256_16314.FStar_Tactics_Types.freshness);
                   FStar_Tactics_Types.tac_verb_dbg =
                     (uu___2256_16314.FStar_Tactics_Types.tac_verb_dbg);
                   FStar_Tactics_Types.local_state = uu____16315
                 }  in
               set ps1)
           in
        FStar_All.pipe_left (wrap_err "lset") uu____16307
  
let (goal_of_goal_ty :
  env ->
    FStar_Reflection_Data.typ ->
      (FStar_Tactics_Types.goal * FStar_TypeChecker_Common.guard_t))
  =
  fun env  ->
    fun typ  ->
      let uu____16342 =
        FStar_TypeChecker_Util.new_implicit_var "proofstate_of_goal_ty"
          typ.FStar_Syntax_Syntax.pos env typ
         in
      match uu____16342 with
      | (u,ctx_uvars,g_u) ->
          let uu____16375 = FStar_List.hd ctx_uvars  in
          (match uu____16375 with
           | (ctx_uvar,uu____16389) ->
               let g =
                 let uu____16391 = FStar_Options.peek ()  in
                 FStar_Tactics_Types.mk_goal env ctx_uvar uu____16391 false
                   ""
                  in
               (g, g_u))
  
let (tac_env : FStar_TypeChecker_Env.env -> FStar_TypeChecker_Env.env) =
  fun env  ->
    let uu____16400 = FStar_TypeChecker_Env.clear_expected_typ env  in
    match uu____16400 with
    | (env1,uu____16408) ->
        let env2 =
          let uu___2273_16414 = env1  in
          {
            FStar_TypeChecker_Env.solver =
              (uu___2273_16414.FStar_TypeChecker_Env.solver);
            FStar_TypeChecker_Env.range =
              (uu___2273_16414.FStar_TypeChecker_Env.range);
            FStar_TypeChecker_Env.curmodule =
              (uu___2273_16414.FStar_TypeChecker_Env.curmodule);
            FStar_TypeChecker_Env.gamma =
              (uu___2273_16414.FStar_TypeChecker_Env.gamma);
            FStar_TypeChecker_Env.gamma_sig =
              (uu___2273_16414.FStar_TypeChecker_Env.gamma_sig);
            FStar_TypeChecker_Env.gamma_cache =
              (uu___2273_16414.FStar_TypeChecker_Env.gamma_cache);
            FStar_TypeChecker_Env.modules =
              (uu___2273_16414.FStar_TypeChecker_Env.modules);
            FStar_TypeChecker_Env.expected_typ =
              (uu___2273_16414.FStar_TypeChecker_Env.expected_typ);
            FStar_TypeChecker_Env.sigtab =
              (uu___2273_16414.FStar_TypeChecker_Env.sigtab);
            FStar_TypeChecker_Env.attrtab =
              (uu___2273_16414.FStar_TypeChecker_Env.attrtab);
            FStar_TypeChecker_Env.instantiate_imp = false;
            FStar_TypeChecker_Env.effects =
              (uu___2273_16414.FStar_TypeChecker_Env.effects);
            FStar_TypeChecker_Env.generalize =
              (uu___2273_16414.FStar_TypeChecker_Env.generalize);
            FStar_TypeChecker_Env.letrecs =
              (uu___2273_16414.FStar_TypeChecker_Env.letrecs);
            FStar_TypeChecker_Env.top_level =
              (uu___2273_16414.FStar_TypeChecker_Env.top_level);
            FStar_TypeChecker_Env.check_uvars =
              (uu___2273_16414.FStar_TypeChecker_Env.check_uvars);
            FStar_TypeChecker_Env.use_eq =
              (uu___2273_16414.FStar_TypeChecker_Env.use_eq);
            FStar_TypeChecker_Env.use_eq_strict =
              (uu___2273_16414.FStar_TypeChecker_Env.use_eq_strict);
            FStar_TypeChecker_Env.is_iface =
              (uu___2273_16414.FStar_TypeChecker_Env.is_iface);
            FStar_TypeChecker_Env.admit =
              (uu___2273_16414.FStar_TypeChecker_Env.admit);
            FStar_TypeChecker_Env.lax =
              (uu___2273_16414.FStar_TypeChecker_Env.lax);
            FStar_TypeChecker_Env.lax_universes =
              (uu___2273_16414.FStar_TypeChecker_Env.lax_universes);
            FStar_TypeChecker_Env.phase1 =
              (uu___2273_16414.FStar_TypeChecker_Env.phase1);
            FStar_TypeChecker_Env.failhard =
              (uu___2273_16414.FStar_TypeChecker_Env.failhard);
            FStar_TypeChecker_Env.nosynth =
              (uu___2273_16414.FStar_TypeChecker_Env.nosynth);
            FStar_TypeChecker_Env.uvar_subtyping =
              (uu___2273_16414.FStar_TypeChecker_Env.uvar_subtyping);
            FStar_TypeChecker_Env.tc_term =
              (uu___2273_16414.FStar_TypeChecker_Env.tc_term);
            FStar_TypeChecker_Env.type_of =
              (uu___2273_16414.FStar_TypeChecker_Env.type_of);
            FStar_TypeChecker_Env.universe_of =
              (uu___2273_16414.FStar_TypeChecker_Env.universe_of);
            FStar_TypeChecker_Env.check_type_of =
              (uu___2273_16414.FStar_TypeChecker_Env.check_type_of);
            FStar_TypeChecker_Env.use_bv_sorts =
              (uu___2273_16414.FStar_TypeChecker_Env.use_bv_sorts);
            FStar_TypeChecker_Env.qtbl_name_and_index =
              (uu___2273_16414.FStar_TypeChecker_Env.qtbl_name_and_index);
            FStar_TypeChecker_Env.normalized_eff_names =
              (uu___2273_16414.FStar_TypeChecker_Env.normalized_eff_names);
            FStar_TypeChecker_Env.fv_delta_depths =
              (uu___2273_16414.FStar_TypeChecker_Env.fv_delta_depths);
            FStar_TypeChecker_Env.proof_ns =
              (uu___2273_16414.FStar_TypeChecker_Env.proof_ns);
            FStar_TypeChecker_Env.synth_hook =
              (uu___2273_16414.FStar_TypeChecker_Env.synth_hook);
            FStar_TypeChecker_Env.try_solve_implicits_hook =
              (uu___2273_16414.FStar_TypeChecker_Env.try_solve_implicits_hook);
            FStar_TypeChecker_Env.splice =
              (uu___2273_16414.FStar_TypeChecker_Env.splice);
            FStar_TypeChecker_Env.mpreprocess =
              (uu___2273_16414.FStar_TypeChecker_Env.mpreprocess);
            FStar_TypeChecker_Env.postprocess =
              (uu___2273_16414.FStar_TypeChecker_Env.postprocess);
            FStar_TypeChecker_Env.is_native_tactic =
              (uu___2273_16414.FStar_TypeChecker_Env.is_native_tactic);
            FStar_TypeChecker_Env.identifier_info =
              (uu___2273_16414.FStar_TypeChecker_Env.identifier_info);
            FStar_TypeChecker_Env.tc_hooks =
              (uu___2273_16414.FStar_TypeChecker_Env.tc_hooks);
            FStar_TypeChecker_Env.dsenv =
              (uu___2273_16414.FStar_TypeChecker_Env.dsenv);
            FStar_TypeChecker_Env.nbe =
              (uu___2273_16414.FStar_TypeChecker_Env.nbe);
            FStar_TypeChecker_Env.strict_args_tab =
              (uu___2273_16414.FStar_TypeChecker_Env.strict_args_tab);
            FStar_TypeChecker_Env.erasable_types_tab =
              (uu___2273_16414.FStar_TypeChecker_Env.erasable_types_tab);
            FStar_TypeChecker_Env.enable_defer_to_tac =
              (uu___2273_16414.FStar_TypeChecker_Env.enable_defer_to_tac)
          }  in
        let env3 =
          let uu___2276_16417 = env2  in
          {
            FStar_TypeChecker_Env.solver =
              (uu___2276_16417.FStar_TypeChecker_Env.solver);
            FStar_TypeChecker_Env.range =
              (uu___2276_16417.FStar_TypeChecker_Env.range);
            FStar_TypeChecker_Env.curmodule =
              (uu___2276_16417.FStar_TypeChecker_Env.curmodule);
            FStar_TypeChecker_Env.gamma =
              (uu___2276_16417.FStar_TypeChecker_Env.gamma);
            FStar_TypeChecker_Env.gamma_sig =
              (uu___2276_16417.FStar_TypeChecker_Env.gamma_sig);
            FStar_TypeChecker_Env.gamma_cache =
              (uu___2276_16417.FStar_TypeChecker_Env.gamma_cache);
            FStar_TypeChecker_Env.modules =
              (uu___2276_16417.FStar_TypeChecker_Env.modules);
            FStar_TypeChecker_Env.expected_typ =
              (uu___2276_16417.FStar_TypeChecker_Env.expected_typ);
            FStar_TypeChecker_Env.sigtab =
              (uu___2276_16417.FStar_TypeChecker_Env.sigtab);
            FStar_TypeChecker_Env.attrtab =
              (uu___2276_16417.FStar_TypeChecker_Env.attrtab);
            FStar_TypeChecker_Env.instantiate_imp =
              (uu___2276_16417.FStar_TypeChecker_Env.instantiate_imp);
            FStar_TypeChecker_Env.effects =
              (uu___2276_16417.FStar_TypeChecker_Env.effects);
            FStar_TypeChecker_Env.generalize =
              (uu___2276_16417.FStar_TypeChecker_Env.generalize);
            FStar_TypeChecker_Env.letrecs =
              (uu___2276_16417.FStar_TypeChecker_Env.letrecs);
            FStar_TypeChecker_Env.top_level =
              (uu___2276_16417.FStar_TypeChecker_Env.top_level);
            FStar_TypeChecker_Env.check_uvars =
              (uu___2276_16417.FStar_TypeChecker_Env.check_uvars);
            FStar_TypeChecker_Env.use_eq =
              (uu___2276_16417.FStar_TypeChecker_Env.use_eq);
            FStar_TypeChecker_Env.use_eq_strict =
              (uu___2276_16417.FStar_TypeChecker_Env.use_eq_strict);
            FStar_TypeChecker_Env.is_iface =
              (uu___2276_16417.FStar_TypeChecker_Env.is_iface);
            FStar_TypeChecker_Env.admit =
              (uu___2276_16417.FStar_TypeChecker_Env.admit);
            FStar_TypeChecker_Env.lax =
              (uu___2276_16417.FStar_TypeChecker_Env.lax);
            FStar_TypeChecker_Env.lax_universes =
              (uu___2276_16417.FStar_TypeChecker_Env.lax_universes);
            FStar_TypeChecker_Env.phase1 =
              (uu___2276_16417.FStar_TypeChecker_Env.phase1);
            FStar_TypeChecker_Env.failhard = true;
            FStar_TypeChecker_Env.nosynth =
              (uu___2276_16417.FStar_TypeChecker_Env.nosynth);
            FStar_TypeChecker_Env.uvar_subtyping =
              (uu___2276_16417.FStar_TypeChecker_Env.uvar_subtyping);
            FStar_TypeChecker_Env.tc_term =
              (uu___2276_16417.FStar_TypeChecker_Env.tc_term);
            FStar_TypeChecker_Env.type_of =
              (uu___2276_16417.FStar_TypeChecker_Env.type_of);
            FStar_TypeChecker_Env.universe_of =
              (uu___2276_16417.FStar_TypeChecker_Env.universe_of);
            FStar_TypeChecker_Env.check_type_of =
              (uu___2276_16417.FStar_TypeChecker_Env.check_type_of);
            FStar_TypeChecker_Env.use_bv_sorts =
              (uu___2276_16417.FStar_TypeChecker_Env.use_bv_sorts);
            FStar_TypeChecker_Env.qtbl_name_and_index =
              (uu___2276_16417.FStar_TypeChecker_Env.qtbl_name_and_index);
            FStar_TypeChecker_Env.normalized_eff_names =
              (uu___2276_16417.FStar_TypeChecker_Env.normalized_eff_names);
            FStar_TypeChecker_Env.fv_delta_depths =
              (uu___2276_16417.FStar_TypeChecker_Env.fv_delta_depths);
            FStar_TypeChecker_Env.proof_ns =
              (uu___2276_16417.FStar_TypeChecker_Env.proof_ns);
            FStar_TypeChecker_Env.synth_hook =
              (uu___2276_16417.FStar_TypeChecker_Env.synth_hook);
            FStar_TypeChecker_Env.try_solve_implicits_hook =
              (uu___2276_16417.FStar_TypeChecker_Env.try_solve_implicits_hook);
            FStar_TypeChecker_Env.splice =
              (uu___2276_16417.FStar_TypeChecker_Env.splice);
            FStar_TypeChecker_Env.mpreprocess =
              (uu___2276_16417.FStar_TypeChecker_Env.mpreprocess);
            FStar_TypeChecker_Env.postprocess =
              (uu___2276_16417.FStar_TypeChecker_Env.postprocess);
            FStar_TypeChecker_Env.is_native_tactic =
              (uu___2276_16417.FStar_TypeChecker_Env.is_native_tactic);
            FStar_TypeChecker_Env.identifier_info =
              (uu___2276_16417.FStar_TypeChecker_Env.identifier_info);
            FStar_TypeChecker_Env.tc_hooks =
              (uu___2276_16417.FStar_TypeChecker_Env.tc_hooks);
            FStar_TypeChecker_Env.dsenv =
              (uu___2276_16417.FStar_TypeChecker_Env.dsenv);
            FStar_TypeChecker_Env.nbe =
              (uu___2276_16417.FStar_TypeChecker_Env.nbe);
            FStar_TypeChecker_Env.strict_args_tab =
              (uu___2276_16417.FStar_TypeChecker_Env.strict_args_tab);
            FStar_TypeChecker_Env.erasable_types_tab =
              (uu___2276_16417.FStar_TypeChecker_Env.erasable_types_tab);
            FStar_TypeChecker_Env.enable_defer_to_tac =
              (uu___2276_16417.FStar_TypeChecker_Env.enable_defer_to_tac)
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
            let uu____16450 =
              FStar_TypeChecker_Env.debug env1
                (FStar_Options.Other "TacVerbose")
               in
            let uu____16453 = FStar_Util.psmap_empty ()  in
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
              FStar_Tactics_Types.tac_verb_dbg = uu____16450;
              FStar_Tactics_Types.local_state = uu____16453
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
        let uu____16479 = goal_of_goal_ty env1 typ  in
        match uu____16479 with
        | (g,g_u) ->
            let ps =
              proofstate_of_goals rng env1 [g]
                g_u.FStar_TypeChecker_Common.implicits
               in
            let uu____16491 = FStar_Tactics_Types.goal_witness g  in
            (ps, uu____16491)
  
let (goal_of_implicit :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Env.implicit -> FStar_Tactics_Types.goal)
  =
  fun env  ->
    fun i  ->
      let uu____16503 = FStar_Options.peek ()  in
      FStar_Tactics_Types.mk_goal
        (let uu___2295_16506 = env  in
         {
           FStar_TypeChecker_Env.solver =
             (uu___2295_16506.FStar_TypeChecker_Env.solver);
           FStar_TypeChecker_Env.range =
             (uu___2295_16506.FStar_TypeChecker_Env.range);
           FStar_TypeChecker_Env.curmodule =
             (uu___2295_16506.FStar_TypeChecker_Env.curmodule);
           FStar_TypeChecker_Env.gamma =
             ((i.FStar_TypeChecker_Common.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_gamma);
           FStar_TypeChecker_Env.gamma_sig =
             (uu___2295_16506.FStar_TypeChecker_Env.gamma_sig);
           FStar_TypeChecker_Env.gamma_cache =
             (uu___2295_16506.FStar_TypeChecker_Env.gamma_cache);
           FStar_TypeChecker_Env.modules =
             (uu___2295_16506.FStar_TypeChecker_Env.modules);
           FStar_TypeChecker_Env.expected_typ =
             (uu___2295_16506.FStar_TypeChecker_Env.expected_typ);
           FStar_TypeChecker_Env.sigtab =
             (uu___2295_16506.FStar_TypeChecker_Env.sigtab);
           FStar_TypeChecker_Env.attrtab =
             (uu___2295_16506.FStar_TypeChecker_Env.attrtab);
           FStar_TypeChecker_Env.instantiate_imp =
             (uu___2295_16506.FStar_TypeChecker_Env.instantiate_imp);
           FStar_TypeChecker_Env.effects =
             (uu___2295_16506.FStar_TypeChecker_Env.effects);
           FStar_TypeChecker_Env.generalize =
             (uu___2295_16506.FStar_TypeChecker_Env.generalize);
           FStar_TypeChecker_Env.letrecs =
             (uu___2295_16506.FStar_TypeChecker_Env.letrecs);
           FStar_TypeChecker_Env.top_level =
             (uu___2295_16506.FStar_TypeChecker_Env.top_level);
           FStar_TypeChecker_Env.check_uvars =
             (uu___2295_16506.FStar_TypeChecker_Env.check_uvars);
           FStar_TypeChecker_Env.use_eq =
             (uu___2295_16506.FStar_TypeChecker_Env.use_eq);
           FStar_TypeChecker_Env.use_eq_strict =
             (uu___2295_16506.FStar_TypeChecker_Env.use_eq_strict);
           FStar_TypeChecker_Env.is_iface =
             (uu___2295_16506.FStar_TypeChecker_Env.is_iface);
           FStar_TypeChecker_Env.admit =
             (uu___2295_16506.FStar_TypeChecker_Env.admit);
           FStar_TypeChecker_Env.lax =
             (uu___2295_16506.FStar_TypeChecker_Env.lax);
           FStar_TypeChecker_Env.lax_universes =
             (uu___2295_16506.FStar_TypeChecker_Env.lax_universes);
           FStar_TypeChecker_Env.phase1 =
             (uu___2295_16506.FStar_TypeChecker_Env.phase1);
           FStar_TypeChecker_Env.failhard =
             (uu___2295_16506.FStar_TypeChecker_Env.failhard);
           FStar_TypeChecker_Env.nosynth =
             (uu___2295_16506.FStar_TypeChecker_Env.nosynth);
           FStar_TypeChecker_Env.uvar_subtyping =
             (uu___2295_16506.FStar_TypeChecker_Env.uvar_subtyping);
           FStar_TypeChecker_Env.tc_term =
             (uu___2295_16506.FStar_TypeChecker_Env.tc_term);
           FStar_TypeChecker_Env.type_of =
             (uu___2295_16506.FStar_TypeChecker_Env.type_of);
           FStar_TypeChecker_Env.universe_of =
             (uu___2295_16506.FStar_TypeChecker_Env.universe_of);
           FStar_TypeChecker_Env.check_type_of =
             (uu___2295_16506.FStar_TypeChecker_Env.check_type_of);
           FStar_TypeChecker_Env.use_bv_sorts =
             (uu___2295_16506.FStar_TypeChecker_Env.use_bv_sorts);
           FStar_TypeChecker_Env.qtbl_name_and_index =
             (uu___2295_16506.FStar_TypeChecker_Env.qtbl_name_and_index);
           FStar_TypeChecker_Env.normalized_eff_names =
             (uu___2295_16506.FStar_TypeChecker_Env.normalized_eff_names);
           FStar_TypeChecker_Env.fv_delta_depths =
             (uu___2295_16506.FStar_TypeChecker_Env.fv_delta_depths);
           FStar_TypeChecker_Env.proof_ns =
             (uu___2295_16506.FStar_TypeChecker_Env.proof_ns);
           FStar_TypeChecker_Env.synth_hook =
             (uu___2295_16506.FStar_TypeChecker_Env.synth_hook);
           FStar_TypeChecker_Env.try_solve_implicits_hook =
             (uu___2295_16506.FStar_TypeChecker_Env.try_solve_implicits_hook);
           FStar_TypeChecker_Env.splice =
             (uu___2295_16506.FStar_TypeChecker_Env.splice);
           FStar_TypeChecker_Env.mpreprocess =
             (uu___2295_16506.FStar_TypeChecker_Env.mpreprocess);
           FStar_TypeChecker_Env.postprocess =
             (uu___2295_16506.FStar_TypeChecker_Env.postprocess);
           FStar_TypeChecker_Env.is_native_tactic =
             (uu___2295_16506.FStar_TypeChecker_Env.is_native_tactic);
           FStar_TypeChecker_Env.identifier_info =
             (uu___2295_16506.FStar_TypeChecker_Env.identifier_info);
           FStar_TypeChecker_Env.tc_hooks =
             (uu___2295_16506.FStar_TypeChecker_Env.tc_hooks);
           FStar_TypeChecker_Env.dsenv =
             (uu___2295_16506.FStar_TypeChecker_Env.dsenv);
           FStar_TypeChecker_Env.nbe =
             (uu___2295_16506.FStar_TypeChecker_Env.nbe);
           FStar_TypeChecker_Env.strict_args_tab =
             (uu___2295_16506.FStar_TypeChecker_Env.strict_args_tab);
           FStar_TypeChecker_Env.erasable_types_tab =
             (uu___2295_16506.FStar_TypeChecker_Env.erasable_types_tab);
           FStar_TypeChecker_Env.enable_defer_to_tac =
             (uu___2295_16506.FStar_TypeChecker_Env.enable_defer_to_tac)
         }) i.FStar_TypeChecker_Common.imp_uvar uu____16503 false
        i.FStar_TypeChecker_Common.imp_reason
  
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
          let uu____16532 = FStar_List.hd goals  in
          FStar_Tactics_Types.goal_witness uu____16532  in
        let ps =
          let uu____16534 =
            FStar_TypeChecker_Env.debug env
              (FStar_Options.Other "TacVerbose")
             in
          let uu____16537 = FStar_Util.psmap_empty ()  in
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
            FStar_Tactics_Types.tac_verb_dbg = uu____16534;
            FStar_Tactics_Types.local_state = uu____16537
          }  in
        (ps, w)
  