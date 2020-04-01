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
      let uu____1387 =
        let uu____1389 = FStar_Options.silent ()  in
        Prims.op_Negation uu____1389  in
      if uu____1387
      then
        FStar_Options.with_saved_options
          (fun uu____1395  ->
             FStar_Options.set_option "print_effect_args"
               (FStar_Options.Bool true);
             FStar_Util.print_generic "proof-state" ps_to_string ps_to_json
               (msg, ps);
             FStar_Util.flush_stdout ())
      else ()
  
let (dump : Prims.string -> unit tac) =
  fun msg  ->
    mk_tac
      (fun ps  ->
         let psc = ps.FStar_Tactics_Types.psc  in
         let subst1 = FStar_TypeChecker_Cfg.psc_subst psc  in
         (let uu____1429 = FStar_Tactics_Types.subst_proof_state subst1 ps
             in
          do_dump_proofstate uu____1429 msg);
         FStar_Tactics_Result.Success ((), ps))
  
let mlog : 'a . (unit -> unit) -> (unit -> 'a tac) -> 'a tac =
  fun f  -> fun cont  -> bind get (fun ps  -> log ps f; cont ()) 
let traise : 'a . Prims.exn -> 'a tac =
  fun e  -> mk_tac (fun ps  -> FStar_Tactics_Result.Failed (e, ps)) 
let fail : 'a . Prims.string -> 'a tac =
  fun msg  ->
    mk_tac
      (fun ps  ->
         (let uu____1502 =
            FStar_TypeChecker_Env.debug ps.FStar_Tactics_Types.main_context
              (FStar_Options.Other "TacFail")
             in
          if uu____1502
          then do_dump_proofstate ps (Prims.op_Hat "TACTIC FAILING: " msg)
          else ());
         FStar_Tactics_Result.Failed
           ((FStar_Tactics_Types.TacticFailure msg), ps))
  
let fail1 : 'Auu____1516 . Prims.string -> Prims.string -> 'Auu____1516 tac =
  fun msg  ->
    fun x  -> let uu____1533 = FStar_Util.format1 msg x  in fail uu____1533
  
let fail2 :
  'Auu____1544 .
    Prims.string -> Prims.string -> Prims.string -> 'Auu____1544 tac
  =
  fun msg  ->
    fun x  ->
      fun y  ->
        let uu____1568 = FStar_Util.format2 msg x y  in fail uu____1568
  
let fail3 :
  'Auu____1581 .
    Prims.string ->
      Prims.string -> Prims.string -> Prims.string -> 'Auu____1581 tac
  =
  fun msg  ->
    fun x  ->
      fun y  ->
        fun z  ->
          let uu____1612 = FStar_Util.format3 msg x y z  in fail uu____1612
  
let fail4 :
  'Auu____1627 .
    Prims.string ->
      Prims.string ->
        Prims.string -> Prims.string -> Prims.string -> 'Auu____1627 tac
  =
  fun msg  ->
    fun x  ->
      fun y  ->
        fun z  ->
          fun w  ->
            let uu____1665 = FStar_Util.format4 msg x y z w  in
            fail uu____1665
  
let catch : 'a . 'a tac -> (Prims.exn,'a) FStar_Util.either tac =
  fun t  ->
    mk_tac
      (fun ps  ->
         let tx = FStar_Syntax_Unionfind.new_transaction ()  in
         let uu____1700 = run t ps  in
         match uu____1700 with
         | FStar_Tactics_Result.Success (a,q) ->
             (FStar_Syntax_Unionfind.commit tx;
              FStar_Tactics_Result.Success ((FStar_Util.Inr a), q))
         | FStar_Tactics_Result.Failed (m,q) ->
             (FStar_Syntax_Unionfind.rollback tx;
              (let ps1 =
                 let uu___233_1724 = ps  in
                 {
                   FStar_Tactics_Types.main_context =
                     (uu___233_1724.FStar_Tactics_Types.main_context);
                   FStar_Tactics_Types.all_implicits =
                     (uu___233_1724.FStar_Tactics_Types.all_implicits);
                   FStar_Tactics_Types.goals =
                     (uu___233_1724.FStar_Tactics_Types.goals);
                   FStar_Tactics_Types.smt_goals =
                     (uu___233_1724.FStar_Tactics_Types.smt_goals);
                   FStar_Tactics_Types.depth =
                     (uu___233_1724.FStar_Tactics_Types.depth);
                   FStar_Tactics_Types.__dump =
                     (uu___233_1724.FStar_Tactics_Types.__dump);
                   FStar_Tactics_Types.psc =
                     (uu___233_1724.FStar_Tactics_Types.psc);
                   FStar_Tactics_Types.entry_range =
                     (uu___233_1724.FStar_Tactics_Types.entry_range);
                   FStar_Tactics_Types.guard_policy =
                     (uu___233_1724.FStar_Tactics_Types.guard_policy);
                   FStar_Tactics_Types.freshness =
                     (q.FStar_Tactics_Types.freshness);
                   FStar_Tactics_Types.tac_verb_dbg =
                     (uu___233_1724.FStar_Tactics_Types.tac_verb_dbg);
                   FStar_Tactics_Types.local_state =
                     (uu___233_1724.FStar_Tactics_Types.local_state)
                 }  in
               FStar_Tactics_Result.Success ((FStar_Util.Inl m), ps1))))
  
let recover : 'a . 'a tac -> (Prims.exn,'a) FStar_Util.either tac =
  fun t  ->
    mk_tac
      (fun ps  ->
         let uu____1763 = run t ps  in
         match uu____1763 with
         | FStar_Tactics_Result.Success (a,q) ->
             FStar_Tactics_Result.Success ((FStar_Util.Inr a), q)
         | FStar_Tactics_Result.Failed (m,q) ->
             FStar_Tactics_Result.Success ((FStar_Util.Inl m), q))
  
let trytac : 'a . 'a tac -> 'a FStar_Pervasives_Native.option tac =
  fun t  ->
    let uu____1811 = catch t  in
    bind uu____1811
      (fun r  ->
         match r with
         | FStar_Util.Inr v1 -> ret (FStar_Pervasives_Native.Some v1)
         | FStar_Util.Inl uu____1838 -> ret FStar_Pervasives_Native.None)
  
let trytac_exn : 'a . 'a tac -> 'a FStar_Pervasives_Native.option tac =
  fun t  ->
    mk_tac
      (fun ps  ->
         try
           (fun uu___259_1870  ->
              match () with
              | () -> let uu____1875 = trytac t  in run uu____1875 ps) ()
         with
         | FStar_Errors.Err (uu____1891,msg) ->
             (log ps
                (fun uu____1897  ->
                   FStar_Util.print1 "trytac_exn error: (%s)" msg);
              FStar_Tactics_Result.Success (FStar_Pervasives_Native.None, ps))
         | FStar_Errors.Error (uu____1903,msg,uu____1905) ->
             (log ps
                (fun uu____1910  ->
                   FStar_Util.print1 "trytac_exn error: (%s)" msg);
              FStar_Tactics_Result.Success (FStar_Pervasives_Native.None, ps)))
  
let wrap_err : 'a . Prims.string -> 'a tac -> 'a tac =
  fun pref  ->
    fun t  ->
      mk_tac
        (fun ps  ->
           let uu____1947 = run t ps  in
           match uu____1947 with
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
  fun p  -> mk_tac (fun uu____1971  -> FStar_Tactics_Result.Success ((), p)) 
let (add_implicits : implicits -> unit tac) =
  fun i  ->
    bind get
      (fun p  ->
         set
           (let uu___294_1986 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___294_1986.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.all_implicits =
                (FStar_List.append i p.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___294_1986.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (uu___294_1986.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___294_1986.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___294_1986.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___294_1986.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___294_1986.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___294_1986.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___294_1986.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___294_1986.FStar_Tactics_Types.tac_verb_dbg);
              FStar_Tactics_Types.local_state =
                (uu___294_1986.FStar_Tactics_Types.local_state)
            }))
  
let (__do_unify :
  env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.bool tac)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        (let uu____2010 =
           FStar_TypeChecker_Env.debug env (FStar_Options.Other "1346")  in
         if uu____2010
         then
           let uu____2014 = FStar_Syntax_Print.term_to_string t1  in
           let uu____2016 = FStar_Syntax_Print.term_to_string t2  in
           FStar_Util.print2 "%%%%%%%%do_unify %s =? %s\n" uu____2014
             uu____2016
         else ());
        (try
           (fun uu___302_2027  ->
              match () with
              | () ->
                  let res = FStar_TypeChecker_Rel.teq_nosmt env t1 t2  in
                  ((let uu____2035 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "1346")
                       in
                    if uu____2035
                    then
                      let uu____2039 =
                        FStar_Common.string_of_option
                          (FStar_TypeChecker_Rel.guard_to_string env) res
                         in
                      let uu____2041 = FStar_Syntax_Print.term_to_string t1
                         in
                      let uu____2043 = FStar_Syntax_Print.term_to_string t2
                         in
                      FStar_Util.print3
                        "%%%%%%%%do_unify (RESULT %s) %s =? %s\n" uu____2039
                        uu____2041 uu____2043
                    else ());
                   (match res with
                    | FStar_Pervasives_Native.None  -> ret false
                    | FStar_Pervasives_Native.Some g ->
                        let uu____2054 =
                          add_implicits g.FStar_TypeChecker_Common.implicits
                           in
                        bind uu____2054 (fun uu____2059  -> ret true)))) ()
         with
         | FStar_Errors.Err (uu____2069,msg) ->
             mlog
               (fun uu____2075  ->
                  FStar_Util.print1 ">> do_unify error, (%s)\n" msg)
               (fun uu____2078  -> ret false)
         | FStar_Errors.Error (uu____2081,msg,r) ->
             mlog
               (fun uu____2089  ->
                  let uu____2090 = FStar_Range.string_of_range r  in
                  FStar_Util.print2 ">> do_unify error, (%s) at (%s)\n" msg
                    uu____2090) (fun uu____2094  -> ret false))
  
let (compress_implicits : unit tac) =
  bind get
    (fun ps  ->
       let imps = ps.FStar_Tactics_Types.all_implicits  in
       let g =
         let uu___328_2108 = FStar_TypeChecker_Env.trivial_guard  in
         {
           FStar_TypeChecker_Common.guard_f =
             (uu___328_2108.FStar_TypeChecker_Common.guard_f);
           FStar_TypeChecker_Common.deferred =
             (uu___328_2108.FStar_TypeChecker_Common.deferred);
           FStar_TypeChecker_Common.univ_ineqs =
             (uu___328_2108.FStar_TypeChecker_Common.univ_ineqs);
           FStar_TypeChecker_Common.implicits = imps
         }  in
       let g1 =
         FStar_TypeChecker_Rel.resolve_implicits_tac
           ps.FStar_Tactics_Types.main_context g
          in
       let ps' =
         let uu___332_2111 = ps  in
         {
           FStar_Tactics_Types.main_context =
             (uu___332_2111.FStar_Tactics_Types.main_context);
           FStar_Tactics_Types.all_implicits =
             (g1.FStar_TypeChecker_Common.implicits);
           FStar_Tactics_Types.goals =
             (uu___332_2111.FStar_Tactics_Types.goals);
           FStar_Tactics_Types.smt_goals =
             (uu___332_2111.FStar_Tactics_Types.smt_goals);
           FStar_Tactics_Types.depth =
             (uu___332_2111.FStar_Tactics_Types.depth);
           FStar_Tactics_Types.__dump =
             (uu___332_2111.FStar_Tactics_Types.__dump);
           FStar_Tactics_Types.psc = (uu___332_2111.FStar_Tactics_Types.psc);
           FStar_Tactics_Types.entry_range =
             (uu___332_2111.FStar_Tactics_Types.entry_range);
           FStar_Tactics_Types.guard_policy =
             (uu___332_2111.FStar_Tactics_Types.guard_policy);
           FStar_Tactics_Types.freshness =
             (uu___332_2111.FStar_Tactics_Types.freshness);
           FStar_Tactics_Types.tac_verb_dbg =
             (uu___332_2111.FStar_Tactics_Types.tac_verb_dbg);
           FStar_Tactics_Types.local_state =
             (uu___332_2111.FStar_Tactics_Types.local_state)
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
          (fun uu____2138  ->
             (let uu____2140 =
                FStar_TypeChecker_Env.debug env (FStar_Options.Other "1346")
                 in
              if uu____2140
              then
                (FStar_Options.push ();
                 (let uu____2145 =
                    FStar_Options.set_options
                      "--debug_level Rel --debug_level RelCheck"
                     in
                  ()))
              else ());
             (let uu____2149 = __do_unify env t1 t2  in
              bind uu____2149
                (fun r  ->
                   (let uu____2160 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "1346")
                       in
                    if uu____2160 then FStar_Options.pop () else ());
                   ret r)))
  
let (do_match :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.bool tac)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uvs1 = FStar_Syntax_Free.uvars_uncached t1  in
        let uu____2192 = do_unify env t1 t2  in
        bind uu____2192
          (fun r  ->
             if r
             then
               let uvs2 = FStar_Syntax_Free.uvars_uncached t1  in
               let uu____2210 =
                 let uu____2212 = FStar_Util.set_eq uvs1 uvs2  in
                 Prims.op_Negation uu____2212  in
               (if uu____2210 then ret false else ret true)
             else ret false)
  
let (remove_solved_goals : unit tac) =
  bind get
    (fun ps  ->
       let ps' =
         let uu___355_2235 = ps  in
         let uu____2236 =
           FStar_List.filter
             (fun g  ->
                let uu____2242 = check_goal_solved g  in
                FStar_Option.isNone uu____2242) ps.FStar_Tactics_Types.goals
            in
         {
           FStar_Tactics_Types.main_context =
             (uu___355_2235.FStar_Tactics_Types.main_context);
           FStar_Tactics_Types.all_implicits =
             (uu___355_2235.FStar_Tactics_Types.all_implicits);
           FStar_Tactics_Types.goals = uu____2236;
           FStar_Tactics_Types.smt_goals =
             (uu___355_2235.FStar_Tactics_Types.smt_goals);
           FStar_Tactics_Types.depth =
             (uu___355_2235.FStar_Tactics_Types.depth);
           FStar_Tactics_Types.__dump =
             (uu___355_2235.FStar_Tactics_Types.__dump);
           FStar_Tactics_Types.psc = (uu___355_2235.FStar_Tactics_Types.psc);
           FStar_Tactics_Types.entry_range =
             (uu___355_2235.FStar_Tactics_Types.entry_range);
           FStar_Tactics_Types.guard_policy =
             (uu___355_2235.FStar_Tactics_Types.guard_policy);
           FStar_Tactics_Types.freshness =
             (uu___355_2235.FStar_Tactics_Types.freshness);
           FStar_Tactics_Types.tac_verb_dbg =
             (uu___355_2235.FStar_Tactics_Types.tac_verb_dbg);
           FStar_Tactics_Types.local_state =
             (uu___355_2235.FStar_Tactics_Types.local_state)
         }  in
       set ps')
  
let (set_solution :
  FStar_Tactics_Types.goal -> FStar_Syntax_Syntax.term -> unit tac) =
  fun goal  ->
    fun solution  ->
      let uu____2260 =
        FStar_Syntax_Unionfind.find
          (goal.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_head
         in
      match uu____2260 with
      | FStar_Pervasives_Native.Some uu____2265 ->
          let uu____2266 =
            let uu____2268 = goal_to_string_verbose goal  in
            FStar_Util.format1 "Goal %s is already solved" uu____2268  in
          fail uu____2266
      | FStar_Pervasives_Native.None  ->
          (FStar_Syntax_Unionfind.change
             (goal.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_head
             solution;
           ret ())
  
let (trysolve :
  FStar_Tactics_Types.goal -> FStar_Syntax_Syntax.term -> Prims.bool tac) =
  fun goal  ->
    fun solution  ->
      let uu____2289 = FStar_Tactics_Types.goal_env goal  in
      let uu____2290 = FStar_Tactics_Types.goal_witness goal  in
      do_unify uu____2289 solution uu____2290
  
let (__dismiss : unit tac) =
  bind get
    (fun p  ->
       let uu____2297 =
         let uu___368_2298 = p  in
         let uu____2299 = FStar_List.tl p.FStar_Tactics_Types.goals  in
         {
           FStar_Tactics_Types.main_context =
             (uu___368_2298.FStar_Tactics_Types.main_context);
           FStar_Tactics_Types.all_implicits =
             (uu___368_2298.FStar_Tactics_Types.all_implicits);
           FStar_Tactics_Types.goals = uu____2299;
           FStar_Tactics_Types.smt_goals =
             (uu___368_2298.FStar_Tactics_Types.smt_goals);
           FStar_Tactics_Types.depth =
             (uu___368_2298.FStar_Tactics_Types.depth);
           FStar_Tactics_Types.__dump =
             (uu___368_2298.FStar_Tactics_Types.__dump);
           FStar_Tactics_Types.psc = (uu___368_2298.FStar_Tactics_Types.psc);
           FStar_Tactics_Types.entry_range =
             (uu___368_2298.FStar_Tactics_Types.entry_range);
           FStar_Tactics_Types.guard_policy =
             (uu___368_2298.FStar_Tactics_Types.guard_policy);
           FStar_Tactics_Types.freshness =
             (uu___368_2298.FStar_Tactics_Types.freshness);
           FStar_Tactics_Types.tac_verb_dbg =
             (uu___368_2298.FStar_Tactics_Types.tac_verb_dbg);
           FStar_Tactics_Types.local_state =
             (uu___368_2298.FStar_Tactics_Types.local_state)
         }  in
       set uu____2297)
  
let (solve :
  FStar_Tactics_Types.goal -> FStar_Syntax_Syntax.term -> unit tac) =
  fun goal  ->
    fun solution  ->
      let e = FStar_Tactics_Types.goal_env goal  in
      mlog
        (fun uu____2321  ->
           let uu____2322 =
             let uu____2324 = FStar_Tactics_Types.goal_witness goal  in
             FStar_Syntax_Print.term_to_string uu____2324  in
           let uu____2325 = FStar_Syntax_Print.term_to_string solution  in
           FStar_Util.print2 "solve %s := %s\n" uu____2322 uu____2325)
        (fun uu____2330  ->
           let uu____2331 = trysolve goal solution  in
           bind uu____2331
             (fun b  ->
                if b
                then bind __dismiss (fun uu____2343  -> remove_solved_goals)
                else
                  (let uu____2346 =
                     let uu____2348 =
                       let uu____2350 = FStar_Tactics_Types.goal_env goal  in
                       tts uu____2350 solution  in
                     let uu____2351 =
                       let uu____2353 = FStar_Tactics_Types.goal_env goal  in
                       let uu____2354 = FStar_Tactics_Types.goal_witness goal
                          in
                       tts uu____2353 uu____2354  in
                     let uu____2355 =
                       let uu____2357 = FStar_Tactics_Types.goal_env goal  in
                       let uu____2358 = FStar_Tactics_Types.goal_type goal
                          in
                       tts uu____2357 uu____2358  in
                     FStar_Util.format3 "%s does not solve %s : %s"
                       uu____2348 uu____2351 uu____2355
                      in
                   fail uu____2346)))
  
let (solve' :
  FStar_Tactics_Types.goal -> FStar_Syntax_Syntax.term -> unit tac) =
  fun goal  ->
    fun solution  ->
      let uu____2375 = set_solution goal solution  in
      bind uu____2375
        (fun uu____2379  ->
           bind __dismiss (fun uu____2381  -> remove_solved_goals))
  
let (set_goals : FStar_Tactics_Types.goal Prims.list -> unit tac) =
  fun gs  ->
    bind get
      (fun ps  ->
         set
           (let uu___384_2400 = ps  in
            {
              FStar_Tactics_Types.main_context =
                (uu___384_2400.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.all_implicits =
                (uu___384_2400.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals = gs;
              FStar_Tactics_Types.smt_goals =
                (uu___384_2400.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___384_2400.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___384_2400.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___384_2400.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___384_2400.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___384_2400.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___384_2400.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___384_2400.FStar_Tactics_Types.tac_verb_dbg);
              FStar_Tactics_Types.local_state =
                (uu___384_2400.FStar_Tactics_Types.local_state)
            }))
  
let (set_smt_goals : FStar_Tactics_Types.goal Prims.list -> unit tac) =
  fun gs  ->
    bind get
      (fun ps  ->
         set
           (let uu___388_2419 = ps  in
            {
              FStar_Tactics_Types.main_context =
                (uu___388_2419.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.all_implicits =
                (uu___388_2419.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___388_2419.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals = gs;
              FStar_Tactics_Types.depth =
                (uu___388_2419.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___388_2419.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___388_2419.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___388_2419.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___388_2419.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___388_2419.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___388_2419.FStar_Tactics_Types.tac_verb_dbg);
              FStar_Tactics_Types.local_state =
                (uu___388_2419.FStar_Tactics_Types.local_state)
            }))
  
let (dismiss_all : unit tac) = set_goals [] 
let (nwarn : Prims.int FStar_ST.ref) = FStar_Util.mk_ref Prims.int_zero 
let (check_valid_goal : FStar_Tactics_Types.goal -> unit) =
  fun g  ->
    let uu____2435 = FStar_Options.defensive ()  in
    if uu____2435
    then
      let b = true  in
      let env = FStar_Tactics_Types.goal_env g  in
      let b1 =
        b &&
          (let uu____2445 = FStar_Tactics_Types.goal_witness g  in
           FStar_TypeChecker_Env.closed env uu____2445)
         in
      let b2 =
        b1 &&
          (let uu____2449 = FStar_Tactics_Types.goal_type g  in
           FStar_TypeChecker_Env.closed env uu____2449)
         in
      let rec aux b3 e =
        let uu____2464 = FStar_TypeChecker_Env.pop_bv e  in
        match uu____2464 with
        | FStar_Pervasives_Native.None  -> b3
        | FStar_Pervasives_Native.Some (bv,e1) ->
            let b4 =
              b3 &&
                (FStar_TypeChecker_Env.closed e1 bv.FStar_Syntax_Syntax.sort)
               in
            aux b4 e1
         in
      let uu____2484 =
        (let uu____2488 = aux b2 env  in Prims.op_Negation uu____2488) &&
          (let uu____2491 = FStar_ST.op_Bang nwarn  in
           uu____2491 < (Prims.of_int (5)))
         in
      (if uu____2484
       then
         ((let uu____2517 =
             let uu____2518 = FStar_Tactics_Types.goal_type g  in
             uu____2518.FStar_Syntax_Syntax.pos  in
           let uu____2521 =
             let uu____2527 =
               let uu____2529 = goal_to_string_verbose g  in
               FStar_Util.format1
                 "The following goal is ill-formed. Keeping calm and carrying on...\n<%s>\n\n"
                 uu____2529
                in
             (FStar_Errors.Warning_IllFormedGoal, uu____2527)  in
           FStar_Errors.log_issue uu____2517 uu____2521);
          (let uu____2533 =
             let uu____2535 = FStar_ST.op_Bang nwarn  in
             uu____2535 + Prims.int_one  in
           FStar_ST.op_Colon_Equals nwarn uu____2533))
       else ())
    else ()
  
let (add_goals : FStar_Tactics_Types.goal Prims.list -> unit tac) =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___410_2604 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___410_2604.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.all_implicits =
                (uu___410_2604.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (FStar_List.append gs p.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (uu___410_2604.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___410_2604.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___410_2604.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___410_2604.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___410_2604.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___410_2604.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___410_2604.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___410_2604.FStar_Tactics_Types.tac_verb_dbg);
              FStar_Tactics_Types.local_state =
                (uu___410_2604.FStar_Tactics_Types.local_state)
            }))
  
let (add_smt_goals : FStar_Tactics_Types.goal Prims.list -> unit tac) =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___415_2625 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___415_2625.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.all_implicits =
                (uu___415_2625.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___415_2625.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (FStar_List.append gs p.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___415_2625.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___415_2625.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___415_2625.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___415_2625.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___415_2625.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___415_2625.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___415_2625.FStar_Tactics_Types.tac_verb_dbg);
              FStar_Tactics_Types.local_state =
                (uu___415_2625.FStar_Tactics_Types.local_state)
            }))
  
let (push_goals : FStar_Tactics_Types.goal Prims.list -> unit tac) =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___420_2646 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___420_2646.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.all_implicits =
                (uu___420_2646.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (FStar_List.append p.FStar_Tactics_Types.goals gs);
              FStar_Tactics_Types.smt_goals =
                (uu___420_2646.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___420_2646.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___420_2646.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___420_2646.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___420_2646.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___420_2646.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___420_2646.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___420_2646.FStar_Tactics_Types.tac_verb_dbg);
              FStar_Tactics_Types.local_state =
                (uu___420_2646.FStar_Tactics_Types.local_state)
            }))
  
let (push_smt_goals : FStar_Tactics_Types.goal Prims.list -> unit tac) =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___425_2667 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___425_2667.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.all_implicits =
                (uu___425_2667.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___425_2667.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (FStar_List.append p.FStar_Tactics_Types.smt_goals gs);
              FStar_Tactics_Types.depth =
                (uu___425_2667.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___425_2667.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___425_2667.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___425_2667.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___425_2667.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___425_2667.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___425_2667.FStar_Tactics_Types.tac_verb_dbg);
              FStar_Tactics_Types.local_state =
                (uu___425_2667.FStar_Tactics_Types.local_state)
            }))
  
let (replace_cur : FStar_Tactics_Types.goal -> unit tac) =
  fun g  -> bind __dismiss (fun uu____2679  -> add_goals [g]) 
let (new_uvar :
  Prims.string ->
    env ->
      FStar_Reflection_Data.typ ->
        (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.ctx_uvar) tac)
  =
  fun reason  ->
    fun env  ->
      fun typ  ->
        let uu____2710 =
          FStar_TypeChecker_Env.new_implicit_var_aux reason
            typ.FStar_Syntax_Syntax.pos env typ
            FStar_Syntax_Syntax.Allow_untyped FStar_Pervasives_Native.None
           in
        match uu____2710 with
        | (u,ctx_uvar,g_u) ->
            let uu____2748 =
              add_implicits g_u.FStar_TypeChecker_Common.implicits  in
            bind uu____2748
              (fun uu____2757  ->
                 let uu____2758 =
                   let uu____2763 =
                     let uu____2764 = FStar_List.hd ctx_uvar  in
                     FStar_Pervasives_Native.fst uu____2764  in
                   (u, uu____2763)  in
                 ret uu____2758)
  
let (is_true : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____2785 = FStar_Syntax_Util.un_squash t1  in
    match uu____2785 with
    | FStar_Pervasives_Native.Some t' ->
        let t'1 = FStar_Syntax_Util.unascribe t'  in
        let uu____2797 =
          let uu____2798 = FStar_Syntax_Subst.compress t'1  in
          uu____2798.FStar_Syntax_Syntax.n  in
        (match uu____2797 with
         | FStar_Syntax_Syntax.Tm_fvar fv ->
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.true_lid
         | uu____2803 -> false)
    | uu____2805 -> false
  
let (is_false : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____2818 = FStar_Syntax_Util.un_squash t  in
    match uu____2818 with
    | FStar_Pervasives_Native.Some t' ->
        let uu____2829 =
          let uu____2830 = FStar_Syntax_Subst.compress t'  in
          uu____2830.FStar_Syntax_Syntax.n  in
        (match uu____2829 with
         | FStar_Syntax_Syntax.Tm_fvar fv ->
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.false_lid
         | uu____2835 -> false)
    | uu____2837 -> false
  
let (cur_goal : unit -> FStar_Tactics_Types.goal tac) =
  fun uu____2850  ->
    bind get
      (fun p  ->
         match p.FStar_Tactics_Types.goals with
         | [] -> fail "No more goals (1)"
         | hd1::tl1 ->
             let uu____2862 =
               FStar_Syntax_Unionfind.find
                 (hd1.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_head
                in
             (match uu____2862 with
              | FStar_Pervasives_Native.None  -> ret hd1
              | FStar_Pervasives_Native.Some t ->
                  ((let uu____2869 = goal_to_string_verbose hd1  in
                    let uu____2871 = FStar_Syntax_Print.term_to_string t  in
                    FStar_Util.print2
                      "!!!!!!!!!!!! GOAL IS ALREADY SOLVED! %s\nsol is %s\n"
                      uu____2869 uu____2871);
                   ret hd1)))
  
let (tadmit_t : FStar_Syntax_Syntax.term -> unit tac) =
  fun t  ->
    let uu____2884 =
      bind get
        (fun ps  ->
           let uu____2890 = cur_goal ()  in
           bind uu____2890
             (fun g  ->
                (let uu____2897 =
                   let uu____2898 = FStar_Tactics_Types.goal_type g  in
                   uu____2898.FStar_Syntax_Syntax.pos  in
                 let uu____2901 =
                   let uu____2907 =
                     let uu____2909 =
                       goal_to_string "" FStar_Pervasives_Native.None ps g
                        in
                     FStar_Util.format1 "Tactics admitted goal <%s>\n\n"
                       uu____2909
                      in
                   (FStar_Errors.Warning_TacAdmit, uu____2907)  in
                 FStar_Errors.log_issue uu____2897 uu____2901);
                solve' g t))
       in
    FStar_All.pipe_left (wrap_err "tadmit_t") uu____2884
  
let (fresh : unit -> FStar_BigInt.t tac) =
  fun uu____2932  ->
    bind get
      (fun ps  ->
         let n1 = ps.FStar_Tactics_Types.freshness  in
         let ps1 =
           let uu___470_2943 = ps  in
           {
             FStar_Tactics_Types.main_context =
               (uu___470_2943.FStar_Tactics_Types.main_context);
             FStar_Tactics_Types.all_implicits =
               (uu___470_2943.FStar_Tactics_Types.all_implicits);
             FStar_Tactics_Types.goals =
               (uu___470_2943.FStar_Tactics_Types.goals);
             FStar_Tactics_Types.smt_goals =
               (uu___470_2943.FStar_Tactics_Types.smt_goals);
             FStar_Tactics_Types.depth =
               (uu___470_2943.FStar_Tactics_Types.depth);
             FStar_Tactics_Types.__dump =
               (uu___470_2943.FStar_Tactics_Types.__dump);
             FStar_Tactics_Types.psc =
               (uu___470_2943.FStar_Tactics_Types.psc);
             FStar_Tactics_Types.entry_range =
               (uu___470_2943.FStar_Tactics_Types.entry_range);
             FStar_Tactics_Types.guard_policy =
               (uu___470_2943.FStar_Tactics_Types.guard_policy);
             FStar_Tactics_Types.freshness = (n1 + Prims.int_one);
             FStar_Tactics_Types.tac_verb_dbg =
               (uu___470_2943.FStar_Tactics_Types.tac_verb_dbg);
             FStar_Tactics_Types.local_state =
               (uu___470_2943.FStar_Tactics_Types.local_state)
           }  in
         let uu____2945 = set ps1  in
         bind uu____2945
           (fun uu____2950  ->
              let uu____2951 = FStar_BigInt.of_int_fs n1  in ret uu____2951))
  
let (curms : unit -> FStar_BigInt.t tac) =
  fun uu____2959  ->
    let uu____2962 =
      let uu____2963 = FStar_Util.now_ms ()  in
      FStar_All.pipe_right uu____2963 FStar_BigInt.of_int_fs  in
    ret uu____2962
  
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
              let uu____3003 = env.FStar_TypeChecker_Env.universe_of env phi
                 in
              FStar_Syntax_Util.mk_squash uu____3003 phi  in
            let uu____3004 = new_uvar reason env typ  in
            bind uu____3004
              (fun uu____3019  ->
                 match uu____3019 with
                 | (uu____3026,ctx_uvar) ->
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
             (fun uu____3073  ->
                let uu____3074 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.print1 "Tac> __tc(%s)\n" uu____3074)
             (fun uu____3079  ->
                let e1 =
                  let uu___489_3081 = e  in
                  {
                    FStar_TypeChecker_Env.solver =
                      (uu___489_3081.FStar_TypeChecker_Env.solver);
                    FStar_TypeChecker_Env.range =
                      (uu___489_3081.FStar_TypeChecker_Env.range);
                    FStar_TypeChecker_Env.curmodule =
                      (uu___489_3081.FStar_TypeChecker_Env.curmodule);
                    FStar_TypeChecker_Env.gamma =
                      (uu___489_3081.FStar_TypeChecker_Env.gamma);
                    FStar_TypeChecker_Env.gamma_sig =
                      (uu___489_3081.FStar_TypeChecker_Env.gamma_sig);
                    FStar_TypeChecker_Env.gamma_cache =
                      (uu___489_3081.FStar_TypeChecker_Env.gamma_cache);
                    FStar_TypeChecker_Env.modules =
                      (uu___489_3081.FStar_TypeChecker_Env.modules);
                    FStar_TypeChecker_Env.expected_typ =
                      (uu___489_3081.FStar_TypeChecker_Env.expected_typ);
                    FStar_TypeChecker_Env.sigtab =
                      (uu___489_3081.FStar_TypeChecker_Env.sigtab);
                    FStar_TypeChecker_Env.attrtab =
                      (uu___489_3081.FStar_TypeChecker_Env.attrtab);
                    FStar_TypeChecker_Env.instantiate_imp =
                      (uu___489_3081.FStar_TypeChecker_Env.instantiate_imp);
                    FStar_TypeChecker_Env.effects =
                      (uu___489_3081.FStar_TypeChecker_Env.effects);
                    FStar_TypeChecker_Env.generalize =
                      (uu___489_3081.FStar_TypeChecker_Env.generalize);
                    FStar_TypeChecker_Env.letrecs =
                      (uu___489_3081.FStar_TypeChecker_Env.letrecs);
                    FStar_TypeChecker_Env.top_level =
                      (uu___489_3081.FStar_TypeChecker_Env.top_level);
                    FStar_TypeChecker_Env.check_uvars =
                      (uu___489_3081.FStar_TypeChecker_Env.check_uvars);
                    FStar_TypeChecker_Env.use_eq =
                      (uu___489_3081.FStar_TypeChecker_Env.use_eq);
                    FStar_TypeChecker_Env.use_eq_strict =
                      (uu___489_3081.FStar_TypeChecker_Env.use_eq_strict);
                    FStar_TypeChecker_Env.is_iface =
                      (uu___489_3081.FStar_TypeChecker_Env.is_iface);
                    FStar_TypeChecker_Env.admit =
                      (uu___489_3081.FStar_TypeChecker_Env.admit);
                    FStar_TypeChecker_Env.lax =
                      (uu___489_3081.FStar_TypeChecker_Env.lax);
                    FStar_TypeChecker_Env.lax_universes =
                      (uu___489_3081.FStar_TypeChecker_Env.lax_universes);
                    FStar_TypeChecker_Env.phase1 =
                      (uu___489_3081.FStar_TypeChecker_Env.phase1);
                    FStar_TypeChecker_Env.failhard =
                      (uu___489_3081.FStar_TypeChecker_Env.failhard);
                    FStar_TypeChecker_Env.nosynth =
                      (uu___489_3081.FStar_TypeChecker_Env.nosynth);
                    FStar_TypeChecker_Env.uvar_subtyping = false;
                    FStar_TypeChecker_Env.tc_term =
                      (uu___489_3081.FStar_TypeChecker_Env.tc_term);
                    FStar_TypeChecker_Env.type_of =
                      (uu___489_3081.FStar_TypeChecker_Env.type_of);
                    FStar_TypeChecker_Env.universe_of =
                      (uu___489_3081.FStar_TypeChecker_Env.universe_of);
                    FStar_TypeChecker_Env.check_type_of =
                      (uu___489_3081.FStar_TypeChecker_Env.check_type_of);
                    FStar_TypeChecker_Env.use_bv_sorts =
                      (uu___489_3081.FStar_TypeChecker_Env.use_bv_sorts);
                    FStar_TypeChecker_Env.qtbl_name_and_index =
                      (uu___489_3081.FStar_TypeChecker_Env.qtbl_name_and_index);
                    FStar_TypeChecker_Env.normalized_eff_names =
                      (uu___489_3081.FStar_TypeChecker_Env.normalized_eff_names);
                    FStar_TypeChecker_Env.fv_delta_depths =
                      (uu___489_3081.FStar_TypeChecker_Env.fv_delta_depths);
                    FStar_TypeChecker_Env.proof_ns =
                      (uu___489_3081.FStar_TypeChecker_Env.proof_ns);
                    FStar_TypeChecker_Env.synth_hook =
                      (uu___489_3081.FStar_TypeChecker_Env.synth_hook);
                    FStar_TypeChecker_Env.try_solve_implicits_hook =
                      (uu___489_3081.FStar_TypeChecker_Env.try_solve_implicits_hook);
                    FStar_TypeChecker_Env.splice =
                      (uu___489_3081.FStar_TypeChecker_Env.splice);
                    FStar_TypeChecker_Env.mpreprocess =
                      (uu___489_3081.FStar_TypeChecker_Env.mpreprocess);
                    FStar_TypeChecker_Env.postprocess =
                      (uu___489_3081.FStar_TypeChecker_Env.postprocess);
                    FStar_TypeChecker_Env.is_native_tactic =
                      (uu___489_3081.FStar_TypeChecker_Env.is_native_tactic);
                    FStar_TypeChecker_Env.identifier_info =
                      (uu___489_3081.FStar_TypeChecker_Env.identifier_info);
                    FStar_TypeChecker_Env.tc_hooks =
                      (uu___489_3081.FStar_TypeChecker_Env.tc_hooks);
                    FStar_TypeChecker_Env.dsenv =
                      (uu___489_3081.FStar_TypeChecker_Env.dsenv);
                    FStar_TypeChecker_Env.nbe =
                      (uu___489_3081.FStar_TypeChecker_Env.nbe);
                    FStar_TypeChecker_Env.strict_args_tab =
                      (uu___489_3081.FStar_TypeChecker_Env.strict_args_tab);
                    FStar_TypeChecker_Env.erasable_types_tab =
                      (uu___489_3081.FStar_TypeChecker_Env.erasable_types_tab)
                  }  in
                try
                  (fun uu___493_3093  ->
                     match () with
                     | () ->
                         let uu____3102 =
                           FStar_TypeChecker_TcTerm.type_of_tot_term e1 t  in
                         ret uu____3102) ()
                with
                | FStar_Errors.Err (uu____3129,msg) ->
                    let uu____3133 = tts e1 t  in
                    let uu____3135 =
                      let uu____3137 = FStar_TypeChecker_Env.all_binders e1
                         in
                      FStar_All.pipe_right uu____3137
                        (FStar_Syntax_Print.binders_to_string ", ")
                       in
                    fail3 "Cannot type %s in context (%s). Error = (%s)"
                      uu____3133 uu____3135 msg
                | FStar_Errors.Error (uu____3147,msg,uu____3149) ->
                    let uu____3152 = tts e1 t  in
                    let uu____3154 =
                      let uu____3156 = FStar_TypeChecker_Env.all_binders e1
                         in
                      FStar_All.pipe_right uu____3156
                        (FStar_Syntax_Print.binders_to_string ", ")
                       in
                    fail3 "Cannot type %s in context (%s). Error = (%s)"
                      uu____3152 uu____3154 msg))
  
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
             (fun uu____3209  ->
                let uu____3210 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.print1 "Tac> __tc_ghost(%s)\n" uu____3210)
             (fun uu____3215  ->
                let e1 =
                  let uu___510_3217 = e  in
                  {
                    FStar_TypeChecker_Env.solver =
                      (uu___510_3217.FStar_TypeChecker_Env.solver);
                    FStar_TypeChecker_Env.range =
                      (uu___510_3217.FStar_TypeChecker_Env.range);
                    FStar_TypeChecker_Env.curmodule =
                      (uu___510_3217.FStar_TypeChecker_Env.curmodule);
                    FStar_TypeChecker_Env.gamma =
                      (uu___510_3217.FStar_TypeChecker_Env.gamma);
                    FStar_TypeChecker_Env.gamma_sig =
                      (uu___510_3217.FStar_TypeChecker_Env.gamma_sig);
                    FStar_TypeChecker_Env.gamma_cache =
                      (uu___510_3217.FStar_TypeChecker_Env.gamma_cache);
                    FStar_TypeChecker_Env.modules =
                      (uu___510_3217.FStar_TypeChecker_Env.modules);
                    FStar_TypeChecker_Env.expected_typ =
                      (uu___510_3217.FStar_TypeChecker_Env.expected_typ);
                    FStar_TypeChecker_Env.sigtab =
                      (uu___510_3217.FStar_TypeChecker_Env.sigtab);
                    FStar_TypeChecker_Env.attrtab =
                      (uu___510_3217.FStar_TypeChecker_Env.attrtab);
                    FStar_TypeChecker_Env.instantiate_imp =
                      (uu___510_3217.FStar_TypeChecker_Env.instantiate_imp);
                    FStar_TypeChecker_Env.effects =
                      (uu___510_3217.FStar_TypeChecker_Env.effects);
                    FStar_TypeChecker_Env.generalize =
                      (uu___510_3217.FStar_TypeChecker_Env.generalize);
                    FStar_TypeChecker_Env.letrecs =
                      (uu___510_3217.FStar_TypeChecker_Env.letrecs);
                    FStar_TypeChecker_Env.top_level =
                      (uu___510_3217.FStar_TypeChecker_Env.top_level);
                    FStar_TypeChecker_Env.check_uvars =
                      (uu___510_3217.FStar_TypeChecker_Env.check_uvars);
                    FStar_TypeChecker_Env.use_eq =
                      (uu___510_3217.FStar_TypeChecker_Env.use_eq);
                    FStar_TypeChecker_Env.use_eq_strict =
                      (uu___510_3217.FStar_TypeChecker_Env.use_eq_strict);
                    FStar_TypeChecker_Env.is_iface =
                      (uu___510_3217.FStar_TypeChecker_Env.is_iface);
                    FStar_TypeChecker_Env.admit =
                      (uu___510_3217.FStar_TypeChecker_Env.admit);
                    FStar_TypeChecker_Env.lax =
                      (uu___510_3217.FStar_TypeChecker_Env.lax);
                    FStar_TypeChecker_Env.lax_universes =
                      (uu___510_3217.FStar_TypeChecker_Env.lax_universes);
                    FStar_TypeChecker_Env.phase1 =
                      (uu___510_3217.FStar_TypeChecker_Env.phase1);
                    FStar_TypeChecker_Env.failhard =
                      (uu___510_3217.FStar_TypeChecker_Env.failhard);
                    FStar_TypeChecker_Env.nosynth =
                      (uu___510_3217.FStar_TypeChecker_Env.nosynth);
                    FStar_TypeChecker_Env.uvar_subtyping = false;
                    FStar_TypeChecker_Env.tc_term =
                      (uu___510_3217.FStar_TypeChecker_Env.tc_term);
                    FStar_TypeChecker_Env.type_of =
                      (uu___510_3217.FStar_TypeChecker_Env.type_of);
                    FStar_TypeChecker_Env.universe_of =
                      (uu___510_3217.FStar_TypeChecker_Env.universe_of);
                    FStar_TypeChecker_Env.check_type_of =
                      (uu___510_3217.FStar_TypeChecker_Env.check_type_of);
                    FStar_TypeChecker_Env.use_bv_sorts =
                      (uu___510_3217.FStar_TypeChecker_Env.use_bv_sorts);
                    FStar_TypeChecker_Env.qtbl_name_and_index =
                      (uu___510_3217.FStar_TypeChecker_Env.qtbl_name_and_index);
                    FStar_TypeChecker_Env.normalized_eff_names =
                      (uu___510_3217.FStar_TypeChecker_Env.normalized_eff_names);
                    FStar_TypeChecker_Env.fv_delta_depths =
                      (uu___510_3217.FStar_TypeChecker_Env.fv_delta_depths);
                    FStar_TypeChecker_Env.proof_ns =
                      (uu___510_3217.FStar_TypeChecker_Env.proof_ns);
                    FStar_TypeChecker_Env.synth_hook =
                      (uu___510_3217.FStar_TypeChecker_Env.synth_hook);
                    FStar_TypeChecker_Env.try_solve_implicits_hook =
                      (uu___510_3217.FStar_TypeChecker_Env.try_solve_implicits_hook);
                    FStar_TypeChecker_Env.splice =
                      (uu___510_3217.FStar_TypeChecker_Env.splice);
                    FStar_TypeChecker_Env.mpreprocess =
                      (uu___510_3217.FStar_TypeChecker_Env.mpreprocess);
                    FStar_TypeChecker_Env.postprocess =
                      (uu___510_3217.FStar_TypeChecker_Env.postprocess);
                    FStar_TypeChecker_Env.is_native_tactic =
                      (uu___510_3217.FStar_TypeChecker_Env.is_native_tactic);
                    FStar_TypeChecker_Env.identifier_info =
                      (uu___510_3217.FStar_TypeChecker_Env.identifier_info);
                    FStar_TypeChecker_Env.tc_hooks =
                      (uu___510_3217.FStar_TypeChecker_Env.tc_hooks);
                    FStar_TypeChecker_Env.dsenv =
                      (uu___510_3217.FStar_TypeChecker_Env.dsenv);
                    FStar_TypeChecker_Env.nbe =
                      (uu___510_3217.FStar_TypeChecker_Env.nbe);
                    FStar_TypeChecker_Env.strict_args_tab =
                      (uu___510_3217.FStar_TypeChecker_Env.strict_args_tab);
                    FStar_TypeChecker_Env.erasable_types_tab =
                      (uu___510_3217.FStar_TypeChecker_Env.erasable_types_tab)
                  }  in
                try
                  (fun uu___514_3232  ->
                     match () with
                     | () ->
                         let uu____3241 =
                           FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term e1 t
                            in
                         (match uu____3241 with
                          | (t1,lc,g) ->
                              ret
                                (t1, (lc.FStar_TypeChecker_Common.res_typ),
                                  g))) ()
                with
                | FStar_Errors.Err (uu____3279,msg) ->
                    let uu____3283 = tts e1 t  in
                    let uu____3285 =
                      let uu____3287 = FStar_TypeChecker_Env.all_binders e1
                         in
                      FStar_All.pipe_right uu____3287
                        (FStar_Syntax_Print.binders_to_string ", ")
                       in
                    fail3 "Cannot type %s in context (%s). Error = (%s)"
                      uu____3283 uu____3285 msg
                | FStar_Errors.Error (uu____3297,msg,uu____3299) ->
                    let uu____3302 = tts e1 t  in
                    let uu____3304 =
                      let uu____3306 = FStar_TypeChecker_Env.all_binders e1
                         in
                      FStar_All.pipe_right uu____3306
                        (FStar_Syntax_Print.binders_to_string ", ")
                       in
                    fail3 "Cannot type %s in context (%s). Error = (%s)"
                      uu____3302 uu____3304 msg))
  
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
             (fun uu____3359  ->
                let uu____3360 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.print1 "Tac> __tc_lax(%s)\n" uu____3360)
             (fun uu____3366  ->
                let e1 =
                  let uu___535_3368 = e  in
                  {
                    FStar_TypeChecker_Env.solver =
                      (uu___535_3368.FStar_TypeChecker_Env.solver);
                    FStar_TypeChecker_Env.range =
                      (uu___535_3368.FStar_TypeChecker_Env.range);
                    FStar_TypeChecker_Env.curmodule =
                      (uu___535_3368.FStar_TypeChecker_Env.curmodule);
                    FStar_TypeChecker_Env.gamma =
                      (uu___535_3368.FStar_TypeChecker_Env.gamma);
                    FStar_TypeChecker_Env.gamma_sig =
                      (uu___535_3368.FStar_TypeChecker_Env.gamma_sig);
                    FStar_TypeChecker_Env.gamma_cache =
                      (uu___535_3368.FStar_TypeChecker_Env.gamma_cache);
                    FStar_TypeChecker_Env.modules =
                      (uu___535_3368.FStar_TypeChecker_Env.modules);
                    FStar_TypeChecker_Env.expected_typ =
                      (uu___535_3368.FStar_TypeChecker_Env.expected_typ);
                    FStar_TypeChecker_Env.sigtab =
                      (uu___535_3368.FStar_TypeChecker_Env.sigtab);
                    FStar_TypeChecker_Env.attrtab =
                      (uu___535_3368.FStar_TypeChecker_Env.attrtab);
                    FStar_TypeChecker_Env.instantiate_imp =
                      (uu___535_3368.FStar_TypeChecker_Env.instantiate_imp);
                    FStar_TypeChecker_Env.effects =
                      (uu___535_3368.FStar_TypeChecker_Env.effects);
                    FStar_TypeChecker_Env.generalize =
                      (uu___535_3368.FStar_TypeChecker_Env.generalize);
                    FStar_TypeChecker_Env.letrecs =
                      (uu___535_3368.FStar_TypeChecker_Env.letrecs);
                    FStar_TypeChecker_Env.top_level =
                      (uu___535_3368.FStar_TypeChecker_Env.top_level);
                    FStar_TypeChecker_Env.check_uvars =
                      (uu___535_3368.FStar_TypeChecker_Env.check_uvars);
                    FStar_TypeChecker_Env.use_eq =
                      (uu___535_3368.FStar_TypeChecker_Env.use_eq);
                    FStar_TypeChecker_Env.use_eq_strict =
                      (uu___535_3368.FStar_TypeChecker_Env.use_eq_strict);
                    FStar_TypeChecker_Env.is_iface =
                      (uu___535_3368.FStar_TypeChecker_Env.is_iface);
                    FStar_TypeChecker_Env.admit =
                      (uu___535_3368.FStar_TypeChecker_Env.admit);
                    FStar_TypeChecker_Env.lax =
                      (uu___535_3368.FStar_TypeChecker_Env.lax);
                    FStar_TypeChecker_Env.lax_universes =
                      (uu___535_3368.FStar_TypeChecker_Env.lax_universes);
                    FStar_TypeChecker_Env.phase1 =
                      (uu___535_3368.FStar_TypeChecker_Env.phase1);
                    FStar_TypeChecker_Env.failhard =
                      (uu___535_3368.FStar_TypeChecker_Env.failhard);
                    FStar_TypeChecker_Env.nosynth =
                      (uu___535_3368.FStar_TypeChecker_Env.nosynth);
                    FStar_TypeChecker_Env.uvar_subtyping = false;
                    FStar_TypeChecker_Env.tc_term =
                      (uu___535_3368.FStar_TypeChecker_Env.tc_term);
                    FStar_TypeChecker_Env.type_of =
                      (uu___535_3368.FStar_TypeChecker_Env.type_of);
                    FStar_TypeChecker_Env.universe_of =
                      (uu___535_3368.FStar_TypeChecker_Env.universe_of);
                    FStar_TypeChecker_Env.check_type_of =
                      (uu___535_3368.FStar_TypeChecker_Env.check_type_of);
                    FStar_TypeChecker_Env.use_bv_sorts =
                      (uu___535_3368.FStar_TypeChecker_Env.use_bv_sorts);
                    FStar_TypeChecker_Env.qtbl_name_and_index =
                      (uu___535_3368.FStar_TypeChecker_Env.qtbl_name_and_index);
                    FStar_TypeChecker_Env.normalized_eff_names =
                      (uu___535_3368.FStar_TypeChecker_Env.normalized_eff_names);
                    FStar_TypeChecker_Env.fv_delta_depths =
                      (uu___535_3368.FStar_TypeChecker_Env.fv_delta_depths);
                    FStar_TypeChecker_Env.proof_ns =
                      (uu___535_3368.FStar_TypeChecker_Env.proof_ns);
                    FStar_TypeChecker_Env.synth_hook =
                      (uu___535_3368.FStar_TypeChecker_Env.synth_hook);
                    FStar_TypeChecker_Env.try_solve_implicits_hook =
                      (uu___535_3368.FStar_TypeChecker_Env.try_solve_implicits_hook);
                    FStar_TypeChecker_Env.splice =
                      (uu___535_3368.FStar_TypeChecker_Env.splice);
                    FStar_TypeChecker_Env.mpreprocess =
                      (uu___535_3368.FStar_TypeChecker_Env.mpreprocess);
                    FStar_TypeChecker_Env.postprocess =
                      (uu___535_3368.FStar_TypeChecker_Env.postprocess);
                    FStar_TypeChecker_Env.is_native_tactic =
                      (uu___535_3368.FStar_TypeChecker_Env.is_native_tactic);
                    FStar_TypeChecker_Env.identifier_info =
                      (uu___535_3368.FStar_TypeChecker_Env.identifier_info);
                    FStar_TypeChecker_Env.tc_hooks =
                      (uu___535_3368.FStar_TypeChecker_Env.tc_hooks);
                    FStar_TypeChecker_Env.dsenv =
                      (uu___535_3368.FStar_TypeChecker_Env.dsenv);
                    FStar_TypeChecker_Env.nbe =
                      (uu___535_3368.FStar_TypeChecker_Env.nbe);
                    FStar_TypeChecker_Env.strict_args_tab =
                      (uu___535_3368.FStar_TypeChecker_Env.strict_args_tab);
                    FStar_TypeChecker_Env.erasable_types_tab =
                      (uu___535_3368.FStar_TypeChecker_Env.erasable_types_tab)
                  }  in
                let e2 =
                  let uu___538_3371 = e1  in
                  {
                    FStar_TypeChecker_Env.solver =
                      (uu___538_3371.FStar_TypeChecker_Env.solver);
                    FStar_TypeChecker_Env.range =
                      (uu___538_3371.FStar_TypeChecker_Env.range);
                    FStar_TypeChecker_Env.curmodule =
                      (uu___538_3371.FStar_TypeChecker_Env.curmodule);
                    FStar_TypeChecker_Env.gamma =
                      (uu___538_3371.FStar_TypeChecker_Env.gamma);
                    FStar_TypeChecker_Env.gamma_sig =
                      (uu___538_3371.FStar_TypeChecker_Env.gamma_sig);
                    FStar_TypeChecker_Env.gamma_cache =
                      (uu___538_3371.FStar_TypeChecker_Env.gamma_cache);
                    FStar_TypeChecker_Env.modules =
                      (uu___538_3371.FStar_TypeChecker_Env.modules);
                    FStar_TypeChecker_Env.expected_typ =
                      (uu___538_3371.FStar_TypeChecker_Env.expected_typ);
                    FStar_TypeChecker_Env.sigtab =
                      (uu___538_3371.FStar_TypeChecker_Env.sigtab);
                    FStar_TypeChecker_Env.attrtab =
                      (uu___538_3371.FStar_TypeChecker_Env.attrtab);
                    FStar_TypeChecker_Env.instantiate_imp =
                      (uu___538_3371.FStar_TypeChecker_Env.instantiate_imp);
                    FStar_TypeChecker_Env.effects =
                      (uu___538_3371.FStar_TypeChecker_Env.effects);
                    FStar_TypeChecker_Env.generalize =
                      (uu___538_3371.FStar_TypeChecker_Env.generalize);
                    FStar_TypeChecker_Env.letrecs =
                      (uu___538_3371.FStar_TypeChecker_Env.letrecs);
                    FStar_TypeChecker_Env.top_level =
                      (uu___538_3371.FStar_TypeChecker_Env.top_level);
                    FStar_TypeChecker_Env.check_uvars =
                      (uu___538_3371.FStar_TypeChecker_Env.check_uvars);
                    FStar_TypeChecker_Env.use_eq =
                      (uu___538_3371.FStar_TypeChecker_Env.use_eq);
                    FStar_TypeChecker_Env.use_eq_strict =
                      (uu___538_3371.FStar_TypeChecker_Env.use_eq_strict);
                    FStar_TypeChecker_Env.is_iface =
                      (uu___538_3371.FStar_TypeChecker_Env.is_iface);
                    FStar_TypeChecker_Env.admit =
                      (uu___538_3371.FStar_TypeChecker_Env.admit);
                    FStar_TypeChecker_Env.lax = true;
                    FStar_TypeChecker_Env.lax_universes =
                      (uu___538_3371.FStar_TypeChecker_Env.lax_universes);
                    FStar_TypeChecker_Env.phase1 =
                      (uu___538_3371.FStar_TypeChecker_Env.phase1);
                    FStar_TypeChecker_Env.failhard =
                      (uu___538_3371.FStar_TypeChecker_Env.failhard);
                    FStar_TypeChecker_Env.nosynth =
                      (uu___538_3371.FStar_TypeChecker_Env.nosynth);
                    FStar_TypeChecker_Env.uvar_subtyping =
                      (uu___538_3371.FStar_TypeChecker_Env.uvar_subtyping);
                    FStar_TypeChecker_Env.tc_term =
                      (uu___538_3371.FStar_TypeChecker_Env.tc_term);
                    FStar_TypeChecker_Env.type_of =
                      (uu___538_3371.FStar_TypeChecker_Env.type_of);
                    FStar_TypeChecker_Env.universe_of =
                      (uu___538_3371.FStar_TypeChecker_Env.universe_of);
                    FStar_TypeChecker_Env.check_type_of =
                      (uu___538_3371.FStar_TypeChecker_Env.check_type_of);
                    FStar_TypeChecker_Env.use_bv_sorts =
                      (uu___538_3371.FStar_TypeChecker_Env.use_bv_sorts);
                    FStar_TypeChecker_Env.qtbl_name_and_index =
                      (uu___538_3371.FStar_TypeChecker_Env.qtbl_name_and_index);
                    FStar_TypeChecker_Env.normalized_eff_names =
                      (uu___538_3371.FStar_TypeChecker_Env.normalized_eff_names);
                    FStar_TypeChecker_Env.fv_delta_depths =
                      (uu___538_3371.FStar_TypeChecker_Env.fv_delta_depths);
                    FStar_TypeChecker_Env.proof_ns =
                      (uu___538_3371.FStar_TypeChecker_Env.proof_ns);
                    FStar_TypeChecker_Env.synth_hook =
                      (uu___538_3371.FStar_TypeChecker_Env.synth_hook);
                    FStar_TypeChecker_Env.try_solve_implicits_hook =
                      (uu___538_3371.FStar_TypeChecker_Env.try_solve_implicits_hook);
                    FStar_TypeChecker_Env.splice =
                      (uu___538_3371.FStar_TypeChecker_Env.splice);
                    FStar_TypeChecker_Env.mpreprocess =
                      (uu___538_3371.FStar_TypeChecker_Env.mpreprocess);
                    FStar_TypeChecker_Env.postprocess =
                      (uu___538_3371.FStar_TypeChecker_Env.postprocess);
                    FStar_TypeChecker_Env.is_native_tactic =
                      (uu___538_3371.FStar_TypeChecker_Env.is_native_tactic);
                    FStar_TypeChecker_Env.identifier_info =
                      (uu___538_3371.FStar_TypeChecker_Env.identifier_info);
                    FStar_TypeChecker_Env.tc_hooks =
                      (uu___538_3371.FStar_TypeChecker_Env.tc_hooks);
                    FStar_TypeChecker_Env.dsenv =
                      (uu___538_3371.FStar_TypeChecker_Env.dsenv);
                    FStar_TypeChecker_Env.nbe =
                      (uu___538_3371.FStar_TypeChecker_Env.nbe);
                    FStar_TypeChecker_Env.strict_args_tab =
                      (uu___538_3371.FStar_TypeChecker_Env.strict_args_tab);
                    FStar_TypeChecker_Env.erasable_types_tab =
                      (uu___538_3371.FStar_TypeChecker_Env.erasable_types_tab)
                  }  in
                try
                  (fun uu___542_3383  ->
                     match () with
                     | () ->
                         let uu____3392 =
                           FStar_TypeChecker_TcTerm.tc_term e2 t  in
                         ret uu____3392) ()
                with
                | FStar_Errors.Err (uu____3419,msg) ->
                    let uu____3423 = tts e2 t  in
                    let uu____3425 =
                      let uu____3427 = FStar_TypeChecker_Env.all_binders e2
                         in
                      FStar_All.pipe_right uu____3427
                        (FStar_Syntax_Print.binders_to_string ", ")
                       in
                    fail3 "Cannot type %s in context (%s). Error = (%s)"
                      uu____3423 uu____3425 msg
                | FStar_Errors.Error (uu____3437,msg,uu____3439) ->
                    let uu____3442 = tts e2 t  in
                    let uu____3444 =
                      let uu____3446 = FStar_TypeChecker_Env.all_binders e2
                         in
                      FStar_All.pipe_right uu____3446
                        (FStar_Syntax_Print.binders_to_string ", ")
                       in
                    fail3 "Cannot type %s in context (%s). Error = (%s)"
                      uu____3442 uu____3444 msg))
  
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
  fun uu____3480  ->
    bind get (fun ps  -> ret ps.FStar_Tactics_Types.guard_policy)
  
let (set_guard_policy : FStar_Tactics_Types.guard_policy -> unit tac) =
  fun pol  ->
    bind get
      (fun ps  ->
         set
           (let uu___563_3499 = ps  in
            {
              FStar_Tactics_Types.main_context =
                (uu___563_3499.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.all_implicits =
                (uu___563_3499.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___563_3499.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (uu___563_3499.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___563_3499.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___563_3499.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___563_3499.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___563_3499.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy = pol;
              FStar_Tactics_Types.freshness =
                (uu___563_3499.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___563_3499.FStar_Tactics_Types.tac_verb_dbg);
              FStar_Tactics_Types.local_state =
                (uu___563_3499.FStar_Tactics_Types.local_state)
            }))
  
let with_policy : 'a . FStar_Tactics_Types.guard_policy -> 'a tac -> 'a tac =
  fun pol  ->
    fun t  ->
      let uu____3524 = get_guard_policy ()  in
      bind uu____3524
        (fun old_pol  ->
           let uu____3530 = set_guard_policy pol  in
           bind uu____3530
             (fun uu____3534  ->
                bind t
                  (fun r  ->
                     let uu____3538 = set_guard_policy old_pol  in
                     bind uu____3538 (fun uu____3542  -> ret r))))
  
let (getopts : FStar_Options.optionstate tac) =
  let uu____3546 = let uu____3551 = cur_goal ()  in trytac uu____3551  in
  bind uu____3546
    (fun uu___0_3558  ->
       match uu___0_3558 with
       | FStar_Pervasives_Native.Some g -> ret g.FStar_Tactics_Types.opts
       | FStar_Pervasives_Native.None  ->
           let uu____3564 = FStar_Options.peek ()  in ret uu____3564)
  
let (proc_guard :
  Prims.string -> env -> FStar_TypeChecker_Common.guard_t -> unit tac) =
  fun reason  ->
    fun e  ->
      fun g  ->
        mlog
          (fun uu____3589  ->
             let uu____3590 = FStar_TypeChecker_Rel.guard_to_string e g  in
             FStar_Util.print2 "Processing guard (%s:%s)\n" reason uu____3590)
          (fun uu____3595  ->
             let uu____3596 =
               add_implicits g.FStar_TypeChecker_Common.implicits  in
             bind uu____3596
               (fun uu____3600  ->
                  bind getopts
                    (fun opts  ->
                       let uu____3604 =
                         let uu____3605 =
                           FStar_TypeChecker_Rel.simplify_guard e g  in
                         uu____3605.FStar_TypeChecker_Common.guard_f  in
                       match uu____3604 with
                       | FStar_TypeChecker_Common.Trivial  -> ret ()
                       | FStar_TypeChecker_Common.NonTrivial f ->
                           let uu____3609 = istrivial e f  in
                           if uu____3609
                           then ret ()
                           else
                             bind get
                               (fun ps  ->
                                  match ps.FStar_Tactics_Types.guard_policy
                                  with
                                  | FStar_Tactics_Types.Drop  ->
                                      ((let uu____3622 =
                                          let uu____3628 =
                                            let uu____3630 =
                                              FStar_TypeChecker_Rel.guard_to_string
                                                e g
                                               in
                                            FStar_Util.format1
                                              "Tactics admitted guard <%s>\n\n"
                                              uu____3630
                                             in
                                          (FStar_Errors.Warning_TacAdmit,
                                            uu____3628)
                                           in
                                        FStar_Errors.log_issue
                                          e.FStar_TypeChecker_Env.range
                                          uu____3622);
                                       ret ())
                                  | FStar_Tactics_Types.Goal  ->
                                      mlog
                                        (fun uu____3636  ->
                                           let uu____3637 =
                                             FStar_TypeChecker_Rel.guard_to_string
                                               e g
                                              in
                                           FStar_Util.print2
                                             "Making guard (%s:%s) into a goal\n"
                                             reason uu____3637)
                                        (fun uu____3642  ->
                                           let uu____3643 =
                                             mk_irrelevant_goal reason e f
                                               opts ""
                                              in
                                           bind uu____3643
                                             (fun goal  ->
                                                let goal1 =
                                                  let uu___592_3651 = goal
                                                     in
                                                  {
                                                    FStar_Tactics_Types.goal_main_env
                                                      =
                                                      (uu___592_3651.FStar_Tactics_Types.goal_main_env);
                                                    FStar_Tactics_Types.goal_ctx_uvar
                                                      =
                                                      (uu___592_3651.FStar_Tactics_Types.goal_ctx_uvar);
                                                    FStar_Tactics_Types.opts
                                                      =
                                                      (uu___592_3651.FStar_Tactics_Types.opts);
                                                    FStar_Tactics_Types.is_guard
                                                      = true;
                                                    FStar_Tactics_Types.label
                                                      =
                                                      (uu___592_3651.FStar_Tactics_Types.label)
                                                  }  in
                                                push_goals [goal1]))
                                  | FStar_Tactics_Types.SMT  ->
                                      mlog
                                        (fun uu____3655  ->
                                           let uu____3656 =
                                             FStar_TypeChecker_Rel.guard_to_string
                                               e g
                                              in
                                           FStar_Util.print2
                                             "Sending guard (%s:%s) to SMT goal\n"
                                             reason uu____3656)
                                        (fun uu____3661  ->
                                           let uu____3662 =
                                             mk_irrelevant_goal reason e f
                                               opts ""
                                              in
                                           bind uu____3662
                                             (fun goal  ->
                                                let goal1 =
                                                  let uu___599_3670 = goal
                                                     in
                                                  {
                                                    FStar_Tactics_Types.goal_main_env
                                                      =
                                                      (uu___599_3670.FStar_Tactics_Types.goal_main_env);
                                                    FStar_Tactics_Types.goal_ctx_uvar
                                                      =
                                                      (uu___599_3670.FStar_Tactics_Types.goal_ctx_uvar);
                                                    FStar_Tactics_Types.opts
                                                      =
                                                      (uu___599_3670.FStar_Tactics_Types.opts);
                                                    FStar_Tactics_Types.is_guard
                                                      = true;
                                                    FStar_Tactics_Types.label
                                                      =
                                                      (uu___599_3670.FStar_Tactics_Types.label)
                                                  }  in
                                                push_smt_goals [goal1]))
                                  | FStar_Tactics_Types.Force  ->
                                      mlog
                                        (fun uu____3674  ->
                                           let uu____3675 =
                                             FStar_TypeChecker_Rel.guard_to_string
                                               e g
                                              in
                                           FStar_Util.print2
                                             "Forcing guard (%s:%s)\n" reason
                                             uu____3675)
                                        (fun uu____3679  ->
                                           try
                                             (fun uu___606_3684  ->
                                                match () with
                                                | () ->
                                                    let uu____3687 =
                                                      let uu____3689 =
                                                        let uu____3691 =
                                                          FStar_TypeChecker_Rel.discharge_guard_no_smt
                                                            e g
                                                           in
                                                        FStar_All.pipe_left
                                                          FStar_TypeChecker_Env.is_trivial
                                                          uu____3691
                                                         in
                                                      Prims.op_Negation
                                                        uu____3689
                                                       in
                                                    if uu____3687
                                                    then
                                                      mlog
                                                        (fun uu____3698  ->
                                                           let uu____3699 =
                                                             FStar_TypeChecker_Rel.guard_to_string
                                                               e g
                                                              in
                                                           FStar_Util.print1
                                                             "guard = %s\n"
                                                             uu____3699)
                                                        (fun uu____3703  ->
                                                           fail1
                                                             "Forcing the guard failed (%s)"
                                                             reason)
                                                    else ret ()) ()
                                           with
                                           | uu___605_3708 ->
                                               mlog
                                                 (fun uu____3713  ->
                                                    let uu____3714 =
                                                      FStar_TypeChecker_Rel.guard_to_string
                                                        e g
                                                       in
                                                    FStar_Util.print1
                                                      "guard = %s\n"
                                                      uu____3714)
                                                 (fun uu____3718  ->
                                                    fail1
                                                      "Forcing the guard failed (%s)"
                                                      reason))))))
  
let (tcc : env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.comp tac) =
  fun e  ->
    fun t  ->
      let uu____3735 =
        let uu____3738 = __tc_lax e t  in
        bind uu____3738
          (fun uu____3758  ->
             match uu____3758 with
             | (uu____3767,lc,uu____3769) ->
                 let uu____3770 =
                   let uu____3771 = FStar_TypeChecker_Common.lcomp_comp lc
                      in
                   FStar_All.pipe_right uu____3771
                     FStar_Pervasives_Native.fst
                    in
                 ret uu____3770)
         in
      FStar_All.pipe_left (wrap_err "tcc") uu____3735
  
let (tc : env -> FStar_Syntax_Syntax.term -> FStar_Reflection_Data.typ tac) =
  fun e  ->
    fun t  ->
      let uu____3800 =
        let uu____3805 = tcc e t  in
        bind uu____3805 (fun c  -> ret (FStar_Syntax_Util.comp_result c))  in
      FStar_All.pipe_left (wrap_err "tc") uu____3800
  
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
            let uu____3857 = mk_irrelevant_goal reason env phi opts label1
               in
            bind uu____3857 (fun goal  -> add_goals [goal])
  
let (trivial : unit -> unit tac) =
  fun uu____3869  ->
    let uu____3872 = cur_goal ()  in
    bind uu____3872
      (fun goal  ->
         let uu____3878 =
           let uu____3880 = FStar_Tactics_Types.goal_env goal  in
           let uu____3881 = FStar_Tactics_Types.goal_type goal  in
           istrivial uu____3880 uu____3881  in
         if uu____3878
         then solve' goal FStar_Syntax_Util.exp_unit
         else
           (let uu____3887 =
              let uu____3889 = FStar_Tactics_Types.goal_env goal  in
              let uu____3890 = FStar_Tactics_Types.goal_type goal  in
              tts uu____3889 uu____3890  in
            fail1 "Not a trivial goal: %s" uu____3887))
  
let divide : 'a 'b . FStar_BigInt.t -> 'a tac -> 'b tac -> ('a * 'b) tac =
  fun n1  ->
    fun l  ->
      fun r  ->
        bind get
          (fun p  ->
             let uu____3941 =
               try
                 (fun uu___665_3964  ->
                    match () with
                    | () ->
                        let uu____3975 =
                          let uu____3984 = FStar_BigInt.to_int_fs n1  in
                          FStar_List.splitAt uu____3984
                            p.FStar_Tactics_Types.goals
                           in
                        ret uu____3975) ()
               with | uu___664_3995 -> fail "divide: not enough goals"  in
             bind uu____3941
               (fun uu____4032  ->
                  match uu____4032 with
                  | (lgs,rgs) ->
                      let lp =
                        let uu___647_4058 = p  in
                        {
                          FStar_Tactics_Types.main_context =
                            (uu___647_4058.FStar_Tactics_Types.main_context);
                          FStar_Tactics_Types.all_implicits =
                            (uu___647_4058.FStar_Tactics_Types.all_implicits);
                          FStar_Tactics_Types.goals = lgs;
                          FStar_Tactics_Types.smt_goals = [];
                          FStar_Tactics_Types.depth =
                            (uu___647_4058.FStar_Tactics_Types.depth);
                          FStar_Tactics_Types.__dump =
                            (uu___647_4058.FStar_Tactics_Types.__dump);
                          FStar_Tactics_Types.psc =
                            (uu___647_4058.FStar_Tactics_Types.psc);
                          FStar_Tactics_Types.entry_range =
                            (uu___647_4058.FStar_Tactics_Types.entry_range);
                          FStar_Tactics_Types.guard_policy =
                            (uu___647_4058.FStar_Tactics_Types.guard_policy);
                          FStar_Tactics_Types.freshness =
                            (uu___647_4058.FStar_Tactics_Types.freshness);
                          FStar_Tactics_Types.tac_verb_dbg =
                            (uu___647_4058.FStar_Tactics_Types.tac_verb_dbg);
                          FStar_Tactics_Types.local_state =
                            (uu___647_4058.FStar_Tactics_Types.local_state)
                        }  in
                      let uu____4059 = set lp  in
                      bind uu____4059
                        (fun uu____4067  ->
                           bind l
                             (fun a  ->
                                bind get
                                  (fun lp'  ->
                                     let rp =
                                       let uu___653_4083 = lp'  in
                                       {
                                         FStar_Tactics_Types.main_context =
                                           (uu___653_4083.FStar_Tactics_Types.main_context);
                                         FStar_Tactics_Types.all_implicits =
                                           (uu___653_4083.FStar_Tactics_Types.all_implicits);
                                         FStar_Tactics_Types.goals = rgs;
                                         FStar_Tactics_Types.smt_goals = [];
                                         FStar_Tactics_Types.depth =
                                           (uu___653_4083.FStar_Tactics_Types.depth);
                                         FStar_Tactics_Types.__dump =
                                           (uu___653_4083.FStar_Tactics_Types.__dump);
                                         FStar_Tactics_Types.psc =
                                           (uu___653_4083.FStar_Tactics_Types.psc);
                                         FStar_Tactics_Types.entry_range =
                                           (uu___653_4083.FStar_Tactics_Types.entry_range);
                                         FStar_Tactics_Types.guard_policy =
                                           (uu___653_4083.FStar_Tactics_Types.guard_policy);
                                         FStar_Tactics_Types.freshness =
                                           (uu___653_4083.FStar_Tactics_Types.freshness);
                                         FStar_Tactics_Types.tac_verb_dbg =
                                           (uu___653_4083.FStar_Tactics_Types.tac_verb_dbg);
                                         FStar_Tactics_Types.local_state =
                                           (uu___653_4083.FStar_Tactics_Types.local_state)
                                       }  in
                                     let uu____4084 = set rp  in
                                     bind uu____4084
                                       (fun uu____4092  ->
                                          bind r
                                            (fun b  ->
                                               bind get
                                                 (fun rp'  ->
                                                    let p' =
                                                      let uu___659_4108 = rp'
                                                         in
                                                      {
                                                        FStar_Tactics_Types.main_context
                                                          =
                                                          (uu___659_4108.FStar_Tactics_Types.main_context);
                                                        FStar_Tactics_Types.all_implicits
                                                          =
                                                          (uu___659_4108.FStar_Tactics_Types.all_implicits);
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
                                                          (uu___659_4108.FStar_Tactics_Types.depth);
                                                        FStar_Tactics_Types.__dump
                                                          =
                                                          (uu___659_4108.FStar_Tactics_Types.__dump);
                                                        FStar_Tactics_Types.psc
                                                          =
                                                          (uu___659_4108.FStar_Tactics_Types.psc);
                                                        FStar_Tactics_Types.entry_range
                                                          =
                                                          (uu___659_4108.FStar_Tactics_Types.entry_range);
                                                        FStar_Tactics_Types.guard_policy
                                                          =
                                                          (uu___659_4108.FStar_Tactics_Types.guard_policy);
                                                        FStar_Tactics_Types.freshness
                                                          =
                                                          (uu___659_4108.FStar_Tactics_Types.freshness);
                                                        FStar_Tactics_Types.tac_verb_dbg
                                                          =
                                                          (uu___659_4108.FStar_Tactics_Types.tac_verb_dbg);
                                                        FStar_Tactics_Types.local_state
                                                          =
                                                          (uu___659_4108.FStar_Tactics_Types.local_state)
                                                      }  in
                                                    let uu____4109 = set p'
                                                       in
                                                    bind uu____4109
                                                      (fun uu____4117  ->
                                                         bind
                                                           remove_solved_goals
                                                           (fun uu____4123 
                                                              -> ret (a, b)))))))))))
  
let focus : 'a . 'a tac -> 'a tac =
  fun f  ->
    let uu____4145 = divide FStar_BigInt.one f idtac  in
    bind uu____4145
      (fun uu____4158  -> match uu____4158 with | (a,()) -> ret a)
  
let rec map : 'a . 'a tac -> 'a Prims.list tac =
  fun tau  ->
    bind get
      (fun p  ->
         match p.FStar_Tactics_Types.goals with
         | [] -> ret []
         | uu____4196::uu____4197 ->
             let uu____4200 =
               let uu____4209 = map tau  in
               divide FStar_BigInt.one tau uu____4209  in
             bind uu____4200
               (fun uu____4227  ->
                  match uu____4227 with | (h,t) -> ret (h :: t)))
  
let (seq : unit tac -> unit tac -> unit tac) =
  fun t1  ->
    fun t2  ->
      let uu____4269 =
        bind t1
          (fun uu____4274  ->
             let uu____4275 = map t2  in
             bind uu____4275 (fun uu____4283  -> ret ()))
         in
      focus uu____4269
  
let (intro : unit -> FStar_Syntax_Syntax.binder tac) =
  fun uu____4293  ->
    let uu____4296 =
      let uu____4299 = cur_goal ()  in
      bind uu____4299
        (fun goal  ->
           let uu____4308 =
             let uu____4315 = FStar_Tactics_Types.goal_type goal  in
             FStar_Syntax_Util.arrow_one uu____4315  in
           match uu____4308 with
           | FStar_Pervasives_Native.Some (b,c) ->
               let uu____4324 =
                 let uu____4326 = FStar_Syntax_Util.is_total_comp c  in
                 Prims.op_Negation uu____4326  in
               if uu____4324
               then fail "Codomain is effectful"
               else
                 (let env' =
                    let uu____4335 = FStar_Tactics_Types.goal_env goal  in
                    FStar_TypeChecker_Env.push_binders uu____4335 [b]  in
                  let typ' = FStar_Syntax_Util.comp_result c  in
                  let uu____4351 = new_uvar "intro" env' typ'  in
                  bind uu____4351
                    (fun uu____4368  ->
                       match uu____4368 with
                       | (body,ctx_uvar) ->
                           let sol =
                             FStar_Syntax_Util.abs [b] body
                               (FStar_Pervasives_Native.Some
                                  (FStar_Syntax_Util.residual_comp_of_comp c))
                              in
                           let uu____4392 = set_solution goal sol  in
                           bind uu____4392
                             (fun uu____4398  ->
                                let g =
                                  FStar_Tactics_Types.mk_goal env' ctx_uvar
                                    goal.FStar_Tactics_Types.opts
                                    goal.FStar_Tactics_Types.is_guard
                                    goal.FStar_Tactics_Types.label
                                   in
                                let uu____4400 =
                                  let uu____4403 = bnorm_goal g  in
                                  replace_cur uu____4403  in
                                bind uu____4400 (fun uu____4405  -> ret b))))
           | FStar_Pervasives_Native.None  ->
               let uu____4410 =
                 let uu____4412 = FStar_Tactics_Types.goal_env goal  in
                 let uu____4413 = FStar_Tactics_Types.goal_type goal  in
                 tts uu____4412 uu____4413  in
               fail1 "goal is not an arrow (%s)" uu____4410)
       in
    FStar_All.pipe_left (wrap_err "intro") uu____4296
  
let (intro_rec :
  unit -> (FStar_Syntax_Syntax.binder * FStar_Syntax_Syntax.binder) tac) =
  fun uu____4431  ->
    let uu____4438 = cur_goal ()  in
    bind uu____4438
      (fun goal  ->
         FStar_Util.print_string
           "WARNING (intro_rec): calling this is known to cause normalizer loops\n";
         FStar_Util.print_string
           "WARNING (intro_rec): proceed at your own risk...\n";
         (let uu____4457 =
            let uu____4464 = FStar_Tactics_Types.goal_type goal  in
            FStar_Syntax_Util.arrow_one uu____4464  in
          match uu____4457 with
          | FStar_Pervasives_Native.Some (b,c) ->
              let uu____4477 =
                let uu____4479 = FStar_Syntax_Util.is_total_comp c  in
                Prims.op_Negation uu____4479  in
              if uu____4477
              then fail "Codomain is effectful"
              else
                (let bv =
                   let uu____4496 = FStar_Tactics_Types.goal_type goal  in
                   FStar_Syntax_Syntax.gen_bv "__recf"
                     FStar_Pervasives_Native.None uu____4496
                    in
                 let bs =
                   let uu____4507 = FStar_Syntax_Syntax.mk_binder bv  in
                   [uu____4507; b]  in
                 let env' =
                   let uu____4533 = FStar_Tactics_Types.goal_env goal  in
                   FStar_TypeChecker_Env.push_binders uu____4533 bs  in
                 let uu____4534 =
                   new_uvar "intro_rec" env'
                     (FStar_Syntax_Util.comp_result c)
                    in
                 bind uu____4534
                   (fun uu____4560  ->
                      match uu____4560 with
                      | (u,ctx_uvar_u) ->
                          let lb =
                            let uu____4574 =
                              FStar_Tactics_Types.goal_type goal  in
                            let uu____4577 =
                              FStar_Syntax_Util.abs [b] u
                                FStar_Pervasives_Native.None
                               in
                            FStar_Syntax_Util.mk_letbinding
                              (FStar_Util.Inl bv) [] uu____4574
                              FStar_Parser_Const.effect_Tot_lid uu____4577 []
                              FStar_Range.dummyRange
                             in
                          let body = FStar_Syntax_Syntax.bv_to_name bv  in
                          let uu____4595 =
                            FStar_Syntax_Subst.close_let_rec [lb] body  in
                          (match uu____4595 with
                           | (lbs,body1) ->
                               let tm =
                                 let uu____4617 =
                                   let uu____4618 =
                                     FStar_Tactics_Types.goal_witness goal
                                      in
                                   uu____4618.FStar_Syntax_Syntax.pos  in
                                 FStar_Syntax_Syntax.mk
                                   (FStar_Syntax_Syntax.Tm_let
                                      ((true, lbs), body1))
                                   FStar_Pervasives_Native.None uu____4617
                                  in
                               let uu____4634 = set_solution goal tm  in
                               bind uu____4634
                                 (fun uu____4643  ->
                                    let uu____4644 =
                                      let uu____4647 =
                                        bnorm_goal
                                          (let uu___730_4650 = goal  in
                                           {
                                             FStar_Tactics_Types.goal_main_env
                                               =
                                               (uu___730_4650.FStar_Tactics_Types.goal_main_env);
                                             FStar_Tactics_Types.goal_ctx_uvar
                                               = ctx_uvar_u;
                                             FStar_Tactics_Types.opts =
                                               (uu___730_4650.FStar_Tactics_Types.opts);
                                             FStar_Tactics_Types.is_guard =
                                               (uu___730_4650.FStar_Tactics_Types.is_guard);
                                             FStar_Tactics_Types.label =
                                               (uu___730_4650.FStar_Tactics_Types.label)
                                           })
                                         in
                                      replace_cur uu____4647  in
                                    bind uu____4644
                                      (fun uu____4657  ->
                                         let uu____4658 =
                                           let uu____4663 =
                                             FStar_Syntax_Syntax.mk_binder bv
                                              in
                                           (uu____4663, b)  in
                                         ret uu____4658)))))
          | FStar_Pervasives_Native.None  ->
              let uu____4672 =
                let uu____4674 = FStar_Tactics_Types.goal_env goal  in
                let uu____4675 = FStar_Tactics_Types.goal_type goal  in
                tts uu____4674 uu____4675  in
              fail1 "intro_rec: goal is not an arrow (%s)" uu____4672))
  
let (norm : FStar_Syntax_Embeddings.norm_step Prims.list -> unit tac) =
  fun s  ->
    let uu____4695 = cur_goal ()  in
    bind uu____4695
      (fun goal  ->
         mlog
           (fun uu____4702  ->
              let uu____4703 =
                let uu____4705 = FStar_Tactics_Types.goal_witness goal  in
                FStar_Syntax_Print.term_to_string uu____4705  in
              FStar_Util.print1 "norm: witness = %s\n" uu____4703)
           (fun uu____4711  ->
              let steps =
                let uu____4715 = FStar_TypeChecker_Normalize.tr_norm_steps s
                   in
                FStar_List.append
                  [FStar_TypeChecker_Env.Reify;
                  FStar_TypeChecker_Env.UnfoldTac] uu____4715
                 in
              let t =
                let uu____4719 = FStar_Tactics_Types.goal_env goal  in
                let uu____4720 = FStar_Tactics_Types.goal_type goal  in
                normalize steps uu____4719 uu____4720  in
              let uu____4721 = FStar_Tactics_Types.goal_with_type goal t  in
              replace_cur uu____4721))
  
let (norm_term_env :
  env ->
    FStar_Syntax_Embeddings.norm_step Prims.list ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term tac)
  =
  fun e  ->
    fun s  ->
      fun t  ->
        let uu____4746 =
          bind get
            (fun ps  ->
               let opts =
                 match ps.FStar_Tactics_Types.goals with
                 | g::uu____4754 -> g.FStar_Tactics_Types.opts
                 | uu____4757 -> FStar_Options.peek ()  in
               mlog
                 (fun uu____4762  ->
                    let uu____4763 = FStar_Syntax_Print.term_to_string t  in
                    FStar_Util.print1 "norm_term_env: t = %s\n" uu____4763)
                 (fun uu____4768  ->
                    let uu____4769 = __tc_lax e t  in
                    bind uu____4769
                      (fun uu____4790  ->
                         match uu____4790 with
                         | (t1,uu____4800,uu____4801) ->
                             let steps =
                               let uu____4805 =
                                 FStar_TypeChecker_Normalize.tr_norm_steps s
                                  in
                               FStar_List.append
                                 [FStar_TypeChecker_Env.Reify;
                                 FStar_TypeChecker_Env.UnfoldTac] uu____4805
                                in
                             let t2 =
                               normalize steps
                                 ps.FStar_Tactics_Types.main_context t1
                                in
                             mlog
                               (fun uu____4811  ->
                                  let uu____4812 =
                                    FStar_Syntax_Print.term_to_string t2  in
                                  FStar_Util.print1
                                    "norm_term_env: t' = %s\n" uu____4812)
                               (fun uu____4816  -> ret t2))))
           in
        FStar_All.pipe_left (wrap_err "norm_term") uu____4746
  
let (refine_intro : unit -> unit tac) =
  fun uu____4829  ->
    let uu____4832 =
      let uu____4835 = cur_goal ()  in
      bind uu____4835
        (fun g  ->
           let uu____4842 =
             let uu____4853 = FStar_Tactics_Types.goal_env g  in
             let uu____4854 = FStar_Tactics_Types.goal_type g  in
             FStar_TypeChecker_Rel.base_and_refinement uu____4853 uu____4854
              in
           match uu____4842 with
           | (uu____4857,FStar_Pervasives_Native.None ) ->
               fail "not a refinement"
           | (t,FStar_Pervasives_Native.Some (bv,phi)) ->
               let g1 = FStar_Tactics_Types.goal_with_type g t  in
               let uu____4883 =
                 let uu____4888 =
                   let uu____4893 =
                     let uu____4894 = FStar_Syntax_Syntax.mk_binder bv  in
                     [uu____4894]  in
                   FStar_Syntax_Subst.open_term uu____4893 phi  in
                 match uu____4888 with
                 | (bvs,phi1) ->
                     let uu____4919 =
                       let uu____4920 = FStar_List.hd bvs  in
                       FStar_Pervasives_Native.fst uu____4920  in
                     (uu____4919, phi1)
                  in
               (match uu____4883 with
                | (bv1,phi1) ->
                    let uu____4939 =
                      let uu____4942 = FStar_Tactics_Types.goal_env g  in
                      let uu____4943 =
                        let uu____4944 =
                          let uu____4947 =
                            let uu____4948 =
                              let uu____4955 =
                                FStar_Tactics_Types.goal_witness g  in
                              (bv1, uu____4955)  in
                            FStar_Syntax_Syntax.NT uu____4948  in
                          [uu____4947]  in
                        FStar_Syntax_Subst.subst uu____4944 phi1  in
                      mk_irrelevant_goal "refine_intro refinement" uu____4942
                        uu____4943 g.FStar_Tactics_Types.opts
                        g.FStar_Tactics_Types.label
                       in
                    bind uu____4939
                      (fun g2  ->
                         bind __dismiss
                           (fun uu____4964  -> add_goals [g1; g2]))))
       in
    FStar_All.pipe_left (wrap_err "refine_intro") uu____4832
  
let (__exact_now : Prims.bool -> FStar_Syntax_Syntax.term -> unit tac) =
  fun set_expected_typ1  ->
    fun t  ->
      let uu____4987 = cur_goal ()  in
      bind uu____4987
        (fun goal  ->
           let env =
             if set_expected_typ1
             then
               let uu____4996 = FStar_Tactics_Types.goal_env goal  in
               let uu____4997 = FStar_Tactics_Types.goal_type goal  in
               FStar_TypeChecker_Env.set_expected_typ uu____4996 uu____4997
             else FStar_Tactics_Types.goal_env goal  in
           let uu____5000 = __tc env t  in
           bind uu____5000
             (fun uu____5019  ->
                match uu____5019 with
                | (t1,typ,guard) ->
                    mlog
                      (fun uu____5034  ->
                         let uu____5035 =
                           FStar_Syntax_Print.term_to_string typ  in
                         let uu____5037 =
                           let uu____5039 = FStar_Tactics_Types.goal_env goal
                              in
                           FStar_TypeChecker_Rel.guard_to_string uu____5039
                             guard
                            in
                         FStar_Util.print2
                           "__exact_now: got type %s\n__exact_now: and guard %s\n"
                           uu____5035 uu____5037)
                      (fun uu____5043  ->
                         let uu____5044 =
                           let uu____5047 = FStar_Tactics_Types.goal_env goal
                              in
                           proc_guard "__exact typing" uu____5047 guard  in
                         bind uu____5044
                           (fun uu____5050  ->
                              mlog
                                (fun uu____5054  ->
                                   let uu____5055 =
                                     FStar_Syntax_Print.term_to_string typ
                                      in
                                   let uu____5057 =
                                     let uu____5059 =
                                       FStar_Tactics_Types.goal_type goal  in
                                     FStar_Syntax_Print.term_to_string
                                       uu____5059
                                      in
                                   FStar_Util.print2
                                     "__exact_now: unifying %s and %s\n"
                                     uu____5055 uu____5057)
                                (fun uu____5063  ->
                                   let uu____5064 =
                                     let uu____5068 =
                                       FStar_Tactics_Types.goal_env goal  in
                                     let uu____5069 =
                                       FStar_Tactics_Types.goal_type goal  in
                                     do_unify uu____5068 typ uu____5069  in
                                   bind uu____5064
                                     (fun b  ->
                                        if b
                                        then solve goal t1
                                        else
                                          (let uu____5079 =
                                             let uu____5086 =
                                               let uu____5092 =
                                                 FStar_Tactics_Types.goal_env
                                                   goal
                                                  in
                                               tts uu____5092  in
                                             let uu____5093 =
                                               FStar_Tactics_Types.goal_type
                                                 goal
                                                in
                                             FStar_TypeChecker_Err.print_discrepancy
                                               uu____5086 typ uu____5093
                                              in
                                           match uu____5079 with
                                           | (typ1,goalt) ->
                                               let uu____5102 =
                                                 let uu____5104 =
                                                   FStar_Tactics_Types.goal_env
                                                     goal
                                                    in
                                                 tts uu____5104 t1  in
                                               let uu____5105 =
                                                 let uu____5107 =
                                                   FStar_Tactics_Types.goal_env
                                                     goal
                                                    in
                                                 let uu____5108 =
                                                   FStar_Tactics_Types.goal_witness
                                                     goal
                                                    in
                                                 tts uu____5107 uu____5108
                                                  in
                                               fail4
                                                 "%s : %s does not exactly solve the goal %s (witness = %s)"
                                                 uu____5102 typ1 goalt
                                                 uu____5105)))))))
  
let (t_exact :
  Prims.bool -> Prims.bool -> FStar_Syntax_Syntax.term -> unit tac) =
  fun try_refine  ->
    fun set_expected_typ1  ->
      fun tm  ->
        let uu____5134 =
          mlog
            (fun uu____5139  ->
               let uu____5140 = FStar_Syntax_Print.term_to_string tm  in
               FStar_Util.print1 "t_exact: tm = %s\n" uu____5140)
            (fun uu____5145  ->
               let uu____5146 =
                 let uu____5153 = __exact_now set_expected_typ1 tm  in
                 catch uu____5153  in
               bind uu____5146
                 (fun uu___2_5162  ->
                    match uu___2_5162 with
                    | FStar_Util.Inr r -> ret ()
                    | FStar_Util.Inl e when Prims.op_Negation try_refine ->
                        traise e
                    | FStar_Util.Inl e ->
                        mlog
                          (fun uu____5173  ->
                             FStar_Util.print_string
                               "__exact_now failed, trying refine...\n")
                          (fun uu____5177  ->
                             let uu____5178 =
                               let uu____5185 =
                                 let uu____5188 =
                                   norm [FStar_Syntax_Embeddings.Delta]  in
                                 bind uu____5188
                                   (fun uu____5193  ->
                                      let uu____5194 = refine_intro ()  in
                                      bind uu____5194
                                        (fun uu____5198  ->
                                           __exact_now set_expected_typ1 tm))
                                  in
                               catch uu____5185  in
                             bind uu____5178
                               (fun uu___1_5205  ->
                                  match uu___1_5205 with
                                  | FStar_Util.Inr r ->
                                      mlog
                                        (fun uu____5214  ->
                                           FStar_Util.print_string
                                             "__exact_now: failed after refining too\n")
                                        (fun uu____5217  -> ret ())
                                  | FStar_Util.Inl uu____5218 ->
                                      mlog
                                        (fun uu____5220  ->
                                           FStar_Util.print_string
                                             "__exact_now: was not a refinement\n")
                                        (fun uu____5223  -> traise e)))))
           in
        FStar_All.pipe_left (wrap_err "exact") uu____5134
  
let rec mapM : 'a 'b . ('a -> 'b tac) -> 'a Prims.list -> 'b Prims.list tac =
  fun f  ->
    fun l  ->
      match l with
      | [] -> ret []
      | x::xs ->
          let uu____5275 = f x  in
          bind uu____5275
            (fun y  ->
               let uu____5283 = mapM f xs  in
               bind uu____5283 (fun ys  -> ret (y :: ys)))
  
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
            let uu____5393 = f e ty2 ty1  in
            bind uu____5393
              (fun uu___3_5407  ->
                 if uu___3_5407
                 then ret acc
                 else
                   (let uu____5427 = FStar_Syntax_Util.arrow_one ty1  in
                    match uu____5427 with
                    | FStar_Pervasives_Native.None  ->
                        let uu____5448 =
                          FStar_Syntax_Print.term_to_string ty1  in
                        let uu____5450 =
                          FStar_Syntax_Print.term_to_string ty2  in
                        fail2 "Could not instantiate, %s to %s" uu____5448
                          uu____5450
                    | FStar_Pervasives_Native.Some (b,c) ->
                        let uu____5467 =
                          let uu____5469 = FStar_Syntax_Util.is_total_comp c
                             in
                          Prims.op_Negation uu____5469  in
                        if uu____5467
                        then fail "Codomain is effectful"
                        else
                          (let uu____5493 =
                             new_uvar "apply arg" e
                               (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                              in
                           bind uu____5493
                             (fun uu____5520  ->
                                match uu____5520 with
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
        let uu____5626 =
          mlog
            (fun uu____5631  ->
               let uu____5632 = FStar_Syntax_Print.term_to_string tm  in
               FStar_Util.print1 "t_apply: tm = %s\n" uu____5632)
            (fun uu____5637  ->
               let uu____5638 = cur_goal ()  in
               bind uu____5638
                 (fun goal  ->
                    let e = FStar_Tactics_Types.goal_env goal  in
                    let uu____5646 = __tc e tm  in
                    bind uu____5646
                      (fun uu____5667  ->
                         match uu____5667 with
                         | (tm1,typ,guard) ->
                             let typ1 = bnorm e typ  in
                             let uu____5680 =
                               let uu____5691 =
                                 FStar_Tactics_Types.goal_type goal  in
                               try_unify_by_application only_match e typ1
                                 uu____5691
                                in
                             bind uu____5680
                               (fun uvs  ->
                                  mlog
                                    (fun uu____5712  ->
                                       let uu____5713 =
                                         FStar_Common.string_of_list
                                           (fun uu____5725  ->
                                              match uu____5725 with
                                              | (t,uu____5734,uu____5735) ->
                                                  FStar_Syntax_Print.term_to_string
                                                    t) uvs
                                          in
                                       FStar_Util.print1
                                         "t_apply: found args = %s\n"
                                         uu____5713)
                                    (fun uu____5743  ->
                                       let fix_qual q =
                                         match q with
                                         | FStar_Pervasives_Native.Some
                                             (FStar_Syntax_Syntax.Meta
                                             uu____5758) ->
                                             FStar_Pervasives_Native.Some
                                               (FStar_Syntax_Syntax.Implicit
                                                  false)
                                         | uu____5762 -> q  in
                                       let w =
                                         FStar_List.fold_right
                                           (fun uu____5785  ->
                                              fun w  ->
                                                match uu____5785 with
                                                | (uvt,q,uu____5803) ->
                                                    FStar_Syntax_Util.mk_app
                                                      w [(uvt, (fix_qual q))])
                                           uvs tm1
                                          in
                                       let uvset =
                                         let uu____5835 =
                                           FStar_Syntax_Free.new_uv_set ()
                                            in
                                         FStar_List.fold_right
                                           (fun uu____5852  ->
                                              fun s  ->
                                                match uu____5852 with
                                                | (uu____5864,uu____5865,uv)
                                                    ->
                                                    let uu____5867 =
                                                      FStar_Syntax_Free.uvars
                                                        uv.FStar_Syntax_Syntax.ctx_uvar_typ
                                                       in
                                                    FStar_Util.set_union s
                                                      uu____5867) uvs
                                           uu____5835
                                          in
                                       let free_in_some_goal uv =
                                         FStar_Util.set_mem uv uvset  in
                                       let uu____5877 = solve' goal w  in
                                       bind uu____5877
                                         (fun uu____5882  ->
                                            let uu____5883 =
                                              mapM
                                                (fun uu____5900  ->
                                                   match uu____5900 with
                                                   | (uvt,q,uv) ->
                                                       let uu____5912 =
                                                         FStar_Syntax_Unionfind.find
                                                           uv.FStar_Syntax_Syntax.ctx_uvar_head
                                                          in
                                                       (match uu____5912 with
                                                        | FStar_Pervasives_Native.Some
                                                            uu____5917 ->
                                                            ret ()
                                                        | FStar_Pervasives_Native.None
                                                             ->
                                                            let uu____5918 =
                                                              uopt &&
                                                                (free_in_some_goal
                                                                   uv)
                                                               in
                                                            if uu____5918
                                                            then ret ()
                                                            else
                                                              (let uu____5925
                                                                 =
                                                                 let uu____5928
                                                                   =
                                                                   bnorm_goal
                                                                    (let uu___900_5931
                                                                    = goal
                                                                     in
                                                                    {
                                                                    FStar_Tactics_Types.goal_main_env
                                                                    =
                                                                    (uu___900_5931.FStar_Tactics_Types.goal_main_env);
                                                                    FStar_Tactics_Types.goal_ctx_uvar
                                                                    = uv;
                                                                    FStar_Tactics_Types.opts
                                                                    =
                                                                    (uu___900_5931.FStar_Tactics_Types.opts);
                                                                    FStar_Tactics_Types.is_guard
                                                                    = false;
                                                                    FStar_Tactics_Types.label
                                                                    =
                                                                    (uu___900_5931.FStar_Tactics_Types.label)
                                                                    })
                                                                    in
                                                                 [uu____5928]
                                                                  in
                                                               add_goals
                                                                 uu____5925)))
                                                uvs
                                               in
                                            bind uu____5883
                                              (fun uu____5936  ->
                                                 proc_guard "apply guard" e
                                                   guard)))))))
           in
        FStar_All.pipe_left (wrap_err "apply") uu____5626
  
let (lemma_or_sq :
  FStar_Syntax_Syntax.comp ->
    (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.option)
  =
  fun c  ->
    let ct = FStar_Syntax_Util.comp_to_comp_typ_nouniv c  in
    let uu____5964 =
      FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
        FStar_Parser_Const.effect_Lemma_lid
       in
    if uu____5964
    then
      let uu____5973 =
        match ct.FStar_Syntax_Syntax.effect_args with
        | pre::post::uu____5988 ->
            ((FStar_Pervasives_Native.fst pre),
              (FStar_Pervasives_Native.fst post))
        | uu____6041 -> failwith "apply_lemma: impossible: not a lemma"  in
      match uu____5973 with
      | (pre,post) ->
          let post1 =
            let uu____6074 =
              let uu____6085 =
                FStar_Syntax_Syntax.as_arg FStar_Syntax_Util.exp_unit  in
              [uu____6085]  in
            FStar_Syntax_Util.mk_app post uu____6074  in
          FStar_Pervasives_Native.Some (pre, post1)
    else
      (let uu____6116 =
         FStar_Syntax_Util.is_pure_effect ct.FStar_Syntax_Syntax.effect_name
          in
       if uu____6116
       then
         let uu____6125 =
           FStar_Syntax_Util.un_squash ct.FStar_Syntax_Syntax.result_typ  in
         FStar_Util.map_opt uu____6125
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
            let uu____6204 = f x e  in
            bind uu____6204 (fun e'  -> fold_left f e' xs1)
  
let (apply_lemma : FStar_Syntax_Syntax.term -> unit tac) =
  fun tm  ->
    let uu____6219 =
      let uu____6222 =
        bind get
          (fun ps  ->
             mlog
               (fun uu____6229  ->
                  let uu____6230 = FStar_Syntax_Print.term_to_string tm  in
                  FStar_Util.print1 "apply_lemma: tm = %s\n" uu____6230)
               (fun uu____6236  ->
                  let is_unit_t t =
                    let uu____6244 =
                      let uu____6245 = FStar_Syntax_Subst.compress t  in
                      uu____6245.FStar_Syntax_Syntax.n  in
                    match uu____6244 with
                    | FStar_Syntax_Syntax.Tm_fvar fv when
                        FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.unit_lid
                        -> true
                    | uu____6251 -> false  in
                  let uu____6253 = cur_goal ()  in
                  bind uu____6253
                    (fun goal  ->
                       let uu____6259 =
                         let uu____6268 = FStar_Tactics_Types.goal_env goal
                            in
                         __tc uu____6268 tm  in
                       bind uu____6259
                         (fun uu____6283  ->
                            match uu____6283 with
                            | (tm1,t,guard) ->
                                let uu____6295 =
                                  FStar_Syntax_Util.arrow_formals_comp t  in
                                (match uu____6295 with
                                 | (bs,comp) ->
                                     let uu____6304 = lemma_or_sq comp  in
                                     (match uu____6304 with
                                      | FStar_Pervasives_Native.None  ->
                                          fail
                                            "not a lemma or squashed function"
                                      | FStar_Pervasives_Native.Some
                                          (pre,post) ->
                                          let uu____6324 =
                                            fold_left
                                              (fun uu____6386  ->
                                                 fun uu____6387  ->
                                                   match (uu____6386,
                                                           uu____6387)
                                                   with
                                                   | ((b,aq),(uvs,imps,subst1))
                                                       ->
                                                       let b_t =
                                                         FStar_Syntax_Subst.subst
                                                           subst1
                                                           b.FStar_Syntax_Syntax.sort
                                                          in
                                                       let uu____6538 =
                                                         is_unit_t b_t  in
                                                       if uu____6538
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
                                                         (let uu____6661 =
                                                            let uu____6668 =
                                                              FStar_Tactics_Types.goal_env
                                                                goal
                                                               in
                                                            new_uvar
                                                              "apply_lemma"
                                                              uu____6668 b_t
                                                             in
                                                          bind uu____6661
                                                            (fun uu____6699 
                                                               ->
                                                               match uu____6699
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
                                          bind uu____6324
                                            (fun uu____6885  ->
                                               match uu____6885 with
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
                                                   let uu____6973 =
                                                     let uu____6977 =
                                                       FStar_Tactics_Types.goal_env
                                                         goal
                                                        in
                                                     let uu____6978 =
                                                       FStar_Syntax_Util.mk_squash
                                                         FStar_Syntax_Syntax.U_zero
                                                         post1
                                                        in
                                                     let uu____6979 =
                                                       FStar_Tactics_Types.goal_type
                                                         goal
                                                        in
                                                     do_unify uu____6977
                                                       uu____6978 uu____6979
                                                      in
                                                   bind uu____6973
                                                     (fun b  ->
                                                        if
                                                          Prims.op_Negation b
                                                        then
                                                          let uu____6991 =
                                                            let uu____6998 =
                                                              let uu____7004
                                                                =
                                                                FStar_Tactics_Types.goal_env
                                                                  goal
                                                                 in
                                                              tts uu____7004
                                                               in
                                                            let uu____7005 =
                                                              FStar_Syntax_Util.mk_squash
                                                                FStar_Syntax_Syntax.U_zero
                                                                post1
                                                               in
                                                            let uu____7006 =
                                                              FStar_Tactics_Types.goal_type
                                                                goal
                                                               in
                                                            FStar_TypeChecker_Err.print_discrepancy
                                                              uu____6998
                                                              uu____7005
                                                              uu____7006
                                                             in
                                                          match uu____6991
                                                          with
                                                          | (post2,goalt) ->
                                                              let uu____7015
                                                                =
                                                                let uu____7017
                                                                  =
                                                                  FStar_Tactics_Types.goal_env
                                                                    goal
                                                                   in
                                                                tts
                                                                  uu____7017
                                                                  tm1
                                                                 in
                                                              fail3
                                                                "Cannot instantiate lemma %s (with postcondition: %s) to match goal (%s)"
                                                                uu____7015
                                                                post2 goalt
                                                        else
                                                          (let uu____7021 =
                                                             solve' goal
                                                               FStar_Syntax_Util.exp_unit
                                                              in
                                                           bind uu____7021
                                                             (fun uu____7029 
                                                                ->
                                                                let is_free_uvar
                                                                  uv t1 =
                                                                  let free_uvars
                                                                    =
                                                                    let uu____7055
                                                                    =
                                                                    let uu____7058
                                                                    =
                                                                    FStar_Syntax_Free.uvars
                                                                    t1  in
                                                                    FStar_Util.set_elements
                                                                    uu____7058
                                                                     in
                                                                    FStar_List.map
                                                                    (fun x 
                                                                    ->
                                                                    x.FStar_Syntax_Syntax.ctx_uvar_head)
                                                                    uu____7055
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
                                                                    let uu____7094
                                                                    =
                                                                    FStar_Tactics_Types.goal_type
                                                                    g'  in
                                                                    is_free_uvar
                                                                    uv
                                                                    uu____7094)
                                                                    goals
                                                                   in
                                                                let checkone
                                                                  t1 goals =
                                                                  let uu____7111
                                                                    =
                                                                    FStar_Syntax_Util.head_and_args
                                                                    t1  in
                                                                  match uu____7111
                                                                  with
                                                                  | (hd1,uu____7130)
                                                                    ->
                                                                    (match 
                                                                    hd1.FStar_Syntax_Syntax.n
                                                                    with
                                                                    | 
                                                                    FStar_Syntax_Syntax.Tm_uvar
                                                                    (uv,uu____7157)
                                                                    ->
                                                                    appears
                                                                    uv.FStar_Syntax_Syntax.ctx_uvar_head
                                                                    goals
                                                                    | 
                                                                    uu____7174
                                                                    -> false)
                                                                   in
                                                                let uu____7176
                                                                  =
                                                                  FStar_All.pipe_right
                                                                    implicits1
                                                                    (
                                                                    mapM
                                                                    (fun imp 
                                                                    ->
                                                                    let uu____7217
                                                                    = imp  in
                                                                    match uu____7217
                                                                    with
                                                                    | 
                                                                    (term,ctx_uvar)
                                                                    ->
                                                                    let uu____7228
                                                                    =
                                                                    FStar_Syntax_Util.head_and_args
                                                                    term  in
                                                                    (match uu____7228
                                                                    with
                                                                    | 
                                                                    (hd1,uu____7250)
                                                                    ->
                                                                    let uu____7275
                                                                    =
                                                                    let uu____7276
                                                                    =
                                                                    FStar_Syntax_Subst.compress
                                                                    hd1  in
                                                                    uu____7276.FStar_Syntax_Syntax.n
                                                                     in
                                                                    (match uu____7275
                                                                    with
                                                                    | 
                                                                    FStar_Syntax_Syntax.Tm_uvar
                                                                    (ctx_uvar1,uu____7284)
                                                                    ->
                                                                    let goal1
                                                                    =
                                                                    bnorm_goal
                                                                    (let uu___1017_7304
                                                                    = goal
                                                                     in
                                                                    {
                                                                    FStar_Tactics_Types.goal_main_env
                                                                    =
                                                                    (uu___1017_7304.FStar_Tactics_Types.goal_main_env);
                                                                    FStar_Tactics_Types.goal_ctx_uvar
                                                                    =
                                                                    ctx_uvar1;
                                                                    FStar_Tactics_Types.opts
                                                                    =
                                                                    (uu___1017_7304.FStar_Tactics_Types.opts);
                                                                    FStar_Tactics_Types.is_guard
                                                                    =
                                                                    (uu___1017_7304.FStar_Tactics_Types.is_guard);
                                                                    FStar_Tactics_Types.label
                                                                    =
                                                                    (uu___1017_7304.FStar_Tactics_Types.label)
                                                                    })  in
                                                                    ret
                                                                    [goal1]
                                                                    | 
                                                                    uu____7307
                                                                    ->
                                                                    mlog
                                                                    (fun
                                                                    uu____7313
                                                                     ->
                                                                    let uu____7314
                                                                    =
                                                                    FStar_Syntax_Print.uvar_to_string
                                                                    ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_head
                                                                     in
                                                                    let uu____7316
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    term  in
                                                                    FStar_Util.print2
                                                                    "apply_lemma: arg %s unified to (%s)\n"
                                                                    uu____7314
                                                                    uu____7316)
                                                                    (fun
                                                                    uu____7322
                                                                     ->
                                                                    let g_typ
                                                                    =
                                                                    let uu____7324
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    goal  in
                                                                    FStar_TypeChecker_TcTerm.check_type_of_well_typed_term'
                                                                    true
                                                                    uu____7324
                                                                    term
                                                                    ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_typ
                                                                     in
                                                                    let uu____7326
                                                                    =
                                                                    let uu____7329
                                                                    =
                                                                    if
                                                                    ps.FStar_Tactics_Types.tac_verb_dbg
                                                                    then
                                                                    let uu____7333
                                                                    =
                                                                    FStar_Syntax_Print.ctx_uvar_to_string
                                                                    ctx_uvar
                                                                     in
                                                                    let uu____7335
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    term  in
                                                                    FStar_Util.format2
                                                                    "apply_lemma solved arg %s to %s\n"
                                                                    uu____7333
                                                                    uu____7335
                                                                    else
                                                                    "apply_lemma solved arg"
                                                                     in
                                                                    let uu____7341
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    goal  in
                                                                    proc_guard
                                                                    uu____7329
                                                                    uu____7341
                                                                    g_typ  in
                                                                    bind
                                                                    uu____7326
                                                                    (fun
                                                                    uu____7345
                                                                     ->
                                                                    ret []))))))
                                                                   in
                                                                bind
                                                                  uu____7176
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
                                                                    let uu____7409
                                                                    = f x xs1
                                                                     in
                                                                    if
                                                                    uu____7409
                                                                    then
                                                                    let uu____7414
                                                                    =
                                                                    filter' f
                                                                    xs1  in x
                                                                    ::
                                                                    uu____7414
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
                                                                    let uu____7429
                                                                    =
                                                                    let uu____7431
                                                                    =
                                                                    FStar_Tactics_Types.goal_witness
                                                                    g  in
                                                                    checkone
                                                                    uu____7431
                                                                    goals  in
                                                                    Prims.op_Negation
                                                                    uu____7429)
                                                                    sub_goals1
                                                                     in
                                                                    let uu____7432
                                                                    =
                                                                    let uu____7435
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    goal  in
                                                                    proc_guard
                                                                    "apply_lemma guard"
                                                                    uu____7435
                                                                    guard  in
                                                                    bind
                                                                    uu____7432
                                                                    (fun
                                                                    uu____7439
                                                                     ->
                                                                    let uu____7440
                                                                    =
                                                                    let uu____7443
                                                                    =
                                                                    let uu____7445
                                                                    =
                                                                    let uu____7447
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    goal  in
                                                                    let uu____7448
                                                                    =
                                                                    FStar_Syntax_Util.mk_squash
                                                                    FStar_Syntax_Syntax.U_zero
                                                                    pre1  in
                                                                    istrivial
                                                                    uu____7447
                                                                    uu____7448
                                                                     in
                                                                    Prims.op_Negation
                                                                    uu____7445
                                                                     in
                                                                    if
                                                                    uu____7443
                                                                    then
                                                                    let uu____7452
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    goal  in
                                                                    add_irrelevant_goal
                                                                    "apply_lemma precondition"
                                                                    uu____7452
                                                                    pre1
                                                                    goal.FStar_Tactics_Types.opts
                                                                    goal.FStar_Tactics_Types.label
                                                                    else
                                                                    ret ()
                                                                     in
                                                                    bind
                                                                    uu____7440
                                                                    (fun
                                                                    uu____7457
                                                                     ->
                                                                    add_goals
                                                                    sub_goals2)))))))))))))
         in
      focus uu____6222  in
    FStar_All.pipe_left (wrap_err "apply_lemma") uu____6219
  
let (destruct_eq' :
  FStar_Reflection_Data.typ ->
    (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.option)
  =
  fun typ  ->
    let uu____7481 = FStar_Syntax_Util.destruct_typ_as_formula typ  in
    match uu____7481 with
    | FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn
        (l,uu____7491::(e1,FStar_Pervasives_Native.None )::(e2,FStar_Pervasives_Native.None
                                                            )::[]))
        when
        (FStar_Ident.lid_equals l FStar_Parser_Const.eq2_lid) ||
          (FStar_Ident.lid_equals l FStar_Parser_Const.c_eq2_lid)
        -> FStar_Pervasives_Native.Some (e1, e2)
    | FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn
        (l,uu____7551::uu____7552::(e1,uu____7554)::(e2,uu____7556)::[]))
        when FStar_Ident.lid_equals l FStar_Parser_Const.eq3_lid ->
        FStar_Pervasives_Native.Some (e1, e2)
    | uu____7633 ->
        let uu____7636 = FStar_Syntax_Util.unb2t typ  in
        (match uu____7636 with
         | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
         | FStar_Pervasives_Native.Some t ->
             let uu____7650 = FStar_Syntax_Util.head_and_args t  in
             (match uu____7650 with
              | (hd1,args) ->
                  let uu____7699 =
                    let uu____7714 =
                      let uu____7715 = FStar_Syntax_Subst.compress hd1  in
                      uu____7715.FStar_Syntax_Syntax.n  in
                    (uu____7714, args)  in
                  (match uu____7699 with
                   | (FStar_Syntax_Syntax.Tm_fvar
                      fv,(uu____7735,FStar_Pervasives_Native.Some
                          (FStar_Syntax_Syntax.Implicit uu____7736))::
                      (e1,FStar_Pervasives_Native.None )::(e2,FStar_Pervasives_Native.None
                                                           )::[])
                       when
                       FStar_Syntax_Syntax.fv_eq_lid fv
                         FStar_Parser_Const.op_Eq
                       -> FStar_Pervasives_Native.Some (e1, e2)
                   | uu____7804 -> FStar_Pervasives_Native.None)))
  
let (destruct_eq :
  FStar_Reflection_Data.typ ->
    (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.option)
  =
  fun typ  ->
    let uu____7841 = destruct_eq' typ  in
    match uu____7841 with
    | FStar_Pervasives_Native.Some t -> FStar_Pervasives_Native.Some t
    | FStar_Pervasives_Native.None  ->
        let uu____7871 = FStar_Syntax_Util.un_squash typ  in
        (match uu____7871 with
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
        let uu____7940 = FStar_TypeChecker_Env.pop_bv e1  in
        match uu____7940 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (bv',e') ->
            if FStar_Syntax_Syntax.bv_eq bvar bv'
            then FStar_Pervasives_Native.Some (e', bv', [])
            else
              (let uu____7998 = aux e'  in
               FStar_Util.map_opt uu____7998
                 (fun uu____8029  ->
                    match uu____8029 with
                    | (e'',bv,bvs) -> (e'', bv, (bv' :: bvs))))
         in
      let uu____8055 = aux e  in
      FStar_Util.map_opt uu____8055
        (fun uu____8086  ->
           match uu____8086 with
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
      FStar_Tactics_Types.goal ->
        (FStar_Syntax_Syntax.bv * FStar_Tactics_Types.goal)
          FStar_Pervasives_Native.option tac)
  =
  fun b1  ->
    fun b2  ->
      fun g  ->
        let uu____8163 =
          let uu____8174 = FStar_Tactics_Types.goal_env g  in
          split_env b1 uu____8174  in
        match uu____8163 with
        | FStar_Pervasives_Native.Some (e0,b11,bvs) ->
            let bs =
              FStar_List.map FStar_Syntax_Syntax.mk_binder (b11 :: bvs)  in
            let t = FStar_Tactics_Types.goal_type g  in
            let uu____8214 =
              let uu____8227 = FStar_Syntax_Subst.close_binders bs  in
              let uu____8236 = FStar_Syntax_Subst.close bs t  in
              (uu____8227, uu____8236)  in
            (match uu____8214 with
             | (bs',t') ->
                 let bs'1 =
                   let uu____8280 = FStar_Syntax_Syntax.mk_binder b2  in
                   let uu____8287 = FStar_List.tail bs'  in uu____8280 ::
                     uu____8287
                    in
                 let uu____8308 = FStar_Syntax_Subst.open_term bs'1 t'  in
                 (match uu____8308 with
                  | (bs'',t'') ->
                      let b21 =
                        let uu____8324 = FStar_List.hd bs''  in
                        FStar_Pervasives_Native.fst uu____8324  in
                      let new_env =
                        let uu____8340 =
                          FStar_List.map FStar_Pervasives_Native.fst bs''  in
                        push_bvs e0 uu____8340  in
                      let uu____8351 = new_uvar "subst_goal" new_env t''  in
                      bind uu____8351
                        (fun uu____8375  ->
                           match uu____8375 with
                           | (uvt,uv) ->
                               let goal' =
                                 FStar_Tactics_Types.mk_goal new_env uv
                                   g.FStar_Tactics_Types.opts
                                   g.FStar_Tactics_Types.is_guard
                                   g.FStar_Tactics_Types.label
                                  in
                               let sol =
                                 let uu____8394 =
                                   FStar_Syntax_Util.abs bs'' uvt
                                     FStar_Pervasives_Native.None
                                    in
                                 let uu____8397 =
                                   FStar_List.map
                                     (fun uu____8418  ->
                                        match uu____8418 with
                                        | (bv,q) ->
                                            let uu____8431 =
                                              FStar_Syntax_Syntax.bv_to_name
                                                bv
                                               in
                                            FStar_Syntax_Syntax.as_arg
                                              uu____8431) bs
                                    in
                                 FStar_Syntax_Util.mk_app uu____8394
                                   uu____8397
                                  in
                               let uu____8432 = set_solution g sol  in
                               bind uu____8432
                                 (fun uu____8442  ->
                                    ret
                                      (FStar_Pervasives_Native.Some
                                         (b21, goal'))))))
        | FStar_Pervasives_Native.None  -> ret FStar_Pervasives_Native.None
  
let (rewrite : FStar_Syntax_Syntax.binder -> unit tac) =
  fun h  ->
    let uu____8481 =
      let uu____8484 = cur_goal ()  in
      bind uu____8484
        (fun goal  ->
           let uu____8492 = h  in
           match uu____8492 with
           | (bv,uu____8496) ->
               mlog
                 (fun uu____8504  ->
                    let uu____8505 = FStar_Syntax_Print.bv_to_string bv  in
                    let uu____8507 =
                      FStar_Syntax_Print.term_to_string
                        bv.FStar_Syntax_Syntax.sort
                       in
                    FStar_Util.print2 "+++Rewrite %s : %s\n" uu____8505
                      uu____8507)
                 (fun uu____8512  ->
                    let uu____8513 =
                      let uu____8524 = FStar_Tactics_Types.goal_env goal  in
                      split_env bv uu____8524  in
                    match uu____8513 with
                    | FStar_Pervasives_Native.None  ->
                        fail "binder not found in environment"
                    | FStar_Pervasives_Native.Some (e0,bv1,bvs) ->
                        let uu____8551 =
                          destruct_eq bv1.FStar_Syntax_Syntax.sort  in
                        (match uu____8551 with
                         | FStar_Pervasives_Native.Some (x,e) ->
                             let uu____8566 =
                               let uu____8567 = FStar_Syntax_Subst.compress x
                                  in
                               uu____8567.FStar_Syntax_Syntax.n  in
                             (match uu____8566 with
                              | FStar_Syntax_Syntax.Tm_name x1 ->
                                  let s = [FStar_Syntax_Syntax.NT (x1, e)]
                                     in
                                  let t = FStar_Tactics_Types.goal_type goal
                                     in
                                  let bs =
                                    FStar_List.map
                                      FStar_Syntax_Syntax.mk_binder bvs
                                     in
                                  let uu____8594 =
                                    let uu____8599 =
                                      FStar_Syntax_Subst.close_binders bs  in
                                    let uu____8600 =
                                      FStar_Syntax_Subst.close bs t  in
                                    (uu____8599, uu____8600)  in
                                  (match uu____8594 with
                                   | (bs',t') ->
                                       let uu____8605 =
                                         let uu____8610 =
                                           FStar_Syntax_Subst.subst_binders s
                                             bs'
                                            in
                                         let uu____8611 =
                                           FStar_Syntax_Subst.subst s t  in
                                         (uu____8610, uu____8611)  in
                                       (match uu____8605 with
                                        | (bs'1,t'1) ->
                                            let uu____8616 =
                                              FStar_Syntax_Subst.open_term
                                                bs'1 t'1
                                               in
                                            (match uu____8616 with
                                             | (bs'',t'') ->
                                                 let new_env =
                                                   let uu____8626 =
                                                     let uu____8629 =
                                                       FStar_List.map
                                                         FStar_Pervasives_Native.fst
                                                         bs''
                                                        in
                                                     bv1 :: uu____8629  in
                                                   push_bvs e0 uu____8626  in
                                                 let uu____8640 =
                                                   new_uvar "rewrite" new_env
                                                     t''
                                                    in
                                                 bind uu____8640
                                                   (fun uu____8658  ->
                                                      match uu____8658 with
                                                      | (uvt,uv) ->
                                                          let goal' =
                                                            FStar_Tactics_Types.mk_goal
                                                              new_env uv
                                                              goal.FStar_Tactics_Types.opts
                                                              goal.FStar_Tactics_Types.is_guard
                                                              goal.FStar_Tactics_Types.label
                                                             in
                                                          let sol =
                                                            let uu____8671 =
                                                              FStar_Syntax_Util.abs
                                                                bs'' uvt
                                                                FStar_Pervasives_Native.None
                                                               in
                                                            let uu____8674 =
                                                              FStar_List.map
                                                                (fun
                                                                   uu____8695
                                                                    ->
                                                                   match uu____8695
                                                                   with
                                                                   | 
                                                                   (bv2,uu____8703)
                                                                    ->
                                                                    let uu____8708
                                                                    =
                                                                    FStar_Syntax_Syntax.bv_to_name
                                                                    bv2  in
                                                                    FStar_Syntax_Syntax.as_arg
                                                                    uu____8708)
                                                                bs
                                                               in
                                                            FStar_Syntax_Util.mk_app
                                                              uu____8671
                                                              uu____8674
                                                             in
                                                          let uu____8709 =
                                                            set_solution goal
                                                              sol
                                                             in
                                                          bind uu____8709
                                                            (fun uu____8713 
                                                               ->
                                                               replace_cur
                                                                 goal')))))
                              | uu____8714 ->
                                  fail
                                    "Not an equality hypothesis with a variable on the LHS")
                         | uu____8716 -> fail "Not an equality hypothesis")))
       in
    FStar_All.pipe_left (wrap_err "rewrite") uu____8481
  
let (rename_to :
  FStar_Syntax_Syntax.binder ->
    Prims.string -> FStar_Syntax_Syntax.binder tac)
  =
  fun b  ->
    fun s  ->
      let uu____8746 =
        let uu____8755 = cur_goal ()  in
        bind uu____8755
          (fun goal  ->
             let uu____8771 = b  in
             match uu____8771 with
             | (bv,q) ->
                 let bv' =
                   let uu____8787 =
                     let uu___1195_8788 = bv  in
                     let uu____8789 =
                       FStar_Ident.mk_ident
                         (s,
                           ((bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange))
                        in
                     {
                       FStar_Syntax_Syntax.ppname = uu____8789;
                       FStar_Syntax_Syntax.index =
                         (uu___1195_8788.FStar_Syntax_Syntax.index);
                       FStar_Syntax_Syntax.sort =
                         (uu___1195_8788.FStar_Syntax_Syntax.sort)
                     }  in
                   FStar_Syntax_Syntax.freshen_bv uu____8787  in
                 let uu____8791 = subst_goal bv bv' goal  in
                 bind uu____8791
                   (fun uu___4_8813  ->
                      match uu___4_8813 with
                      | FStar_Pervasives_Native.None  ->
                          fail "binder not found in environment"
                      | FStar_Pervasives_Native.Some (bv'1,goal1) ->
                          let uu____8845 = replace_cur goal1  in
                          bind uu____8845 (fun uu____8855  -> ret (bv'1, q))))
         in
      FStar_All.pipe_left (wrap_err "rename_to") uu____8746
  
let (binder_retype : FStar_Syntax_Syntax.binder -> unit tac) =
  fun b  ->
    let uu____8891 =
      let uu____8894 = cur_goal ()  in
      bind uu____8894
        (fun goal  ->
           let uu____8903 = b  in
           match uu____8903 with
           | (bv,uu____8907) ->
               let uu____8912 =
                 let uu____8923 = FStar_Tactics_Types.goal_env goal  in
                 split_env bv uu____8923  in
               (match uu____8912 with
                | FStar_Pervasives_Native.None  ->
                    fail "binder is not present in environment"
                | FStar_Pervasives_Native.Some (e0,bv1,bvs) ->
                    let uu____8950 = FStar_Syntax_Util.type_u ()  in
                    (match uu____8950 with
                     | (ty,u) ->
                         let uu____8959 = new_uvar "binder_retype" e0 ty  in
                         bind uu____8959
                           (fun uu____8978  ->
                              match uu____8978 with
                              | (t',u_t') ->
                                  let bv'' =
                                    let uu___1222_8988 = bv1  in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___1222_8988.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___1222_8988.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = t'
                                    }  in
                                  let s =
                                    let uu____8992 =
                                      let uu____8993 =
                                        let uu____9000 =
                                          FStar_Syntax_Syntax.bv_to_name bv''
                                           in
                                        (bv1, uu____9000)  in
                                      FStar_Syntax_Syntax.NT uu____8993  in
                                    [uu____8992]  in
                                  let bvs1 =
                                    FStar_List.map
                                      (fun b1  ->
                                         let uu___1227_9012 = b1  in
                                         let uu____9013 =
                                           FStar_Syntax_Subst.subst s
                                             b1.FStar_Syntax_Syntax.sort
                                            in
                                         {
                                           FStar_Syntax_Syntax.ppname =
                                             (uu___1227_9012.FStar_Syntax_Syntax.ppname);
                                           FStar_Syntax_Syntax.index =
                                             (uu___1227_9012.FStar_Syntax_Syntax.index);
                                           FStar_Syntax_Syntax.sort =
                                             uu____9013
                                         }) bvs
                                     in
                                  let env' = push_bvs e0 (bv'' :: bvs1)  in
                                  bind __dismiss
                                    (fun uu____9020  ->
                                       let new_goal =
                                         let uu____9022 =
                                           FStar_Tactics_Types.goal_with_env
                                             goal env'
                                            in
                                         let uu____9023 =
                                           let uu____9024 =
                                             FStar_Tactics_Types.goal_type
                                               goal
                                              in
                                           FStar_Syntax_Subst.subst s
                                             uu____9024
                                            in
                                         FStar_Tactics_Types.goal_with_type
                                           uu____9022 uu____9023
                                          in
                                       let uu____9025 = add_goals [new_goal]
                                          in
                                       bind uu____9025
                                         (fun uu____9030  ->
                                            let uu____9031 =
                                              FStar_Syntax_Util.mk_eq2
                                                (FStar_Syntax_Syntax.U_succ u)
                                                ty
                                                bv1.FStar_Syntax_Syntax.sort
                                                t'
                                               in
                                            add_irrelevant_goal
                                              "binder_retype equation" e0
                                              uu____9031
                                              goal.FStar_Tactics_Types.opts
                                              goal.FStar_Tactics_Types.label))))))
       in
    FStar_All.pipe_left (wrap_err "binder_retype") uu____8891
  
let (norm_binder_type :
  FStar_Syntax_Embeddings.norm_step Prims.list ->
    FStar_Syntax_Syntax.binder -> unit tac)
  =
  fun s  ->
    fun b  ->
      let uu____9057 =
        let uu____9060 = cur_goal ()  in
        bind uu____9060
          (fun goal  ->
             let uu____9069 = b  in
             match uu____9069 with
             | (bv,uu____9073) ->
                 let uu____9078 =
                   let uu____9089 = FStar_Tactics_Types.goal_env goal  in
                   split_env bv uu____9089  in
                 (match uu____9078 with
                  | FStar_Pervasives_Native.None  ->
                      fail "binder is not present in environment"
                  | FStar_Pervasives_Native.Some (e0,bv1,bvs) ->
                      let steps =
                        let uu____9119 =
                          FStar_TypeChecker_Normalize.tr_norm_steps s  in
                        FStar_List.append
                          [FStar_TypeChecker_Env.Reify;
                          FStar_TypeChecker_Env.UnfoldTac] uu____9119
                         in
                      let sort' =
                        normalize steps e0 bv1.FStar_Syntax_Syntax.sort  in
                      let bv' =
                        let uu___1248_9124 = bv1  in
                        {
                          FStar_Syntax_Syntax.ppname =
                            (uu___1248_9124.FStar_Syntax_Syntax.ppname);
                          FStar_Syntax_Syntax.index =
                            (uu___1248_9124.FStar_Syntax_Syntax.index);
                          FStar_Syntax_Syntax.sort = sort'
                        }  in
                      let env' = push_bvs e0 (bv' :: bvs)  in
                      let uu____9126 =
                        FStar_Tactics_Types.goal_with_env goal env'  in
                      replace_cur uu____9126))
         in
      FStar_All.pipe_left (wrap_err "norm_binder_type") uu____9057
  
let (revert : unit -> unit tac) =
  fun uu____9139  ->
    let uu____9142 = cur_goal ()  in
    bind uu____9142
      (fun goal  ->
         let uu____9148 =
           let uu____9155 = FStar_Tactics_Types.goal_env goal  in
           FStar_TypeChecker_Env.pop_bv uu____9155  in
         match uu____9148 with
         | FStar_Pervasives_Native.None  ->
             fail "Cannot revert; empty context"
         | FStar_Pervasives_Native.Some (x,env') ->
             let typ' =
               let uu____9172 =
                 let uu____9175 = FStar_Tactics_Types.goal_type goal  in
                 FStar_Syntax_Syntax.mk_Total uu____9175  in
               FStar_Syntax_Util.arrow [(x, FStar_Pervasives_Native.None)]
                 uu____9172
                in
             let uu____9190 = new_uvar "revert" env' typ'  in
             bind uu____9190
               (fun uu____9206  ->
                  match uu____9206 with
                  | (r,u_r) ->
                      let uu____9215 =
                        let uu____9218 =
                          let uu____9219 =
                            let uu____9220 =
                              FStar_Tactics_Types.goal_type goal  in
                            uu____9220.FStar_Syntax_Syntax.pos  in
                          let uu____9223 =
                            let uu____9228 =
                              let uu____9229 =
                                let uu____9238 =
                                  FStar_Syntax_Syntax.bv_to_name x  in
                                FStar_Syntax_Syntax.as_arg uu____9238  in
                              [uu____9229]  in
                            FStar_Syntax_Syntax.mk_Tm_app r uu____9228  in
                          uu____9223 FStar_Pervasives_Native.None uu____9219
                           in
                        set_solution goal uu____9218  in
                      bind uu____9215
                        (fun uu____9257  ->
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
      let uu____9271 = FStar_Syntax_Free.names t  in
      FStar_Util.set_mem bv uu____9271
  
let (clear : FStar_Syntax_Syntax.binder -> unit tac) =
  fun b  ->
    let bv = FStar_Pervasives_Native.fst b  in
    let uu____9287 = cur_goal ()  in
    bind uu____9287
      (fun goal  ->
         mlog
           (fun uu____9295  ->
              let uu____9296 = FStar_Syntax_Print.binder_to_string b  in
              let uu____9298 =
                let uu____9300 =
                  let uu____9302 =
                    let uu____9311 = FStar_Tactics_Types.goal_env goal  in
                    FStar_TypeChecker_Env.all_binders uu____9311  in
                  FStar_All.pipe_right uu____9302 FStar_List.length  in
                FStar_All.pipe_right uu____9300 FStar_Util.string_of_int  in
              FStar_Util.print2 "Clear of (%s), env has %s binders\n"
                uu____9296 uu____9298)
           (fun uu____9332  ->
              let uu____9333 =
                let uu____9344 = FStar_Tactics_Types.goal_env goal  in
                split_env bv uu____9344  in
              match uu____9333 with
              | FStar_Pervasives_Native.None  ->
                  fail "Cannot clear; binder not in environment"
              | FStar_Pervasives_Native.Some (e',bv1,bvs) ->
                  let rec check1 bvs1 =
                    match bvs1 with
                    | [] -> ret ()
                    | bv'::bvs2 ->
                        let uu____9389 =
                          free_in bv1 bv'.FStar_Syntax_Syntax.sort  in
                        if uu____9389
                        then
                          let uu____9394 =
                            let uu____9396 =
                              FStar_Syntax_Print.bv_to_string bv'  in
                            FStar_Util.format1
                              "Cannot clear; binder present in the type of %s"
                              uu____9396
                             in
                          fail uu____9394
                        else check1 bvs2
                     in
                  let uu____9401 =
                    let uu____9403 = FStar_Tactics_Types.goal_type goal  in
                    free_in bv1 uu____9403  in
                  if uu____9401
                  then fail "Cannot clear; binder present in goal"
                  else
                    (let uu____9410 = check1 bvs  in
                     bind uu____9410
                       (fun uu____9416  ->
                          let env' = push_bvs e' bvs  in
                          let uu____9418 =
                            let uu____9425 =
                              FStar_Tactics_Types.goal_type goal  in
                            new_uvar "clear.witness" env' uu____9425  in
                          bind uu____9418
                            (fun uu____9435  ->
                               match uu____9435 with
                               | (ut,uvar_ut) ->
                                   let uu____9444 = set_solution goal ut  in
                                   bind uu____9444
                                     (fun uu____9449  ->
                                        let uu____9450 =
                                          FStar_Tactics_Types.mk_goal env'
                                            uvar_ut
                                            goal.FStar_Tactics_Types.opts
                                            goal.FStar_Tactics_Types.is_guard
                                            goal.FStar_Tactics_Types.label
                                           in
                                        replace_cur uu____9450))))))
  
let (clear_top : unit -> unit tac) =
  fun uu____9458  ->
    let uu____9461 = cur_goal ()  in
    bind uu____9461
      (fun goal  ->
         let uu____9467 =
           let uu____9474 = FStar_Tactics_Types.goal_env goal  in
           FStar_TypeChecker_Env.pop_bv uu____9474  in
         match uu____9467 with
         | FStar_Pervasives_Native.None  ->
             fail "Cannot clear; empty context"
         | FStar_Pervasives_Native.Some (x,uu____9483) ->
             let uu____9488 = FStar_Syntax_Syntax.mk_binder x  in
             clear uu____9488)
  
let (prune : Prims.string -> unit tac) =
  fun s  ->
    let uu____9501 = cur_goal ()  in
    bind uu____9501
      (fun g  ->
         let ctx = FStar_Tactics_Types.goal_env g  in
         let ctx' =
           let uu____9511 = FStar_Ident.path_of_text s  in
           FStar_TypeChecker_Env.rem_proof_ns ctx uu____9511  in
         let g' = FStar_Tactics_Types.goal_with_env g ctx'  in replace_cur g')
  
let (addns : Prims.string -> unit tac) =
  fun s  ->
    let uu____9525 = cur_goal ()  in
    bind uu____9525
      (fun g  ->
         let ctx = FStar_Tactics_Types.goal_env g  in
         let ctx' =
           let uu____9535 = FStar_Ident.path_of_text s  in
           FStar_TypeChecker_Env.add_proof_ns ctx uu____9535  in
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
            let uu____9577 = FStar_Syntax_Subst.compress t  in
            uu____9577.FStar_Syntax_Syntax.n  in
          let uu____9580 =
            if d = FStar_Tactics_Types.TopDown
            then
              f env
                (let uu___1430_9587 = t  in
                 {
                   FStar_Syntax_Syntax.n = tn;
                   FStar_Syntax_Syntax.pos =
                     (uu___1430_9587.FStar_Syntax_Syntax.pos);
                   FStar_Syntax_Syntax.vars =
                     (uu___1430_9587.FStar_Syntax_Syntax.vars)
                 })
            else ret t  in
          bind uu____9580
            (fun t1  ->
               let ff = tac_fold_env d f env  in
               let tn1 =
                 let uu____9604 =
                   let uu____9605 = FStar_Syntax_Subst.compress t1  in
                   uu____9605.FStar_Syntax_Syntax.n  in
                 match uu____9604 with
                 | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
                     let uu____9636 = ff hd1  in
                     bind uu____9636
                       (fun hd2  ->
                          let fa uu____9662 =
                            match uu____9662 with
                            | (a,q) ->
                                let uu____9683 = ff a  in
                                bind uu____9683 (fun a1  -> ret (a1, q))
                             in
                          let uu____9702 = mapM fa args  in
                          bind uu____9702
                            (fun args1  ->
                               ret (FStar_Syntax_Syntax.Tm_app (hd2, args1))))
                 | FStar_Syntax_Syntax.Tm_abs (bs,t2,k) ->
                     let uu____9784 = FStar_Syntax_Subst.open_term bs t2  in
                     (match uu____9784 with
                      | (bs1,t') ->
                          let uu____9793 =
                            let uu____9796 =
                              FStar_TypeChecker_Env.push_binders env bs1  in
                            tac_fold_env d f uu____9796 t'  in
                          bind uu____9793
                            (fun t''  ->
                               let uu____9800 =
                                 let uu____9801 =
                                   let uu____9820 =
                                     FStar_Syntax_Subst.close_binders bs1  in
                                   let uu____9829 =
                                     FStar_Syntax_Subst.close bs1 t''  in
                                   (uu____9820, uu____9829, k)  in
                                 FStar_Syntax_Syntax.Tm_abs uu____9801  in
                               ret uu____9800))
                 | FStar_Syntax_Syntax.Tm_arrow (bs,k) -> ret tn
                 | FStar_Syntax_Syntax.Tm_match (hd1,brs) ->
                     let uu____9904 = ff hd1  in
                     bind uu____9904
                       (fun hd2  ->
                          let ffb br =
                            let uu____9919 =
                              FStar_Syntax_Subst.open_branch br  in
                            match uu____9919 with
                            | (pat,w,e) ->
                                let bvs = FStar_Syntax_Syntax.pat_bvs pat  in
                                let ff1 =
                                  let uu____9951 =
                                    FStar_TypeChecker_Env.push_bvs env bvs
                                     in
                                  tac_fold_env d f uu____9951  in
                                let uu____9952 = ff1 e  in
                                bind uu____9952
                                  (fun e1  ->
                                     let br1 =
                                       FStar_Syntax_Subst.close_branch
                                         (pat, w, e1)
                                        in
                                     ret br1)
                             in
                          let uu____9967 = mapM ffb brs  in
                          bind uu____9967
                            (fun brs1  ->
                               ret (FStar_Syntax_Syntax.Tm_match (hd2, brs1))))
                 | FStar_Syntax_Syntax.Tm_let
                     ((false
                       ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inl bv;
                          FStar_Syntax_Syntax.lbunivs = uu____10011;
                          FStar_Syntax_Syntax.lbtyp = uu____10012;
                          FStar_Syntax_Syntax.lbeff = uu____10013;
                          FStar_Syntax_Syntax.lbdef = def;
                          FStar_Syntax_Syntax.lbattrs = uu____10015;
                          FStar_Syntax_Syntax.lbpos = uu____10016;_}::[]),e)
                     ->
                     let lb =
                       let uu____10044 =
                         let uu____10045 = FStar_Syntax_Subst.compress t1  in
                         uu____10045.FStar_Syntax_Syntax.n  in
                       match uu____10044 with
                       | FStar_Syntax_Syntax.Tm_let
                           ((false ,lb::[]),uu____10049) -> lb
                       | uu____10065 -> failwith "impossible"  in
                     let fflb lb1 =
                       let uu____10075 = ff lb1.FStar_Syntax_Syntax.lbdef  in
                       bind uu____10075
                         (fun def1  ->
                            ret
                              (let uu___1383_10081 = lb1  in
                               {
                                 FStar_Syntax_Syntax.lbname =
                                   (uu___1383_10081.FStar_Syntax_Syntax.lbname);
                                 FStar_Syntax_Syntax.lbunivs =
                                   (uu___1383_10081.FStar_Syntax_Syntax.lbunivs);
                                 FStar_Syntax_Syntax.lbtyp =
                                   (uu___1383_10081.FStar_Syntax_Syntax.lbtyp);
                                 FStar_Syntax_Syntax.lbeff =
                                   (uu___1383_10081.FStar_Syntax_Syntax.lbeff);
                                 FStar_Syntax_Syntax.lbdef = def1;
                                 FStar_Syntax_Syntax.lbattrs =
                                   (uu___1383_10081.FStar_Syntax_Syntax.lbattrs);
                                 FStar_Syntax_Syntax.lbpos =
                                   (uu___1383_10081.FStar_Syntax_Syntax.lbpos)
                               }))
                        in
                     let uu____10082 = fflb lb  in
                     bind uu____10082
                       (fun lb1  ->
                          let uu____10092 =
                            let uu____10097 =
                              let uu____10098 =
                                FStar_Syntax_Syntax.mk_binder bv  in
                              [uu____10098]  in
                            FStar_Syntax_Subst.open_term uu____10097 e  in
                          match uu____10092 with
                          | (bs,e1) ->
                              let ff1 =
                                let uu____10128 =
                                  FStar_TypeChecker_Env.push_binders env bs
                                   in
                                tac_fold_env d f uu____10128  in
                              let uu____10129 = ff1 e1  in
                              bind uu____10129
                                (fun e2  ->
                                   let e3 = FStar_Syntax_Subst.close bs e2
                                      in
                                   ret
                                     (FStar_Syntax_Syntax.Tm_let
                                        ((false, [lb1]), e3))))
                 | FStar_Syntax_Syntax.Tm_let ((true ,lbs),e) ->
                     let fflb lb =
                       let uu____10176 = ff lb.FStar_Syntax_Syntax.lbdef  in
                       bind uu____10176
                         (fun def  ->
                            ret
                              (let uu___1401_10182 = lb  in
                               {
                                 FStar_Syntax_Syntax.lbname =
                                   (uu___1401_10182.FStar_Syntax_Syntax.lbname);
                                 FStar_Syntax_Syntax.lbunivs =
                                   (uu___1401_10182.FStar_Syntax_Syntax.lbunivs);
                                 FStar_Syntax_Syntax.lbtyp =
                                   (uu___1401_10182.FStar_Syntax_Syntax.lbtyp);
                                 FStar_Syntax_Syntax.lbeff =
                                   (uu___1401_10182.FStar_Syntax_Syntax.lbeff);
                                 FStar_Syntax_Syntax.lbdef = def;
                                 FStar_Syntax_Syntax.lbattrs =
                                   (uu___1401_10182.FStar_Syntax_Syntax.lbattrs);
                                 FStar_Syntax_Syntax.lbpos =
                                   (uu___1401_10182.FStar_Syntax_Syntax.lbpos)
                               }))
                        in
                     let uu____10183 = FStar_Syntax_Subst.open_let_rec lbs e
                        in
                     (match uu____10183 with
                      | (lbs1,e1) ->
                          let uu____10198 = mapM fflb lbs1  in
                          bind uu____10198
                            (fun lbs2  ->
                               let uu____10210 = ff e1  in
                               bind uu____10210
                                 (fun e2  ->
                                    let uu____10218 =
                                      FStar_Syntax_Subst.close_let_rec lbs2
                                        e2
                                       in
                                    match uu____10218 with
                                    | (lbs3,e3) ->
                                        ret
                                          (FStar_Syntax_Syntax.Tm_let
                                             ((true, lbs3), e3)))))
                 | FStar_Syntax_Syntax.Tm_ascribed (t2,asc,eff) ->
                     let uu____10289 = ff t2  in
                     bind uu____10289
                       (fun t3  ->
                          ret
                            (FStar_Syntax_Syntax.Tm_ascribed (t3, asc, eff)))
                 | FStar_Syntax_Syntax.Tm_meta (t2,m) ->
                     let uu____10320 = ff t2  in
                     bind uu____10320
                       (fun t3  -> ret (FStar_Syntax_Syntax.Tm_meta (t3, m)))
                 | uu____10327 -> ret tn  in
               bind tn1
                 (fun tn2  ->
                    let t' =
                      let uu___1425_10334 = t1  in
                      {
                        FStar_Syntax_Syntax.n = tn2;
                        FStar_Syntax_Syntax.pos =
                          (uu___1425_10334.FStar_Syntax_Syntax.pos);
                        FStar_Syntax_Syntax.vars =
                          (uu___1425_10334.FStar_Syntax_Syntax.vars)
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
              let uu____10381 =
                FStar_TypeChecker_TcTerm.tc_term
                  (let uu___1438_10390 = env  in
                   {
                     FStar_TypeChecker_Env.solver =
                       (uu___1438_10390.FStar_TypeChecker_Env.solver);
                     FStar_TypeChecker_Env.range =
                       (uu___1438_10390.FStar_TypeChecker_Env.range);
                     FStar_TypeChecker_Env.curmodule =
                       (uu___1438_10390.FStar_TypeChecker_Env.curmodule);
                     FStar_TypeChecker_Env.gamma =
                       (uu___1438_10390.FStar_TypeChecker_Env.gamma);
                     FStar_TypeChecker_Env.gamma_sig =
                       (uu___1438_10390.FStar_TypeChecker_Env.gamma_sig);
                     FStar_TypeChecker_Env.gamma_cache =
                       (uu___1438_10390.FStar_TypeChecker_Env.gamma_cache);
                     FStar_TypeChecker_Env.modules =
                       (uu___1438_10390.FStar_TypeChecker_Env.modules);
                     FStar_TypeChecker_Env.expected_typ =
                       (uu___1438_10390.FStar_TypeChecker_Env.expected_typ);
                     FStar_TypeChecker_Env.sigtab =
                       (uu___1438_10390.FStar_TypeChecker_Env.sigtab);
                     FStar_TypeChecker_Env.attrtab =
                       (uu___1438_10390.FStar_TypeChecker_Env.attrtab);
                     FStar_TypeChecker_Env.instantiate_imp =
                       (uu___1438_10390.FStar_TypeChecker_Env.instantiate_imp);
                     FStar_TypeChecker_Env.effects =
                       (uu___1438_10390.FStar_TypeChecker_Env.effects);
                     FStar_TypeChecker_Env.generalize =
                       (uu___1438_10390.FStar_TypeChecker_Env.generalize);
                     FStar_TypeChecker_Env.letrecs =
                       (uu___1438_10390.FStar_TypeChecker_Env.letrecs);
                     FStar_TypeChecker_Env.top_level =
                       (uu___1438_10390.FStar_TypeChecker_Env.top_level);
                     FStar_TypeChecker_Env.check_uvars =
                       (uu___1438_10390.FStar_TypeChecker_Env.check_uvars);
                     FStar_TypeChecker_Env.use_eq =
                       (uu___1438_10390.FStar_TypeChecker_Env.use_eq);
                     FStar_TypeChecker_Env.use_eq_strict =
                       (uu___1438_10390.FStar_TypeChecker_Env.use_eq_strict);
                     FStar_TypeChecker_Env.is_iface =
                       (uu___1438_10390.FStar_TypeChecker_Env.is_iface);
                     FStar_TypeChecker_Env.admit =
                       (uu___1438_10390.FStar_TypeChecker_Env.admit);
                     FStar_TypeChecker_Env.lax = true;
                     FStar_TypeChecker_Env.lax_universes =
                       (uu___1438_10390.FStar_TypeChecker_Env.lax_universes);
                     FStar_TypeChecker_Env.phase1 =
                       (uu___1438_10390.FStar_TypeChecker_Env.phase1);
                     FStar_TypeChecker_Env.failhard =
                       (uu___1438_10390.FStar_TypeChecker_Env.failhard);
                     FStar_TypeChecker_Env.nosynth =
                       (uu___1438_10390.FStar_TypeChecker_Env.nosynth);
                     FStar_TypeChecker_Env.uvar_subtyping =
                       (uu___1438_10390.FStar_TypeChecker_Env.uvar_subtyping);
                     FStar_TypeChecker_Env.tc_term =
                       (uu___1438_10390.FStar_TypeChecker_Env.tc_term);
                     FStar_TypeChecker_Env.type_of =
                       (uu___1438_10390.FStar_TypeChecker_Env.type_of);
                     FStar_TypeChecker_Env.universe_of =
                       (uu___1438_10390.FStar_TypeChecker_Env.universe_of);
                     FStar_TypeChecker_Env.check_type_of =
                       (uu___1438_10390.FStar_TypeChecker_Env.check_type_of);
                     FStar_TypeChecker_Env.use_bv_sorts =
                       (uu___1438_10390.FStar_TypeChecker_Env.use_bv_sorts);
                     FStar_TypeChecker_Env.qtbl_name_and_index =
                       (uu___1438_10390.FStar_TypeChecker_Env.qtbl_name_and_index);
                     FStar_TypeChecker_Env.normalized_eff_names =
                       (uu___1438_10390.FStar_TypeChecker_Env.normalized_eff_names);
                     FStar_TypeChecker_Env.fv_delta_depths =
                       (uu___1438_10390.FStar_TypeChecker_Env.fv_delta_depths);
                     FStar_TypeChecker_Env.proof_ns =
                       (uu___1438_10390.FStar_TypeChecker_Env.proof_ns);
                     FStar_TypeChecker_Env.synth_hook =
                       (uu___1438_10390.FStar_TypeChecker_Env.synth_hook);
                     FStar_TypeChecker_Env.try_solve_implicits_hook =
                       (uu___1438_10390.FStar_TypeChecker_Env.try_solve_implicits_hook);
                     FStar_TypeChecker_Env.splice =
                       (uu___1438_10390.FStar_TypeChecker_Env.splice);
                     FStar_TypeChecker_Env.mpreprocess =
                       (uu___1438_10390.FStar_TypeChecker_Env.mpreprocess);
                     FStar_TypeChecker_Env.postprocess =
                       (uu___1438_10390.FStar_TypeChecker_Env.postprocess);
                     FStar_TypeChecker_Env.is_native_tactic =
                       (uu___1438_10390.FStar_TypeChecker_Env.is_native_tactic);
                     FStar_TypeChecker_Env.identifier_info =
                       (uu___1438_10390.FStar_TypeChecker_Env.identifier_info);
                     FStar_TypeChecker_Env.tc_hooks =
                       (uu___1438_10390.FStar_TypeChecker_Env.tc_hooks);
                     FStar_TypeChecker_Env.dsenv =
                       (uu___1438_10390.FStar_TypeChecker_Env.dsenv);
                     FStar_TypeChecker_Env.nbe =
                       (uu___1438_10390.FStar_TypeChecker_Env.nbe);
                     FStar_TypeChecker_Env.strict_args_tab =
                       (uu___1438_10390.FStar_TypeChecker_Env.strict_args_tab);
                     FStar_TypeChecker_Env.erasable_types_tab =
                       (uu___1438_10390.FStar_TypeChecker_Env.erasable_types_tab)
                   }) t
                 in
              match uu____10381 with
              | (uu____10394,lcomp,g) ->
                  let uu____10397 =
                    (let uu____10401 =
                       FStar_TypeChecker_Common.is_pure_or_ghost_lcomp lcomp
                        in
                     Prims.op_Negation uu____10401) ||
                      (let uu____10404 = FStar_TypeChecker_Env.is_trivial g
                          in
                       Prims.op_Negation uu____10404)
                     in
                  if uu____10397
                  then ret t
                  else
                    (let rewrite_eq =
                       let typ = lcomp.FStar_TypeChecker_Common.res_typ  in
                       let uu____10415 = new_uvar "pointwise_rec" env typ  in
                       bind uu____10415
                         (fun uu____10432  ->
                            match uu____10432 with
                            | (ut,uvar_ut) ->
                                (log ps
                                   (fun uu____10445  ->
                                      let uu____10446 =
                                        FStar_Syntax_Print.term_to_string t
                                         in
                                      let uu____10448 =
                                        FStar_Syntax_Print.term_to_string ut
                                         in
                                      FStar_Util.print2
                                        "Pointwise_rec: making equality\n\t%s ==\n\t%s\n"
                                        uu____10446 uu____10448);
                                 (let uu____10451 =
                                    let uu____10454 =
                                      let uu____10455 =
                                        FStar_TypeChecker_TcTerm.universe_of
                                          env typ
                                         in
                                      FStar_Syntax_Util.mk_eq2 uu____10455
                                        typ t ut
                                       in
                                    add_irrelevant_goal
                                      "pointwise_rec equation" env
                                      uu____10454 opts label1
                                     in
                                  bind uu____10451
                                    (fun uu____10459  ->
                                       let uu____10460 =
                                         bind tau
                                           (fun uu____10466  ->
                                              let ut1 =
                                                FStar_TypeChecker_Normalize.reduce_uvar_solutions
                                                  env ut
                                                 in
                                              log ps
                                                (fun uu____10472  ->
                                                   let uu____10473 =
                                                     FStar_Syntax_Print.term_to_string
                                                       t
                                                      in
                                                   let uu____10475 =
                                                     FStar_Syntax_Print.term_to_string
                                                       ut1
                                                      in
                                                   FStar_Util.print2
                                                     "pointwise_rec: succeeded rewriting\n\t%s to\n\t%s\n"
                                                     uu____10473 uu____10475);
                                              ret ut1)
                                          in
                                       focus uu____10460))))
                        in
                     let uu____10478 = catch rewrite_eq  in
                     bind uu____10478
                       (fun uu___5_10490  ->
                          match uu___5_10490 with
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
          let uu____10690 = FStar_Syntax_Subst.compress t  in
          maybe_continue ctrl uu____10690
            (fun t1  ->
               let uu____10698 =
                 f env
                   (let uu___1515_10706 = t1  in
                    {
                      FStar_Syntax_Syntax.n = (t1.FStar_Syntax_Syntax.n);
                      FStar_Syntax_Syntax.pos =
                        (uu___1515_10706.FStar_Syntax_Syntax.pos);
                      FStar_Syntax_Syntax.vars =
                        (uu___1515_10706.FStar_Syntax_Syntax.vars)
                    })
                  in
               bind uu____10698
                 (fun uu____10722  ->
                    match uu____10722 with
                    | (t2,ctrl1) ->
                        maybe_continue ctrl1 t2
                          (fun t3  ->
                             let uu____10745 =
                               let uu____10746 =
                                 FStar_Syntax_Subst.compress t3  in
                               uu____10746.FStar_Syntax_Syntax.n  in
                             match uu____10745 with
                             | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
                                 let uu____10783 =
                                   ctrl_tac_fold f env ctrl1 hd1  in
                                 bind uu____10783
                                   (fun uu____10805  ->
                                      match uu____10805 with
                                      | (hd2,ctrl2) ->
                                          let ctrl3 = keep_going ctrl2  in
                                          let uu____10821 =
                                            ctrl_tac_fold_args f env ctrl3
                                              args
                                             in
                                          bind uu____10821
                                            (fun uu____10845  ->
                                               match uu____10845 with
                                               | (args1,ctrl4) ->
                                                   ret
                                                     ((let uu___1495_10875 =
                                                         t3  in
                                                       {
                                                         FStar_Syntax_Syntax.n
                                                           =
                                                           (FStar_Syntax_Syntax.Tm_app
                                                              (hd2, args1));
                                                         FStar_Syntax_Syntax.pos
                                                           =
                                                           (uu___1495_10875.FStar_Syntax_Syntax.pos);
                                                         FStar_Syntax_Syntax.vars
                                                           =
                                                           (uu___1495_10875.FStar_Syntax_Syntax.vars)
                                                       }), ctrl4)))
                             | FStar_Syntax_Syntax.Tm_abs (bs,t4,k) ->
                                 let uu____10917 =
                                   FStar_Syntax_Subst.open_term bs t4  in
                                 (match uu____10917 with
                                  | (bs1,t') ->
                                      let uu____10932 =
                                        let uu____10939 =
                                          FStar_TypeChecker_Env.push_binders
                                            env bs1
                                           in
                                        ctrl_tac_fold f uu____10939 ctrl1 t'
                                         in
                                      bind uu____10932
                                        (fun uu____10954  ->
                                           match uu____10954 with
                                           | (t'',ctrl2) ->
                                               let uu____10969 =
                                                 let uu____10976 =
                                                   let uu___1508_10979 = t4
                                                      in
                                                   let uu____10982 =
                                                     let uu____10983 =
                                                       let uu____11002 =
                                                         FStar_Syntax_Subst.close_binders
                                                           bs1
                                                          in
                                                       let uu____11011 =
                                                         FStar_Syntax_Subst.close
                                                           bs1 t''
                                                          in
                                                       (uu____11002,
                                                         uu____11011, k)
                                                        in
                                                     FStar_Syntax_Syntax.Tm_abs
                                                       uu____10983
                                                      in
                                                   {
                                                     FStar_Syntax_Syntax.n =
                                                       uu____10982;
                                                     FStar_Syntax_Syntax.pos
                                                       =
                                                       (uu___1508_10979.FStar_Syntax_Syntax.pos);
                                                     FStar_Syntax_Syntax.vars
                                                       =
                                                       (uu___1508_10979.FStar_Syntax_Syntax.vars)
                                                   }  in
                                                 (uu____10976, ctrl2)  in
                                               ret uu____10969))
                             | FStar_Syntax_Syntax.Tm_arrow (bs,k) ->
                                 ret (t3, ctrl1)
                             | uu____11064 -> ret (t3, ctrl1))))

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
              let uu____11110 = ctrl_tac_fold f env ctrl t  in
              bind uu____11110
                (fun uu____11131  ->
                   match uu____11131 with
                   | (t1,ctrl1) ->
                       let uu____11146 = ctrl_tac_fold_args f env ctrl1 ts1
                          in
                       bind uu____11146
                         (fun uu____11170  ->
                            match uu____11170 with
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
                let uu____11261 =
                  let uu____11269 =
                    add_irrelevant_goal "dummy" env FStar_Syntax_Util.t_true
                      opts label1
                     in
                  bind uu____11269
                    (fun uu____11280  ->
                       let uu____11281 = ctrl t1  in
                       bind uu____11281
                         (fun res  ->
                            let uu____11307 = trivial ()  in
                            bind uu____11307 (fun uu____11316  -> ret res)))
                   in
                bind uu____11261
                  (fun uu____11334  ->
                     match uu____11334 with
                     | (should_rewrite,ctrl1) ->
                         if Prims.op_Negation should_rewrite
                         then ret (t1, ctrl1)
                         else
                           (let uu____11363 =
                              FStar_TypeChecker_TcTerm.tc_term
                                (let uu___1545_11372 = env  in
                                 {
                                   FStar_TypeChecker_Env.solver =
                                     (uu___1545_11372.FStar_TypeChecker_Env.solver);
                                   FStar_TypeChecker_Env.range =
                                     (uu___1545_11372.FStar_TypeChecker_Env.range);
                                   FStar_TypeChecker_Env.curmodule =
                                     (uu___1545_11372.FStar_TypeChecker_Env.curmodule);
                                   FStar_TypeChecker_Env.gamma =
                                     (uu___1545_11372.FStar_TypeChecker_Env.gamma);
                                   FStar_TypeChecker_Env.gamma_sig =
                                     (uu___1545_11372.FStar_TypeChecker_Env.gamma_sig);
                                   FStar_TypeChecker_Env.gamma_cache =
                                     (uu___1545_11372.FStar_TypeChecker_Env.gamma_cache);
                                   FStar_TypeChecker_Env.modules =
                                     (uu___1545_11372.FStar_TypeChecker_Env.modules);
                                   FStar_TypeChecker_Env.expected_typ =
                                     (uu___1545_11372.FStar_TypeChecker_Env.expected_typ);
                                   FStar_TypeChecker_Env.sigtab =
                                     (uu___1545_11372.FStar_TypeChecker_Env.sigtab);
                                   FStar_TypeChecker_Env.attrtab =
                                     (uu___1545_11372.FStar_TypeChecker_Env.attrtab);
                                   FStar_TypeChecker_Env.instantiate_imp =
                                     (uu___1545_11372.FStar_TypeChecker_Env.instantiate_imp);
                                   FStar_TypeChecker_Env.effects =
                                     (uu___1545_11372.FStar_TypeChecker_Env.effects);
                                   FStar_TypeChecker_Env.generalize =
                                     (uu___1545_11372.FStar_TypeChecker_Env.generalize);
                                   FStar_TypeChecker_Env.letrecs =
                                     (uu___1545_11372.FStar_TypeChecker_Env.letrecs);
                                   FStar_TypeChecker_Env.top_level =
                                     (uu___1545_11372.FStar_TypeChecker_Env.top_level);
                                   FStar_TypeChecker_Env.check_uvars =
                                     (uu___1545_11372.FStar_TypeChecker_Env.check_uvars);
                                   FStar_TypeChecker_Env.use_eq =
                                     (uu___1545_11372.FStar_TypeChecker_Env.use_eq);
                                   FStar_TypeChecker_Env.use_eq_strict =
                                     (uu___1545_11372.FStar_TypeChecker_Env.use_eq_strict);
                                   FStar_TypeChecker_Env.is_iface =
                                     (uu___1545_11372.FStar_TypeChecker_Env.is_iface);
                                   FStar_TypeChecker_Env.admit =
                                     (uu___1545_11372.FStar_TypeChecker_Env.admit);
                                   FStar_TypeChecker_Env.lax = true;
                                   FStar_TypeChecker_Env.lax_universes =
                                     (uu___1545_11372.FStar_TypeChecker_Env.lax_universes);
                                   FStar_TypeChecker_Env.phase1 =
                                     (uu___1545_11372.FStar_TypeChecker_Env.phase1);
                                   FStar_TypeChecker_Env.failhard =
                                     (uu___1545_11372.FStar_TypeChecker_Env.failhard);
                                   FStar_TypeChecker_Env.nosynth =
                                     (uu___1545_11372.FStar_TypeChecker_Env.nosynth);
                                   FStar_TypeChecker_Env.uvar_subtyping =
                                     (uu___1545_11372.FStar_TypeChecker_Env.uvar_subtyping);
                                   FStar_TypeChecker_Env.tc_term =
                                     (uu___1545_11372.FStar_TypeChecker_Env.tc_term);
                                   FStar_TypeChecker_Env.type_of =
                                     (uu___1545_11372.FStar_TypeChecker_Env.type_of);
                                   FStar_TypeChecker_Env.universe_of =
                                     (uu___1545_11372.FStar_TypeChecker_Env.universe_of);
                                   FStar_TypeChecker_Env.check_type_of =
                                     (uu___1545_11372.FStar_TypeChecker_Env.check_type_of);
                                   FStar_TypeChecker_Env.use_bv_sorts =
                                     (uu___1545_11372.FStar_TypeChecker_Env.use_bv_sorts);
                                   FStar_TypeChecker_Env.qtbl_name_and_index
                                     =
                                     (uu___1545_11372.FStar_TypeChecker_Env.qtbl_name_and_index);
                                   FStar_TypeChecker_Env.normalized_eff_names
                                     =
                                     (uu___1545_11372.FStar_TypeChecker_Env.normalized_eff_names);
                                   FStar_TypeChecker_Env.fv_delta_depths =
                                     (uu___1545_11372.FStar_TypeChecker_Env.fv_delta_depths);
                                   FStar_TypeChecker_Env.proof_ns =
                                     (uu___1545_11372.FStar_TypeChecker_Env.proof_ns);
                                   FStar_TypeChecker_Env.synth_hook =
                                     (uu___1545_11372.FStar_TypeChecker_Env.synth_hook);
                                   FStar_TypeChecker_Env.try_solve_implicits_hook
                                     =
                                     (uu___1545_11372.FStar_TypeChecker_Env.try_solve_implicits_hook);
                                   FStar_TypeChecker_Env.splice =
                                     (uu___1545_11372.FStar_TypeChecker_Env.splice);
                                   FStar_TypeChecker_Env.mpreprocess =
                                     (uu___1545_11372.FStar_TypeChecker_Env.mpreprocess);
                                   FStar_TypeChecker_Env.postprocess =
                                     (uu___1545_11372.FStar_TypeChecker_Env.postprocess);
                                   FStar_TypeChecker_Env.is_native_tactic =
                                     (uu___1545_11372.FStar_TypeChecker_Env.is_native_tactic);
                                   FStar_TypeChecker_Env.identifier_info =
                                     (uu___1545_11372.FStar_TypeChecker_Env.identifier_info);
                                   FStar_TypeChecker_Env.tc_hooks =
                                     (uu___1545_11372.FStar_TypeChecker_Env.tc_hooks);
                                   FStar_TypeChecker_Env.dsenv =
                                     (uu___1545_11372.FStar_TypeChecker_Env.dsenv);
                                   FStar_TypeChecker_Env.nbe =
                                     (uu___1545_11372.FStar_TypeChecker_Env.nbe);
                                   FStar_TypeChecker_Env.strict_args_tab =
                                     (uu___1545_11372.FStar_TypeChecker_Env.strict_args_tab);
                                   FStar_TypeChecker_Env.erasable_types_tab =
                                     (uu___1545_11372.FStar_TypeChecker_Env.erasable_types_tab)
                                 }) t1
                               in
                            match uu____11363 with
                            | (t2,lcomp,g) ->
                                let uu____11383 =
                                  (let uu____11387 =
                                     FStar_TypeChecker_Common.is_pure_or_ghost_lcomp
                                       lcomp
                                      in
                                   Prims.op_Negation uu____11387) ||
                                    (let uu____11390 =
                                       FStar_TypeChecker_Env.is_trivial g  in
                                     Prims.op_Negation uu____11390)
                                   in
                                if uu____11383
                                then ret (t2, globalStop)
                                else
                                  (let typ =
                                     lcomp.FStar_TypeChecker_Common.res_typ
                                      in
                                   let uu____11406 =
                                     new_uvar "pointwise_rec" env typ  in
                                   bind uu____11406
                                     (fun uu____11427  ->
                                        match uu____11427 with
                                        | (ut,uvar_ut) ->
                                            (log ps
                                               (fun uu____11444  ->
                                                  let uu____11445 =
                                                    FStar_Syntax_Print.term_to_string
                                                      t2
                                                     in
                                                  let uu____11447 =
                                                    FStar_Syntax_Print.term_to_string
                                                      ut
                                                     in
                                                  FStar_Util.print2
                                                    "Pointwise_rec: making equality\n\t%s ==\n\t%s\n"
                                                    uu____11445 uu____11447);
                                             (let uu____11450 =
                                                let uu____11453 =
                                                  let uu____11454 =
                                                    FStar_TypeChecker_TcTerm.universe_of
                                                      env typ
                                                     in
                                                  FStar_Syntax_Util.mk_eq2
                                                    uu____11454 typ t2 ut
                                                   in
                                                add_irrelevant_goal
                                                  "rewrite_rec equation" env
                                                  uu____11453 opts label1
                                                 in
                                              bind uu____11450
                                                (fun uu____11462  ->
                                                   let uu____11463 =
                                                     bind rewriter
                                                       (fun uu____11477  ->
                                                          let ut1 =
                                                            FStar_TypeChecker_Normalize.reduce_uvar_solutions
                                                              env ut
                                                             in
                                                          log ps
                                                            (fun uu____11483 
                                                               ->
                                                               let uu____11484
                                                                 =
                                                                 FStar_Syntax_Print.term_to_string
                                                                   t2
                                                                  in
                                                               let uu____11486
                                                                 =
                                                                 FStar_Syntax_Print.term_to_string
                                                                   ut1
                                                                  in
                                                               FStar_Util.print2
                                                                 "rewrite_rec: succeeded rewriting\n\t%s to\n\t%s\n"
                                                                 uu____11484
                                                                 uu____11486);
                                                          ret (ut1, ctrl1))
                                                      in
                                                   focus uu____11463)))))))
  
let (topdown_rewrite :
  (FStar_Syntax_Syntax.term -> (Prims.bool * FStar_BigInt.t) tac) ->
    unit tac -> unit tac)
  =
  fun ctrl  ->
    fun rewriter  ->
      let uu____11531 =
        bind get
          (fun ps  ->
             let uu____11541 =
               match ps.FStar_Tactics_Types.goals with
               | g::gs -> (g, gs)
               | [] -> failwith "no goals"  in
             match uu____11541 with
             | (g,gs) ->
                 let gt1 = FStar_Tactics_Types.goal_type g  in
                 (log ps
                    (fun uu____11579  ->
                       let uu____11580 =
                         FStar_Syntax_Print.term_to_string gt1  in
                       FStar_Util.print1 "Topdown_rewrite starting with %s\n"
                         uu____11580);
                  bind dismiss_all
                    (fun uu____11585  ->
                       let uu____11586 =
                         let uu____11593 = FStar_Tactics_Types.goal_env g  in
                         ctrl_tac_fold
                           (rewrite_rec ps ctrl rewriter
                              g.FStar_Tactics_Types.opts
                              g.FStar_Tactics_Types.label) uu____11593
                           keepGoing gt1
                          in
                       bind uu____11586
                         (fun uu____11603  ->
                            match uu____11603 with
                            | (gt',uu____11611) ->
                                (log ps
                                   (fun uu____11615  ->
                                      let uu____11616 =
                                        FStar_Syntax_Print.term_to_string gt'
                                         in
                                      FStar_Util.print1
                                        "Topdown_rewrite seems to have succeded with %s\n"
                                        uu____11616);
                                 (let uu____11619 = push_goals gs  in
                                  bind uu____11619
                                    (fun uu____11624  ->
                                       let uu____11625 =
                                         let uu____11628 =
                                           let uu____11629 =
                                             FStar_Tactics_Types.goal_with_type
                                               g gt'
                                              in
                                           FStar_All.pipe_right uu____11629
                                             bnorm_goal
                                            in
                                         [uu____11628]  in
                                       add_goals uu____11625)))))))
         in
      FStar_All.pipe_left (wrap_err "topdown_rewrite") uu____11531
  
let (t_pointwise : FStar_Tactics_Types.direction -> unit tac -> unit tac) =
  fun d  ->
    fun tau  ->
      let uu____11654 =
        bind get
          (fun ps  ->
             let uu____11664 =
               match ps.FStar_Tactics_Types.goals with
               | g::gs -> (g, gs)
               | [] -> failwith "no goals"  in
             match uu____11664 with
             | (g,gs) ->
                 let gt1 = FStar_Tactics_Types.goal_type g  in
                 (log ps
                    (fun uu____11702  ->
                       let uu____11703 =
                         FStar_Syntax_Print.term_to_string gt1  in
                       FStar_Util.print1 "Pointwise starting with %s\n"
                         uu____11703);
                  bind dismiss_all
                    (fun uu____11708  ->
                       let uu____11709 =
                         let uu____11712 = FStar_Tactics_Types.goal_env g  in
                         tac_fold_env d
                           (pointwise_rec ps tau g.FStar_Tactics_Types.opts
                              g.FStar_Tactics_Types.label) uu____11712 gt1
                          in
                       bind uu____11709
                         (fun gt'  ->
                            log ps
                              (fun uu____11720  ->
                                 let uu____11721 =
                                   FStar_Syntax_Print.term_to_string gt'  in
                                 FStar_Util.print1
                                   "Pointwise seems to have succeded with %s\n"
                                   uu____11721);
                            (let uu____11724 = push_goals gs  in
                             bind uu____11724
                               (fun uu____11729  ->
                                  let uu____11730 =
                                    let uu____11733 =
                                      let uu____11734 =
                                        FStar_Tactics_Types.goal_with_type g
                                          gt'
                                         in
                                      FStar_All.pipe_right uu____11734
                                        bnorm_goal
                                       in
                                    [uu____11733]  in
                                  add_goals uu____11730))))))
         in
      FStar_All.pipe_left (wrap_err "t_pointwise") uu____11654
  
let (_trefl :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> unit tac) =
  fun l  ->
    fun r  ->
      let uu____11755 = cur_goal ()  in
      bind uu____11755
        (fun g  ->
           let uu____11761 =
             let uu____11765 = FStar_Tactics_Types.goal_env g  in
             do_unify uu____11765 l r  in
           bind uu____11761
             (fun b  ->
                if b
                then solve' g FStar_Syntax_Util.exp_unit
                else
                  (let l1 =
                     let uu____11776 = FStar_Tactics_Types.goal_env g  in
                     FStar_TypeChecker_Normalize.normalize
                       [FStar_TypeChecker_Env.UnfoldUntil
                          FStar_Syntax_Syntax.delta_constant;
                       FStar_TypeChecker_Env.Primops;
                       FStar_TypeChecker_Env.UnfoldTac] uu____11776 l
                      in
                   let r1 =
                     let uu____11778 = FStar_Tactics_Types.goal_env g  in
                     FStar_TypeChecker_Normalize.normalize
                       [FStar_TypeChecker_Env.UnfoldUntil
                          FStar_Syntax_Syntax.delta_constant;
                       FStar_TypeChecker_Env.Primops;
                       FStar_TypeChecker_Env.UnfoldTac] uu____11778 r
                      in
                   let uu____11779 =
                     let uu____11783 = FStar_Tactics_Types.goal_env g  in
                     do_unify uu____11783 l1 r1  in
                   bind uu____11779
                     (fun b1  ->
                        if b1
                        then solve' g FStar_Syntax_Util.exp_unit
                        else
                          (let uu____11793 =
                             let uu____11800 =
                               let uu____11806 =
                                 FStar_Tactics_Types.goal_env g  in
                               tts uu____11806  in
                             FStar_TypeChecker_Err.print_discrepancy
                               uu____11800 l1 r1
                              in
                           match uu____11793 with
                           | (ls,rs) ->
                               fail2 "not a trivial equality ((%s) vs (%s))"
                                 ls rs)))))
  
let (trefl : unit -> unit tac) =
  fun uu____11823  ->
    let uu____11826 =
      let uu____11829 = cur_goal ()  in
      bind uu____11829
        (fun g  ->
           let uu____11837 =
             let uu____11844 =
               let uu____11845 = FStar_Tactics_Types.goal_env g  in
               let uu____11846 = FStar_Tactics_Types.goal_type g  in
               bnorm uu____11845 uu____11846  in
             destruct_eq uu____11844  in
           match uu____11837 with
           | FStar_Pervasives_Native.Some (l,r) -> _trefl l r
           | FStar_Pervasives_Native.None  ->
               let uu____11859 =
                 let uu____11861 = FStar_Tactics_Types.goal_env g  in
                 let uu____11862 = FStar_Tactics_Types.goal_type g  in
                 tts uu____11861 uu____11862  in
               fail1 "not an equality (%s)" uu____11859)
       in
    FStar_All.pipe_left (wrap_err "trefl") uu____11826
  
let (dup : unit -> unit tac) =
  fun uu____11876  ->
    let uu____11879 = cur_goal ()  in
    bind uu____11879
      (fun g  ->
         let uu____11885 =
           let uu____11892 = FStar_Tactics_Types.goal_env g  in
           let uu____11893 = FStar_Tactics_Types.goal_type g  in
           new_uvar "dup" uu____11892 uu____11893  in
         bind uu____11885
           (fun uu____11903  ->
              match uu____11903 with
              | (u,u_uvar) ->
                  let g' =
                    let uu___1628_11913 = g  in
                    {
                      FStar_Tactics_Types.goal_main_env =
                        (uu___1628_11913.FStar_Tactics_Types.goal_main_env);
                      FStar_Tactics_Types.goal_ctx_uvar = u_uvar;
                      FStar_Tactics_Types.opts =
                        (uu___1628_11913.FStar_Tactics_Types.opts);
                      FStar_Tactics_Types.is_guard =
                        (uu___1628_11913.FStar_Tactics_Types.is_guard);
                      FStar_Tactics_Types.label =
                        (uu___1628_11913.FStar_Tactics_Types.label)
                    }  in
                  bind __dismiss
                    (fun uu____11916  ->
                       let uu____11917 =
                         let uu____11920 = FStar_Tactics_Types.goal_env g  in
                         let uu____11921 =
                           let uu____11922 =
                             let uu____11923 = FStar_Tactics_Types.goal_env g
                                in
                             let uu____11924 =
                               FStar_Tactics_Types.goal_type g  in
                             FStar_TypeChecker_TcTerm.universe_of uu____11923
                               uu____11924
                              in
                           let uu____11925 = FStar_Tactics_Types.goal_type g
                              in
                           let uu____11926 =
                             FStar_Tactics_Types.goal_witness g  in
                           FStar_Syntax_Util.mk_eq2 uu____11922 uu____11925 u
                             uu____11926
                            in
                         add_irrelevant_goal "dup equation" uu____11920
                           uu____11921 g.FStar_Tactics_Types.opts
                           g.FStar_Tactics_Types.label
                          in
                       bind uu____11917
                         (fun uu____11930  ->
                            let uu____11931 = add_goals [g']  in
                            bind uu____11931 (fun uu____11935  -> ret ())))))
  
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
              let uu____12061 = f x y  in
              if uu____12061 then aux (x :: acc) xs ys else (acc, xs, ys)
          | uu____12084 -> (acc, l11, l21)  in
        let uu____12099 = aux [] l1 l2  in
        match uu____12099 with | (pr,t1,t2) -> ((FStar_List.rev pr), t1, t2)
  
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
      let uu____12205 = get_phi g1  in
      match uu____12205 with
      | FStar_Pervasives_Native.None  -> fail "goal 1 is not irrelevant"
      | FStar_Pervasives_Native.Some phi1 ->
          let uu____12212 = get_phi g2  in
          (match uu____12212 with
           | FStar_Pervasives_Native.None  -> fail "goal 2 is not irrelevant"
           | FStar_Pervasives_Native.Some phi2 ->
               let gamma1 =
                 (g1.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_gamma
                  in
               let gamma2 =
                 (g2.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_gamma
                  in
               let uu____12225 =
                 longest_prefix FStar_Syntax_Syntax.eq_binding
                   (FStar_List.rev gamma1) (FStar_List.rev gamma2)
                  in
               (match uu____12225 with
                | (gamma,r1,r2) ->
                    let t1 =
                      let uu____12256 =
                        FStar_TypeChecker_Env.binders_of_bindings
                          (FStar_List.rev r1)
                         in
                      close_forall_no_univs1 uu____12256 phi1  in
                    let t2 =
                      let uu____12266 =
                        FStar_TypeChecker_Env.binders_of_bindings
                          (FStar_List.rev r2)
                         in
                      close_forall_no_univs1 uu____12266 phi2  in
                    let uu____12275 =
                      set_solution g1 FStar_Syntax_Util.exp_unit  in
                    bind uu____12275
                      (fun uu____12280  ->
                         let uu____12281 =
                           set_solution g2 FStar_Syntax_Util.exp_unit  in
                         bind uu____12281
                           (fun uu____12288  ->
                              let ng = FStar_Syntax_Util.mk_conj t1 t2  in
                              let nenv =
                                let uu___1679_12293 =
                                  FStar_Tactics_Types.goal_env g1  in
                                let uu____12294 =
                                  FStar_Util.smap_create (Prims.of_int (100))
                                   in
                                {
                                  FStar_TypeChecker_Env.solver =
                                    (uu___1679_12293.FStar_TypeChecker_Env.solver);
                                  FStar_TypeChecker_Env.range =
                                    (uu___1679_12293.FStar_TypeChecker_Env.range);
                                  FStar_TypeChecker_Env.curmodule =
                                    (uu___1679_12293.FStar_TypeChecker_Env.curmodule);
                                  FStar_TypeChecker_Env.gamma =
                                    (FStar_List.rev gamma);
                                  FStar_TypeChecker_Env.gamma_sig =
                                    (uu___1679_12293.FStar_TypeChecker_Env.gamma_sig);
                                  FStar_TypeChecker_Env.gamma_cache =
                                    uu____12294;
                                  FStar_TypeChecker_Env.modules =
                                    (uu___1679_12293.FStar_TypeChecker_Env.modules);
                                  FStar_TypeChecker_Env.expected_typ =
                                    (uu___1679_12293.FStar_TypeChecker_Env.expected_typ);
                                  FStar_TypeChecker_Env.sigtab =
                                    (uu___1679_12293.FStar_TypeChecker_Env.sigtab);
                                  FStar_TypeChecker_Env.attrtab =
                                    (uu___1679_12293.FStar_TypeChecker_Env.attrtab);
                                  FStar_TypeChecker_Env.instantiate_imp =
                                    (uu___1679_12293.FStar_TypeChecker_Env.instantiate_imp);
                                  FStar_TypeChecker_Env.effects =
                                    (uu___1679_12293.FStar_TypeChecker_Env.effects);
                                  FStar_TypeChecker_Env.generalize =
                                    (uu___1679_12293.FStar_TypeChecker_Env.generalize);
                                  FStar_TypeChecker_Env.letrecs =
                                    (uu___1679_12293.FStar_TypeChecker_Env.letrecs);
                                  FStar_TypeChecker_Env.top_level =
                                    (uu___1679_12293.FStar_TypeChecker_Env.top_level);
                                  FStar_TypeChecker_Env.check_uvars =
                                    (uu___1679_12293.FStar_TypeChecker_Env.check_uvars);
                                  FStar_TypeChecker_Env.use_eq =
                                    (uu___1679_12293.FStar_TypeChecker_Env.use_eq);
                                  FStar_TypeChecker_Env.use_eq_strict =
                                    (uu___1679_12293.FStar_TypeChecker_Env.use_eq_strict);
                                  FStar_TypeChecker_Env.is_iface =
                                    (uu___1679_12293.FStar_TypeChecker_Env.is_iface);
                                  FStar_TypeChecker_Env.admit =
                                    (uu___1679_12293.FStar_TypeChecker_Env.admit);
                                  FStar_TypeChecker_Env.lax =
                                    (uu___1679_12293.FStar_TypeChecker_Env.lax);
                                  FStar_TypeChecker_Env.lax_universes =
                                    (uu___1679_12293.FStar_TypeChecker_Env.lax_universes);
                                  FStar_TypeChecker_Env.phase1 =
                                    (uu___1679_12293.FStar_TypeChecker_Env.phase1);
                                  FStar_TypeChecker_Env.failhard =
                                    (uu___1679_12293.FStar_TypeChecker_Env.failhard);
                                  FStar_TypeChecker_Env.nosynth =
                                    (uu___1679_12293.FStar_TypeChecker_Env.nosynth);
                                  FStar_TypeChecker_Env.uvar_subtyping =
                                    (uu___1679_12293.FStar_TypeChecker_Env.uvar_subtyping);
                                  FStar_TypeChecker_Env.tc_term =
                                    (uu___1679_12293.FStar_TypeChecker_Env.tc_term);
                                  FStar_TypeChecker_Env.type_of =
                                    (uu___1679_12293.FStar_TypeChecker_Env.type_of);
                                  FStar_TypeChecker_Env.universe_of =
                                    (uu___1679_12293.FStar_TypeChecker_Env.universe_of);
                                  FStar_TypeChecker_Env.check_type_of =
                                    (uu___1679_12293.FStar_TypeChecker_Env.check_type_of);
                                  FStar_TypeChecker_Env.use_bv_sorts =
                                    (uu___1679_12293.FStar_TypeChecker_Env.use_bv_sorts);
                                  FStar_TypeChecker_Env.qtbl_name_and_index =
                                    (uu___1679_12293.FStar_TypeChecker_Env.qtbl_name_and_index);
                                  FStar_TypeChecker_Env.normalized_eff_names
                                    =
                                    (uu___1679_12293.FStar_TypeChecker_Env.normalized_eff_names);
                                  FStar_TypeChecker_Env.fv_delta_depths =
                                    (uu___1679_12293.FStar_TypeChecker_Env.fv_delta_depths);
                                  FStar_TypeChecker_Env.proof_ns =
                                    (uu___1679_12293.FStar_TypeChecker_Env.proof_ns);
                                  FStar_TypeChecker_Env.synth_hook =
                                    (uu___1679_12293.FStar_TypeChecker_Env.synth_hook);
                                  FStar_TypeChecker_Env.try_solve_implicits_hook
                                    =
                                    (uu___1679_12293.FStar_TypeChecker_Env.try_solve_implicits_hook);
                                  FStar_TypeChecker_Env.splice =
                                    (uu___1679_12293.FStar_TypeChecker_Env.splice);
                                  FStar_TypeChecker_Env.mpreprocess =
                                    (uu___1679_12293.FStar_TypeChecker_Env.mpreprocess);
                                  FStar_TypeChecker_Env.postprocess =
                                    (uu___1679_12293.FStar_TypeChecker_Env.postprocess);
                                  FStar_TypeChecker_Env.is_native_tactic =
                                    (uu___1679_12293.FStar_TypeChecker_Env.is_native_tactic);
                                  FStar_TypeChecker_Env.identifier_info =
                                    (uu___1679_12293.FStar_TypeChecker_Env.identifier_info);
                                  FStar_TypeChecker_Env.tc_hooks =
                                    (uu___1679_12293.FStar_TypeChecker_Env.tc_hooks);
                                  FStar_TypeChecker_Env.dsenv =
                                    (uu___1679_12293.FStar_TypeChecker_Env.dsenv);
                                  FStar_TypeChecker_Env.nbe =
                                    (uu___1679_12293.FStar_TypeChecker_Env.nbe);
                                  FStar_TypeChecker_Env.strict_args_tab =
                                    (uu___1679_12293.FStar_TypeChecker_Env.strict_args_tab);
                                  FStar_TypeChecker_Env.erasable_types_tab =
                                    (uu___1679_12293.FStar_TypeChecker_Env.erasable_types_tab)
                                }  in
                              let uu____12298 =
                                mk_irrelevant_goal "joined" nenv ng
                                  g1.FStar_Tactics_Types.opts
                                  g1.FStar_Tactics_Types.label
                                 in
                              bind uu____12298
                                (fun goal  ->
                                   mlog
                                     (fun uu____12308  ->
                                        let uu____12309 =
                                          goal_to_string_verbose g1  in
                                        let uu____12311 =
                                          goal_to_string_verbose g2  in
                                        let uu____12313 =
                                          goal_to_string_verbose goal  in
                                        FStar_Util.print3
                                          "join_goals of\n(%s)\nand\n(%s)\n= (%s)\n"
                                          uu____12309 uu____12311 uu____12313)
                                     (fun uu____12317  -> ret goal))))))
  
let (join : unit -> unit tac) =
  fun uu____12325  ->
    bind get
      (fun ps  ->
         match ps.FStar_Tactics_Types.goals with
         | g1::g2::gs ->
             let uu____12341 =
               set
                 (let uu___1694_12346 = ps  in
                  {
                    FStar_Tactics_Types.main_context =
                      (uu___1694_12346.FStar_Tactics_Types.main_context);
                    FStar_Tactics_Types.all_implicits =
                      (uu___1694_12346.FStar_Tactics_Types.all_implicits);
                    FStar_Tactics_Types.goals = gs;
                    FStar_Tactics_Types.smt_goals =
                      (uu___1694_12346.FStar_Tactics_Types.smt_goals);
                    FStar_Tactics_Types.depth =
                      (uu___1694_12346.FStar_Tactics_Types.depth);
                    FStar_Tactics_Types.__dump =
                      (uu___1694_12346.FStar_Tactics_Types.__dump);
                    FStar_Tactics_Types.psc =
                      (uu___1694_12346.FStar_Tactics_Types.psc);
                    FStar_Tactics_Types.entry_range =
                      (uu___1694_12346.FStar_Tactics_Types.entry_range);
                    FStar_Tactics_Types.guard_policy =
                      (uu___1694_12346.FStar_Tactics_Types.guard_policy);
                    FStar_Tactics_Types.freshness =
                      (uu___1694_12346.FStar_Tactics_Types.freshness);
                    FStar_Tactics_Types.tac_verb_dbg =
                      (uu___1694_12346.FStar_Tactics_Types.tac_verb_dbg);
                    FStar_Tactics_Types.local_state =
                      (uu___1694_12346.FStar_Tactics_Types.local_state)
                  })
                in
             bind uu____12341
               (fun uu____12349  ->
                  let uu____12350 = join_goals g1 g2  in
                  bind uu____12350 (fun g12  -> add_goals [g12]))
         | uu____12355 -> fail "join: less than 2 goals")
  
let (set_options : Prims.string -> unit tac) =
  fun s  ->
    let uu____12371 =
      let uu____12374 = cur_goal ()  in
      bind uu____12374
        (fun g  ->
           FStar_Options.push ();
           (let uu____12387 = FStar_Util.smap_copy g.FStar_Tactics_Types.opts
               in
            FStar_Options.set uu____12387);
           (let res = FStar_Options.set_options s  in
            let opts' = FStar_Options.peek ()  in
            FStar_Options.pop ();
            (match res with
             | FStar_Getopt.Success  ->
                 let g' =
                   let uu___1705_12394 = g  in
                   {
                     FStar_Tactics_Types.goal_main_env =
                       (uu___1705_12394.FStar_Tactics_Types.goal_main_env);
                     FStar_Tactics_Types.goal_ctx_uvar =
                       (uu___1705_12394.FStar_Tactics_Types.goal_ctx_uvar);
                     FStar_Tactics_Types.opts = opts';
                     FStar_Tactics_Types.is_guard =
                       (uu___1705_12394.FStar_Tactics_Types.is_guard);
                     FStar_Tactics_Types.label =
                       (uu___1705_12394.FStar_Tactics_Types.label)
                   }  in
                 replace_cur g'
             | FStar_Getopt.Error err ->
                 fail2 "Setting options `%s` failed: %s" s err
             | FStar_Getopt.Help  ->
                 fail1 "Setting options `%s` failed (got `Help`?)" s)))
       in
    FStar_All.pipe_left (wrap_err "set_options") uu____12371
  
let (top_env : unit -> env tac) =
  fun uu____12411  ->
    bind get
      (fun ps  -> FStar_All.pipe_left ret ps.FStar_Tactics_Types.main_context)
  
let (lax_on : unit -> Prims.bool tac) =
  fun uu____12426  ->
    let uu____12430 = cur_goal ()  in
    bind uu____12430
      (fun g  ->
         let uu____12437 =
           (FStar_Options.lax ()) ||
             (let uu____12440 = FStar_Tactics_Types.goal_env g  in
              uu____12440.FStar_TypeChecker_Env.lax)
            in
         ret uu____12437)
  
let (unquote :
  FStar_Reflection_Data.typ ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term tac)
  =
  fun ty  ->
    fun tm  ->
      let uu____12457 =
        mlog
          (fun uu____12462  ->
             let uu____12463 = FStar_Syntax_Print.term_to_string tm  in
             FStar_Util.print1 "unquote: tm = %s\n" uu____12463)
          (fun uu____12468  ->
             let uu____12469 = cur_goal ()  in
             bind uu____12469
               (fun goal  ->
                  let env =
                    let uu____12477 = FStar_Tactics_Types.goal_env goal  in
                    FStar_TypeChecker_Env.set_expected_typ uu____12477 ty  in
                  let uu____12478 = __tc_ghost env tm  in
                  bind uu____12478
                    (fun uu____12497  ->
                       match uu____12497 with
                       | (tm1,typ,guard) ->
                           mlog
                             (fun uu____12511  ->
                                let uu____12512 =
                                  FStar_Syntax_Print.term_to_string tm1  in
                                FStar_Util.print1 "unquote: tm' = %s\n"
                                  uu____12512)
                             (fun uu____12516  ->
                                mlog
                                  (fun uu____12519  ->
                                     let uu____12520 =
                                       FStar_Syntax_Print.term_to_string typ
                                        in
                                     FStar_Util.print1 "unquote: typ = %s\n"
                                       uu____12520)
                                  (fun uu____12525  ->
                                     let uu____12526 =
                                       proc_guard "unquote" env guard  in
                                     bind uu____12526
                                       (fun uu____12531  -> ret tm1))))))
         in
      FStar_All.pipe_left (wrap_err "unquote") uu____12457
  
let (uvar_env :
  env ->
    FStar_Reflection_Data.typ FStar_Pervasives_Native.option ->
      FStar_Syntax_Syntax.term tac)
  =
  fun env  ->
    fun ty  ->
      let uu____12556 =
        match ty with
        | FStar_Pervasives_Native.Some ty1 -> ret ty1
        | FStar_Pervasives_Native.None  ->
            let uu____12562 =
              let uu____12569 =
                let uu____12570 = FStar_Syntax_Util.type_u ()  in
                FStar_All.pipe_left FStar_Pervasives_Native.fst uu____12570
                 in
              new_uvar "uvar_env.2" env uu____12569  in
            bind uu____12562
              (fun uu____12587  ->
                 match uu____12587 with | (typ,uvar_typ) -> ret typ)
         in
      bind uu____12556
        (fun typ  ->
           let uu____12599 = new_uvar "uvar_env" env typ  in
           bind uu____12599
             (fun uu____12614  ->
                match uu____12614 with | (t,uvar_t) -> ret t))
  
let (unshelve : FStar_Syntax_Syntax.term -> unit tac) =
  fun t  ->
    let uu____12633 =
      bind get
        (fun ps  ->
           let env = ps.FStar_Tactics_Types.main_context  in
           let opts =
             match ps.FStar_Tactics_Types.goals with
             | g::uu____12652 -> g.FStar_Tactics_Types.opts
             | uu____12655 -> FStar_Options.peek ()  in
           let uu____12658 = FStar_Syntax_Util.head_and_args t  in
           match uu____12658 with
           | ({
                FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                  (ctx_uvar,uu____12678);
                FStar_Syntax_Syntax.pos = uu____12679;
                FStar_Syntax_Syntax.vars = uu____12680;_},uu____12681)
               ->
               let env1 =
                 let uu___1759_12723 = env  in
                 {
                   FStar_TypeChecker_Env.solver =
                     (uu___1759_12723.FStar_TypeChecker_Env.solver);
                   FStar_TypeChecker_Env.range =
                     (uu___1759_12723.FStar_TypeChecker_Env.range);
                   FStar_TypeChecker_Env.curmodule =
                     (uu___1759_12723.FStar_TypeChecker_Env.curmodule);
                   FStar_TypeChecker_Env.gamma =
                     (ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_gamma);
                   FStar_TypeChecker_Env.gamma_sig =
                     (uu___1759_12723.FStar_TypeChecker_Env.gamma_sig);
                   FStar_TypeChecker_Env.gamma_cache =
                     (uu___1759_12723.FStar_TypeChecker_Env.gamma_cache);
                   FStar_TypeChecker_Env.modules =
                     (uu___1759_12723.FStar_TypeChecker_Env.modules);
                   FStar_TypeChecker_Env.expected_typ =
                     (uu___1759_12723.FStar_TypeChecker_Env.expected_typ);
                   FStar_TypeChecker_Env.sigtab =
                     (uu___1759_12723.FStar_TypeChecker_Env.sigtab);
                   FStar_TypeChecker_Env.attrtab =
                     (uu___1759_12723.FStar_TypeChecker_Env.attrtab);
                   FStar_TypeChecker_Env.instantiate_imp =
                     (uu___1759_12723.FStar_TypeChecker_Env.instantiate_imp);
                   FStar_TypeChecker_Env.effects =
                     (uu___1759_12723.FStar_TypeChecker_Env.effects);
                   FStar_TypeChecker_Env.generalize =
                     (uu___1759_12723.FStar_TypeChecker_Env.generalize);
                   FStar_TypeChecker_Env.letrecs =
                     (uu___1759_12723.FStar_TypeChecker_Env.letrecs);
                   FStar_TypeChecker_Env.top_level =
                     (uu___1759_12723.FStar_TypeChecker_Env.top_level);
                   FStar_TypeChecker_Env.check_uvars =
                     (uu___1759_12723.FStar_TypeChecker_Env.check_uvars);
                   FStar_TypeChecker_Env.use_eq =
                     (uu___1759_12723.FStar_TypeChecker_Env.use_eq);
                   FStar_TypeChecker_Env.use_eq_strict =
                     (uu___1759_12723.FStar_TypeChecker_Env.use_eq_strict);
                   FStar_TypeChecker_Env.is_iface =
                     (uu___1759_12723.FStar_TypeChecker_Env.is_iface);
                   FStar_TypeChecker_Env.admit =
                     (uu___1759_12723.FStar_TypeChecker_Env.admit);
                   FStar_TypeChecker_Env.lax =
                     (uu___1759_12723.FStar_TypeChecker_Env.lax);
                   FStar_TypeChecker_Env.lax_universes =
                     (uu___1759_12723.FStar_TypeChecker_Env.lax_universes);
                   FStar_TypeChecker_Env.phase1 =
                     (uu___1759_12723.FStar_TypeChecker_Env.phase1);
                   FStar_TypeChecker_Env.failhard =
                     (uu___1759_12723.FStar_TypeChecker_Env.failhard);
                   FStar_TypeChecker_Env.nosynth =
                     (uu___1759_12723.FStar_TypeChecker_Env.nosynth);
                   FStar_TypeChecker_Env.uvar_subtyping =
                     (uu___1759_12723.FStar_TypeChecker_Env.uvar_subtyping);
                   FStar_TypeChecker_Env.tc_term =
                     (uu___1759_12723.FStar_TypeChecker_Env.tc_term);
                   FStar_TypeChecker_Env.type_of =
                     (uu___1759_12723.FStar_TypeChecker_Env.type_of);
                   FStar_TypeChecker_Env.universe_of =
                     (uu___1759_12723.FStar_TypeChecker_Env.universe_of);
                   FStar_TypeChecker_Env.check_type_of =
                     (uu___1759_12723.FStar_TypeChecker_Env.check_type_of);
                   FStar_TypeChecker_Env.use_bv_sorts =
                     (uu___1759_12723.FStar_TypeChecker_Env.use_bv_sorts);
                   FStar_TypeChecker_Env.qtbl_name_and_index =
                     (uu___1759_12723.FStar_TypeChecker_Env.qtbl_name_and_index);
                   FStar_TypeChecker_Env.normalized_eff_names =
                     (uu___1759_12723.FStar_TypeChecker_Env.normalized_eff_names);
                   FStar_TypeChecker_Env.fv_delta_depths =
                     (uu___1759_12723.FStar_TypeChecker_Env.fv_delta_depths);
                   FStar_TypeChecker_Env.proof_ns =
                     (uu___1759_12723.FStar_TypeChecker_Env.proof_ns);
                   FStar_TypeChecker_Env.synth_hook =
                     (uu___1759_12723.FStar_TypeChecker_Env.synth_hook);
                   FStar_TypeChecker_Env.try_solve_implicits_hook =
                     (uu___1759_12723.FStar_TypeChecker_Env.try_solve_implicits_hook);
                   FStar_TypeChecker_Env.splice =
                     (uu___1759_12723.FStar_TypeChecker_Env.splice);
                   FStar_TypeChecker_Env.mpreprocess =
                     (uu___1759_12723.FStar_TypeChecker_Env.mpreprocess);
                   FStar_TypeChecker_Env.postprocess =
                     (uu___1759_12723.FStar_TypeChecker_Env.postprocess);
                   FStar_TypeChecker_Env.is_native_tactic =
                     (uu___1759_12723.FStar_TypeChecker_Env.is_native_tactic);
                   FStar_TypeChecker_Env.identifier_info =
                     (uu___1759_12723.FStar_TypeChecker_Env.identifier_info);
                   FStar_TypeChecker_Env.tc_hooks =
                     (uu___1759_12723.FStar_TypeChecker_Env.tc_hooks);
                   FStar_TypeChecker_Env.dsenv =
                     (uu___1759_12723.FStar_TypeChecker_Env.dsenv);
                   FStar_TypeChecker_Env.nbe =
                     (uu___1759_12723.FStar_TypeChecker_Env.nbe);
                   FStar_TypeChecker_Env.strict_args_tab =
                     (uu___1759_12723.FStar_TypeChecker_Env.strict_args_tab);
                   FStar_TypeChecker_Env.erasable_types_tab =
                     (uu___1759_12723.FStar_TypeChecker_Env.erasable_types_tab)
                 }  in
               let g =
                 FStar_Tactics_Types.mk_goal env1 ctx_uvar opts false ""  in
               let uu____12727 =
                 let uu____12730 = bnorm_goal g  in [uu____12730]  in
               add_goals uu____12727
           | uu____12731 -> fail "not a uvar")
       in
    FStar_All.pipe_left (wrap_err "unshelve") uu____12633
  
let (tac_and : Prims.bool tac -> Prims.bool tac -> Prims.bool tac) =
  fun t1  ->
    fun t2  ->
      let comp =
        bind t1
          (fun b  ->
             let uu____12793 = if b then t2 else ret false  in
             bind uu____12793 (fun b'  -> if b' then ret b' else fail ""))
         in
      let uu____12819 = trytac comp  in
      bind uu____12819
        (fun uu___6_12831  ->
           match uu___6_12831 with
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
        let uu____12873 =
          bind get
            (fun ps  ->
               let uu____12881 = __tc e t1  in
               bind uu____12881
                 (fun uu____12902  ->
                    match uu____12902 with
                    | (t11,ty1,g1) ->
                        let uu____12915 = __tc e t2  in
                        bind uu____12915
                          (fun uu____12936  ->
                             match uu____12936 with
                             | (t21,ty2,g2) ->
                                 let uu____12949 =
                                   proc_guard "unify_env g1" e g1  in
                                 bind uu____12949
                                   (fun uu____12956  ->
                                      let uu____12957 =
                                        proc_guard "unify_env g2" e g2  in
                                      bind uu____12957
                                        (fun uu____12965  ->
                                           let uu____12966 =
                                             do_unify e ty1 ty2  in
                                           let uu____12970 =
                                             do_unify e t11 t21  in
                                           tac_and uu____12966 uu____12970)))))
           in
        FStar_All.pipe_left (wrap_err "unify_env") uu____12873
  
let (launch_process :
  Prims.string -> Prims.string Prims.list -> Prims.string -> Prims.string tac)
  =
  fun prog  ->
    fun args  ->
      fun input  ->
        bind idtac
          (fun uu____13018  ->
             let uu____13019 = FStar_Options.unsafe_tactic_exec ()  in
             if uu____13019
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
        (fun uu____13053  ->
           let uu____13054 =
             FStar_Syntax_Syntax.gen_bv nm FStar_Pervasives_Native.None t  in
           ret uu____13054)
  
let (change : FStar_Reflection_Data.typ -> unit tac) =
  fun ty  ->
    let uu____13065 =
      mlog
        (fun uu____13070  ->
           let uu____13071 = FStar_Syntax_Print.term_to_string ty  in
           FStar_Util.print1 "change: ty = %s\n" uu____13071)
        (fun uu____13076  ->
           let uu____13077 = cur_goal ()  in
           bind uu____13077
             (fun g  ->
                let uu____13083 =
                  let uu____13092 = FStar_Tactics_Types.goal_env g  in
                  __tc uu____13092 ty  in
                bind uu____13083
                  (fun uu____13104  ->
                     match uu____13104 with
                     | (ty1,uu____13114,guard) ->
                         let uu____13116 =
                           let uu____13119 = FStar_Tactics_Types.goal_env g
                              in
                           proc_guard "change" uu____13119 guard  in
                         bind uu____13116
                           (fun uu____13123  ->
                              let uu____13124 =
                                let uu____13128 =
                                  FStar_Tactics_Types.goal_env g  in
                                let uu____13129 =
                                  FStar_Tactics_Types.goal_type g  in
                                do_unify uu____13128 uu____13129 ty1  in
                              bind uu____13124
                                (fun bb  ->
                                   if bb
                                   then
                                     let uu____13138 =
                                       FStar_Tactics_Types.goal_with_type g
                                         ty1
                                        in
                                     replace_cur uu____13138
                                   else
                                     (let steps =
                                        [FStar_TypeChecker_Env.AllowUnboundUniverses;
                                        FStar_TypeChecker_Env.UnfoldUntil
                                          FStar_Syntax_Syntax.delta_constant;
                                        FStar_TypeChecker_Env.Primops]  in
                                      let ng =
                                        let uu____13145 =
                                          FStar_Tactics_Types.goal_env g  in
                                        let uu____13146 =
                                          FStar_Tactics_Types.goal_type g  in
                                        normalize steps uu____13145
                                          uu____13146
                                         in
                                      let nty =
                                        let uu____13148 =
                                          FStar_Tactics_Types.goal_env g  in
                                        normalize steps uu____13148 ty1  in
                                      let uu____13149 =
                                        let uu____13153 =
                                          FStar_Tactics_Types.goal_env g  in
                                        do_unify uu____13153 ng nty  in
                                      bind uu____13149
                                        (fun b  ->
                                           if b
                                           then
                                             let uu____13162 =
                                               FStar_Tactics_Types.goal_with_type
                                                 g ty1
                                                in
                                             replace_cur uu____13162
                                           else fail "not convertible")))))))
       in
    FStar_All.pipe_left (wrap_err "change") uu____13065
  
let failwhen : 'a . Prims.bool -> Prims.string -> (unit -> 'a tac) -> 'a tac
  = fun b  -> fun msg  -> fun k  -> if b then fail msg else k () 
let (t_destruct :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.fv * FStar_BigInt.t) Prims.list tac)
  =
  fun s_tm  ->
    let uu____13236 =
      let uu____13245 = cur_goal ()  in
      bind uu____13245
        (fun g  ->
           let uu____13257 =
             let uu____13266 = FStar_Tactics_Types.goal_env g  in
             __tc uu____13266 s_tm  in
           bind uu____13257
             (fun uu____13284  ->
                match uu____13284 with
                | (s_tm1,s_ty,guard) ->
                    let uu____13302 =
                      let uu____13305 = FStar_Tactics_Types.goal_env g  in
                      proc_guard "destruct" uu____13305 guard  in
                    bind uu____13302
                      (fun uu____13319  ->
                         let s_ty1 =
                           let uu____13321 = FStar_Tactics_Types.goal_env g
                              in
                           FStar_TypeChecker_Normalize.normalize
                             [FStar_TypeChecker_Env.UnfoldTac;
                             FStar_TypeChecker_Env.Weak;
                             FStar_TypeChecker_Env.HNF;
                             FStar_TypeChecker_Env.UnfoldUntil
                               FStar_Syntax_Syntax.delta_constant]
                             uu____13321 s_ty
                            in
                         let uu____13322 =
                           FStar_Syntax_Util.head_and_args' s_ty1  in
                         match uu____13322 with
                         | (h,args) ->
                             let uu____13367 =
                               let uu____13374 =
                                 let uu____13375 =
                                   FStar_Syntax_Subst.compress h  in
                                 uu____13375.FStar_Syntax_Syntax.n  in
                               match uu____13374 with
                               | FStar_Syntax_Syntax.Tm_fvar fv ->
                                   ret (fv, [])
                               | FStar_Syntax_Syntax.Tm_uinst
                                   ({
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.Tm_fvar fv;
                                      FStar_Syntax_Syntax.pos = uu____13390;
                                      FStar_Syntax_Syntax.vars = uu____13391;_},us)
                                   -> ret (fv, us)
                               | uu____13401 -> fail "type is not an fv"  in
                             bind uu____13367
                               (fun uu____13422  ->
                                  match uu____13422 with
                                  | (fv,a_us) ->
                                      let t_lid =
                                        FStar_Syntax_Syntax.lid_of_fv fv  in
                                      let uu____13438 =
                                        let uu____13441 =
                                          FStar_Tactics_Types.goal_env g  in
                                        FStar_TypeChecker_Env.lookup_sigelt
                                          uu____13441 t_lid
                                         in
                                      (match uu____13438 with
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
                                                let uu____13482 =
                                                  erasable &&
                                                    (let uu____13485 =
                                                       is_irrelevant g  in
                                                     Prims.op_Negation
                                                       uu____13485)
                                                   in
                                                failwhen uu____13482
                                                  "cannot destruct erasable type to solve proof-relevant goal"
                                                  (fun uu____13495  ->
                                                     failwhen
                                                       ((FStar_List.length
                                                           a_us)
                                                          <>
                                                          (FStar_List.length
                                                             t_us))
                                                       "t_us don't match?"
                                                       (fun uu____13508  ->
                                                          let uu____13509 =
                                                            FStar_Syntax_Subst.open_term
                                                              t_ps t_ty
                                                             in
                                                          match uu____13509
                                                          with
                                                          | (t_ps1,t_ty1) ->
                                                              let uu____13524
                                                                =
                                                                mapM
                                                                  (fun c_lid 
                                                                    ->
                                                                    let uu____13552
                                                                    =
                                                                    let uu____13555
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    g  in
                                                                    FStar_TypeChecker_Env.lookup_sigelt
                                                                    uu____13555
                                                                    c_lid  in
                                                                    match uu____13552
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
                                                                    uu____13632
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
                                                                    let uu____13637
                                                                    =
                                                                    FStar_TypeChecker_Env.inst_tscheme
                                                                    (c_us,
                                                                    c_ty1)
                                                                     in
                                                                    match uu____13637
                                                                    with
                                                                    | 
                                                                    (c_us1,c_ty2)
                                                                    ->
                                                                    let uu____13660
                                                                    =
                                                                    FStar_Syntax_Util.arrow_formals_comp
                                                                    c_ty2  in
                                                                    (match uu____13660
                                                                    with
                                                                    | 
                                                                    (bs,comp)
                                                                    ->
                                                                    let uu____13679
                                                                    =
                                                                    let rename_bv
                                                                    bv =
                                                                    let ppname
                                                                    =
                                                                    bv.FStar_Syntax_Syntax.ppname
                                                                     in
                                                                    let ppname1
                                                                    =
                                                                    let uu___1886_13702
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
                                                                    (uu___1886_13702.FStar_Ident.idRange)
                                                                    }  in
                                                                    FStar_Syntax_Syntax.freshen_bv
                                                                    (let uu___1889_13706
                                                                    = bv  in
                                                                    {
                                                                    FStar_Syntax_Syntax.ppname
                                                                    = ppname1;
                                                                    FStar_Syntax_Syntax.index
                                                                    =
                                                                    (uu___1889_13706.FStar_Syntax_Syntax.index);
                                                                    FStar_Syntax_Syntax.sort
                                                                    =
                                                                    (uu___1889_13706.FStar_Syntax_Syntax.sort)
                                                                    })  in
                                                                    let bs' =
                                                                    FStar_List.map
                                                                    (fun
                                                                    uu____13732
                                                                     ->
                                                                    match uu____13732
                                                                    with
                                                                    | 
                                                                    (bv,aq)
                                                                    ->
                                                                    let uu____13751
                                                                    =
                                                                    rename_bv
                                                                    bv  in
                                                                    (uu____13751,
                                                                    aq)) bs
                                                                     in
                                                                    let subst1
                                                                    =
                                                                    FStar_List.map2
                                                                    (fun
                                                                    uu____13776
                                                                     ->
                                                                    fun
                                                                    uu____13777
                                                                     ->
                                                                    match 
                                                                    (uu____13776,
                                                                    uu____13777)
                                                                    with
                                                                    | 
                                                                    ((bv,uu____13803),
                                                                    (bv',uu____13805))
                                                                    ->
                                                                    let uu____13826
                                                                    =
                                                                    let uu____13833
                                                                    =
                                                                    FStar_Syntax_Syntax.bv_to_name
                                                                    bv'  in
                                                                    (bv,
                                                                    uu____13833)
                                                                     in
                                                                    FStar_Syntax_Syntax.NT
                                                                    uu____13826)
                                                                    bs bs'
                                                                     in
                                                                    let uu____13838
                                                                    =
                                                                    FStar_Syntax_Subst.subst_binders
                                                                    subst1
                                                                    bs'  in
                                                                    let uu____13847
                                                                    =
                                                                    FStar_Syntax_Subst.subst_comp
                                                                    subst1
                                                                    comp  in
                                                                    (uu____13838,
                                                                    uu____13847)
                                                                     in
                                                                    (match uu____13679
                                                                    with
                                                                    | 
                                                                    (bs1,comp1)
                                                                    ->
                                                                    let uu____13894
                                                                    =
                                                                    FStar_List.splitAt
                                                                    nparam
                                                                    bs1  in
                                                                    (match uu____13894
                                                                    with
                                                                    | 
                                                                    (d_ps,bs2)
                                                                    ->
                                                                    let uu____13967
                                                                    =
                                                                    let uu____13969
                                                                    =
                                                                    FStar_Syntax_Util.is_total_comp
                                                                    comp1  in
                                                                    Prims.op_Negation
                                                                    uu____13969
                                                                     in
                                                                    failwhen
                                                                    uu____13967
                                                                    "not total?"
                                                                    (fun
                                                                    uu____13988
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
                                                                    uu___7_14005
                                                                    =
                                                                    match uu___7_14005
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    (FStar_Syntax_Syntax.Implicit
                                                                    uu____14009)
                                                                    -> true
                                                                    | 
                                                                    uu____14012
                                                                    -> false
                                                                     in
                                                                    let uu____14016
                                                                    =
                                                                    FStar_List.splitAt
                                                                    nparam
                                                                    args  in
                                                                    match uu____14016
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
                                                                    uu____14152
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
                                                                    uu____14214
                                                                     ->
                                                                    match uu____14214
                                                                    with
                                                                    | 
                                                                    ((bv,uu____14234),
                                                                    (t,uu____14236))
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
                                                                    uu____14306
                                                                     ->
                                                                    match uu____14306
                                                                    with
                                                                    | 
                                                                    ((bv,uu____14333),
                                                                    (t,uu____14335))
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
                                                                    uu____14394
                                                                     ->
                                                                    match uu____14394
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
                                                                    let uu____14449
                                                                    =
                                                                    FStar_TypeChecker_TcTerm.tc_pat
                                                                    (let uu___1948_14473
                                                                    = env  in
                                                                    {
                                                                    FStar_TypeChecker_Env.solver
                                                                    =
                                                                    (uu___1948_14473.FStar_TypeChecker_Env.solver);
                                                                    FStar_TypeChecker_Env.range
                                                                    =
                                                                    (uu___1948_14473.FStar_TypeChecker_Env.range);
                                                                    FStar_TypeChecker_Env.curmodule
                                                                    =
                                                                    (uu___1948_14473.FStar_TypeChecker_Env.curmodule);
                                                                    FStar_TypeChecker_Env.gamma
                                                                    =
                                                                    (uu___1948_14473.FStar_TypeChecker_Env.gamma);
                                                                    FStar_TypeChecker_Env.gamma_sig
                                                                    =
                                                                    (uu___1948_14473.FStar_TypeChecker_Env.gamma_sig);
                                                                    FStar_TypeChecker_Env.gamma_cache
                                                                    =
                                                                    (uu___1948_14473.FStar_TypeChecker_Env.gamma_cache);
                                                                    FStar_TypeChecker_Env.modules
                                                                    =
                                                                    (uu___1948_14473.FStar_TypeChecker_Env.modules);
                                                                    FStar_TypeChecker_Env.expected_typ
                                                                    =
                                                                    (uu___1948_14473.FStar_TypeChecker_Env.expected_typ);
                                                                    FStar_TypeChecker_Env.sigtab
                                                                    =
                                                                    (uu___1948_14473.FStar_TypeChecker_Env.sigtab);
                                                                    FStar_TypeChecker_Env.attrtab
                                                                    =
                                                                    (uu___1948_14473.FStar_TypeChecker_Env.attrtab);
                                                                    FStar_TypeChecker_Env.instantiate_imp
                                                                    =
                                                                    (uu___1948_14473.FStar_TypeChecker_Env.instantiate_imp);
                                                                    FStar_TypeChecker_Env.effects
                                                                    =
                                                                    (uu___1948_14473.FStar_TypeChecker_Env.effects);
                                                                    FStar_TypeChecker_Env.generalize
                                                                    =
                                                                    (uu___1948_14473.FStar_TypeChecker_Env.generalize);
                                                                    FStar_TypeChecker_Env.letrecs
                                                                    =
                                                                    (uu___1948_14473.FStar_TypeChecker_Env.letrecs);
                                                                    FStar_TypeChecker_Env.top_level
                                                                    =
                                                                    (uu___1948_14473.FStar_TypeChecker_Env.top_level);
                                                                    FStar_TypeChecker_Env.check_uvars
                                                                    =
                                                                    (uu___1948_14473.FStar_TypeChecker_Env.check_uvars);
                                                                    FStar_TypeChecker_Env.use_eq
                                                                    =
                                                                    (uu___1948_14473.FStar_TypeChecker_Env.use_eq);
                                                                    FStar_TypeChecker_Env.use_eq_strict
                                                                    =
                                                                    (uu___1948_14473.FStar_TypeChecker_Env.use_eq_strict);
                                                                    FStar_TypeChecker_Env.is_iface
                                                                    =
                                                                    (uu___1948_14473.FStar_TypeChecker_Env.is_iface);
                                                                    FStar_TypeChecker_Env.admit
                                                                    =
                                                                    (uu___1948_14473.FStar_TypeChecker_Env.admit);
                                                                    FStar_TypeChecker_Env.lax
                                                                    = true;
                                                                    FStar_TypeChecker_Env.lax_universes
                                                                    =
                                                                    (uu___1948_14473.FStar_TypeChecker_Env.lax_universes);
                                                                    FStar_TypeChecker_Env.phase1
                                                                    =
                                                                    (uu___1948_14473.FStar_TypeChecker_Env.phase1);
                                                                    FStar_TypeChecker_Env.failhard
                                                                    =
                                                                    (uu___1948_14473.FStar_TypeChecker_Env.failhard);
                                                                    FStar_TypeChecker_Env.nosynth
                                                                    =
                                                                    (uu___1948_14473.FStar_TypeChecker_Env.nosynth);
                                                                    FStar_TypeChecker_Env.uvar_subtyping
                                                                    =
                                                                    (uu___1948_14473.FStar_TypeChecker_Env.uvar_subtyping);
                                                                    FStar_TypeChecker_Env.tc_term
                                                                    =
                                                                    (uu___1948_14473.FStar_TypeChecker_Env.tc_term);
                                                                    FStar_TypeChecker_Env.type_of
                                                                    =
                                                                    (uu___1948_14473.FStar_TypeChecker_Env.type_of);
                                                                    FStar_TypeChecker_Env.universe_of
                                                                    =
                                                                    (uu___1948_14473.FStar_TypeChecker_Env.universe_of);
                                                                    FStar_TypeChecker_Env.check_type_of
                                                                    =
                                                                    (uu___1948_14473.FStar_TypeChecker_Env.check_type_of);
                                                                    FStar_TypeChecker_Env.use_bv_sorts
                                                                    =
                                                                    (uu___1948_14473.FStar_TypeChecker_Env.use_bv_sorts);
                                                                    FStar_TypeChecker_Env.qtbl_name_and_index
                                                                    =
                                                                    (uu___1948_14473.FStar_TypeChecker_Env.qtbl_name_and_index);
                                                                    FStar_TypeChecker_Env.normalized_eff_names
                                                                    =
                                                                    (uu___1948_14473.FStar_TypeChecker_Env.normalized_eff_names);
                                                                    FStar_TypeChecker_Env.fv_delta_depths
                                                                    =
                                                                    (uu___1948_14473.FStar_TypeChecker_Env.fv_delta_depths);
                                                                    FStar_TypeChecker_Env.proof_ns
                                                                    =
                                                                    (uu___1948_14473.FStar_TypeChecker_Env.proof_ns);
                                                                    FStar_TypeChecker_Env.synth_hook
                                                                    =
                                                                    (uu___1948_14473.FStar_TypeChecker_Env.synth_hook);
                                                                    FStar_TypeChecker_Env.try_solve_implicits_hook
                                                                    =
                                                                    (uu___1948_14473.FStar_TypeChecker_Env.try_solve_implicits_hook);
                                                                    FStar_TypeChecker_Env.splice
                                                                    =
                                                                    (uu___1948_14473.FStar_TypeChecker_Env.splice);
                                                                    FStar_TypeChecker_Env.mpreprocess
                                                                    =
                                                                    (uu___1948_14473.FStar_TypeChecker_Env.mpreprocess);
                                                                    FStar_TypeChecker_Env.postprocess
                                                                    =
                                                                    (uu___1948_14473.FStar_TypeChecker_Env.postprocess);
                                                                    FStar_TypeChecker_Env.is_native_tactic
                                                                    =
                                                                    (uu___1948_14473.FStar_TypeChecker_Env.is_native_tactic);
                                                                    FStar_TypeChecker_Env.identifier_info
                                                                    =
                                                                    (uu___1948_14473.FStar_TypeChecker_Env.identifier_info);
                                                                    FStar_TypeChecker_Env.tc_hooks
                                                                    =
                                                                    (uu___1948_14473.FStar_TypeChecker_Env.tc_hooks);
                                                                    FStar_TypeChecker_Env.dsenv
                                                                    =
                                                                    (uu___1948_14473.FStar_TypeChecker_Env.dsenv);
                                                                    FStar_TypeChecker_Env.nbe
                                                                    =
                                                                    (uu___1948_14473.FStar_TypeChecker_Env.nbe);
                                                                    FStar_TypeChecker_Env.strict_args_tab
                                                                    =
                                                                    (uu___1948_14473.FStar_TypeChecker_Env.strict_args_tab);
                                                                    FStar_TypeChecker_Env.erasable_types_tab
                                                                    =
                                                                    (uu___1948_14473.FStar_TypeChecker_Env.erasable_types_tab)
                                                                    }) s_ty1
                                                                    pat  in
                                                                    match uu____14449
                                                                    with
                                                                    | 
                                                                    (uu____14487,uu____14488,uu____14489,uu____14490,pat_t,uu____14492,_guard_pat,_erasable)
                                                                    ->
                                                                    let eq_b
                                                                    =
                                                                    let uu____14506
                                                                    =
                                                                    let uu____14507
                                                                    =
                                                                    FStar_Syntax_Util.mk_eq2
                                                                    equ s_ty1
                                                                    s_tm1
                                                                    pat_t  in
                                                                    FStar_Syntax_Util.mk_squash
                                                                    equ
                                                                    uu____14507
                                                                     in
                                                                    FStar_Syntax_Syntax.gen_bv
                                                                    "breq"
                                                                    FStar_Pervasives_Native.None
                                                                    uu____14506
                                                                     in
                                                                    let cod1
                                                                    =
                                                                    let uu____14512
                                                                    =
                                                                    let uu____14521
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_binder
                                                                    eq_b  in
                                                                    [uu____14521]
                                                                     in
                                                                    let uu____14540
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Total
                                                                    cod  in
                                                                    FStar_Syntax_Util.arrow
                                                                    uu____14512
                                                                    uu____14540
                                                                     in
                                                                    let nty =
                                                                    let uu____14546
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Total
                                                                    cod1  in
                                                                    FStar_Syntax_Util.arrow
                                                                    bs3
                                                                    uu____14546
                                                                     in
                                                                    let uu____14549
                                                                    =
                                                                    new_uvar
                                                                    "destruct branch"
                                                                    env nty
                                                                     in
                                                                    bind
                                                                    uu____14549
                                                                    (fun
                                                                    uu____14579
                                                                     ->
                                                                    match uu____14579
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
                                                                    let uu____14606
                                                                    =
                                                                    let uu____14617
                                                                    =
                                                                    FStar_Syntax_Syntax.as_arg
                                                                    FStar_Syntax_Util.exp_unit
                                                                     in
                                                                    [uu____14617]
                                                                     in
                                                                    FStar_Syntax_Util.mk_app
                                                                    brt
                                                                    uu____14606
                                                                     in
                                                                    let br =
                                                                    FStar_Syntax_Subst.close_branch
                                                                    (pat,
                                                                    FStar_Pervasives_Native.None,
                                                                    brt1)  in
                                                                    let uu____14653
                                                                    =
                                                                    let uu____14664
                                                                    =
                                                                    let uu____14669
                                                                    =
                                                                    FStar_BigInt.of_int_fs
                                                                    (FStar_List.length
                                                                    bs3)  in
                                                                    (fv1,
                                                                    uu____14669)
                                                                     in
                                                                    (g', br,
                                                                    uu____14664)
                                                                     in
                                                                    ret
                                                                    uu____14653)))))))
                                                                    | 
                                                                    uu____14690
                                                                    ->
                                                                    fail
                                                                    "impossible: not a ctor"))
                                                                  c_lids
                                                                 in
                                                              bind
                                                                uu____13524
                                                                (fun goal_brs
                                                                    ->
                                                                   let uu____14740
                                                                    =
                                                                    FStar_List.unzip3
                                                                    goal_brs
                                                                     in
                                                                   match uu____14740
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
                                                                    let uu____14813
                                                                    =
                                                                    solve' g
                                                                    w  in
                                                                    bind
                                                                    uu____14813
                                                                    (fun
                                                                    uu____14824
                                                                     ->
                                                                    let uu____14825
                                                                    =
                                                                    add_goals
                                                                    goals  in
                                                                    bind
                                                                    uu____14825
                                                                    (fun
                                                                    uu____14835
                                                                     ->
                                                                    ret infos)))))
                                            | uu____14842 ->
                                                fail "not an inductive type"))))))
       in
    FStar_All.pipe_left (wrap_err "destruct") uu____13236
  
let rec last : 'a . 'a Prims.list -> 'a =
  fun l  ->
    match l with
    | [] -> failwith "last: empty list"
    | x::[] -> x
    | uu____14891::xs -> last xs
  
let rec init : 'a . 'a Prims.list -> 'a Prims.list =
  fun l  ->
    match l with
    | [] -> failwith "init: empty list"
    | x::[] -> []
    | x::xs -> let uu____14921 = init xs  in x :: uu____14921
  
let rec (inspect :
  FStar_Syntax_Syntax.term -> FStar_Reflection_Data.term_view tac) =
  fun t  ->
    let uu____14934 =
      let t1 = FStar_Syntax_Util.unascribe t  in
      let t2 = FStar_Syntax_Util.un_uinst t1  in
      let t3 = FStar_Syntax_Util.unlazy_emb t2  in
      match t3.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_meta (t4,uu____14943) -> inspect t4
      | FStar_Syntax_Syntax.Tm_name bv ->
          FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_Var bv)
      | FStar_Syntax_Syntax.Tm_bvar bv ->
          FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_BVar bv)
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_FVar fv)
      | FStar_Syntax_Syntax.Tm_app (hd1,[]) ->
          failwith "empty arguments on Tm_app"
      | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
          let uu____15009 = last args  in
          (match uu____15009 with
           | (a,q) ->
               let q' = FStar_Reflection_Basic.inspect_aqual q  in
               let uu____15039 =
                 let uu____15040 =
                   let uu____15045 =
                     let uu____15046 =
                       let uu____15051 = init args  in
                       FStar_Syntax_Syntax.mk_Tm_app hd1 uu____15051  in
                     uu____15046 FStar_Pervasives_Native.None
                       t3.FStar_Syntax_Syntax.pos
                      in
                   (uu____15045, (a, q'))  in
                 FStar_Reflection_Data.Tv_App uu____15040  in
               FStar_All.pipe_left ret uu____15039)
      | FStar_Syntax_Syntax.Tm_abs ([],uu____15062,uu____15063) ->
          failwith "empty arguments on Tm_abs"
      | FStar_Syntax_Syntax.Tm_abs (bs,t4,k) ->
          let uu____15116 = FStar_Syntax_Subst.open_term bs t4  in
          (match uu____15116 with
           | (bs1,t5) ->
               (match bs1 with
                | [] -> failwith "impossible"
                | b::bs2 ->
                    let uu____15158 =
                      let uu____15159 =
                        let uu____15164 = FStar_Syntax_Util.abs bs2 t5 k  in
                        (b, uu____15164)  in
                      FStar_Reflection_Data.Tv_Abs uu____15159  in
                    FStar_All.pipe_left ret uu____15158))
      | FStar_Syntax_Syntax.Tm_type uu____15167 ->
          FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_Type ())
      | FStar_Syntax_Syntax.Tm_arrow ([],k) ->
          failwith "empty binders on arrow"
      | FStar_Syntax_Syntax.Tm_arrow uu____15192 ->
          let uu____15207 = FStar_Syntax_Util.arrow_one t3  in
          (match uu____15207 with
           | FStar_Pervasives_Native.Some (b,c) ->
               FStar_All.pipe_left ret
                 (FStar_Reflection_Data.Tv_Arrow (b, c))
           | FStar_Pervasives_Native.None  -> failwith "impossible")
      | FStar_Syntax_Syntax.Tm_refine (bv,t4) ->
          let b = FStar_Syntax_Syntax.mk_binder bv  in
          let uu____15238 = FStar_Syntax_Subst.open_term [b] t4  in
          (match uu____15238 with
           | (b',t5) ->
               let b1 =
                 match b' with
                 | b'1::[] -> b'1
                 | uu____15291 -> failwith "impossible"  in
               FStar_All.pipe_left ret
                 (FStar_Reflection_Data.Tv_Refine
                    ((FStar_Pervasives_Native.fst b1), t5)))
      | FStar_Syntax_Syntax.Tm_constant c ->
          let uu____15304 =
            let uu____15305 = FStar_Reflection_Basic.inspect_const c  in
            FStar_Reflection_Data.Tv_Const uu____15305  in
          FStar_All.pipe_left ret uu____15304
      | FStar_Syntax_Syntax.Tm_uvar (ctx_u,s) ->
          let uu____15326 =
            let uu____15327 =
              let uu____15332 =
                let uu____15333 =
                  FStar_Syntax_Unionfind.uvar_id
                    ctx_u.FStar_Syntax_Syntax.ctx_uvar_head
                   in
                FStar_BigInt.of_int_fs uu____15333  in
              (uu____15332, (ctx_u, s))  in
            FStar_Reflection_Data.Tv_Uvar uu____15327  in
          FStar_All.pipe_left ret uu____15326
      | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),t21) ->
          if lb.FStar_Syntax_Syntax.lbunivs <> []
          then FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown
          else
            (match lb.FStar_Syntax_Syntax.lbname with
             | FStar_Util.Inr uu____15373 ->
                 FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown
             | FStar_Util.Inl bv ->
                 let b = FStar_Syntax_Syntax.mk_binder bv  in
                 let uu____15378 = FStar_Syntax_Subst.open_term [b] t21  in
                 (match uu____15378 with
                  | (bs,t22) ->
                      let b1 =
                        match bs with
                        | b1::[] -> b1
                        | uu____15431 ->
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
             | FStar_Util.Inr uu____15475 ->
                 FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown
             | FStar_Util.Inl bv ->
                 let uu____15479 = FStar_Syntax_Subst.open_let_rec [lb] t21
                    in
                 (match uu____15479 with
                  | (lbs,t22) ->
                      (match lbs with
                       | lb1::[] ->
                           (match lb1.FStar_Syntax_Syntax.lbname with
                            | FStar_Util.Inr uu____15499 ->
                                ret FStar_Reflection_Data.Tv_Unknown
                            | FStar_Util.Inl bv1 ->
                                FStar_All.pipe_left ret
                                  (FStar_Reflection_Data.Tv_Let
                                     (true,
                                       (lb1.FStar_Syntax_Syntax.lbattrs),
                                       bv1, (lb1.FStar_Syntax_Syntax.lbdef),
                                       t22)))
                       | uu____15507 ->
                           failwith
                             "impossible: open_term returned different amount of binders")))
      | FStar_Syntax_Syntax.Tm_match (t4,brs) ->
          let rec inspect_pat p =
            match p.FStar_Syntax_Syntax.v with
            | FStar_Syntax_Syntax.Pat_constant c ->
                let uu____15562 = FStar_Reflection_Basic.inspect_const c  in
                FStar_Reflection_Data.Pat_Constant uu____15562
            | FStar_Syntax_Syntax.Pat_cons (fv,ps) ->
                let uu____15583 =
                  let uu____15595 =
                    FStar_List.map
                      (fun uu____15619  ->
                         match uu____15619 with
                         | (p1,b) ->
                             let uu____15640 = inspect_pat p1  in
                             (uu____15640, b)) ps
                     in
                  (fv, uu____15595)  in
                FStar_Reflection_Data.Pat_Cons uu____15583
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
              (fun uu___8_15736  ->
                 match uu___8_15736 with
                 | (pat,uu____15758,t5) ->
                     let uu____15776 = inspect_pat pat  in (uu____15776, t5))
              brs1
             in
          FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_Match (t4, brs2))
      | FStar_Syntax_Syntax.Tm_unknown  ->
          FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown
      | uu____15785 ->
          ((let uu____15787 =
              let uu____15793 =
                let uu____15795 = FStar_Syntax_Print.tag_of_term t3  in
                let uu____15797 = FStar_Syntax_Print.term_to_string t3  in
                FStar_Util.format2
                  "inspect: outside of expected syntax (%s, %s)\n"
                  uu____15795 uu____15797
                 in
              (FStar_Errors.Warning_CantInspect, uu____15793)  in
            FStar_Errors.log_issue t3.FStar_Syntax_Syntax.pos uu____15787);
           FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown)
       in
    wrap_err "inspect" uu____14934
  
let (pack : FStar_Reflection_Data.term_view -> FStar_Syntax_Syntax.term tac)
  =
  fun tv  ->
    match tv with
    | FStar_Reflection_Data.Tv_Var bv ->
        let uu____15815 = FStar_Syntax_Syntax.bv_to_name bv  in
        FStar_All.pipe_left ret uu____15815
    | FStar_Reflection_Data.Tv_BVar bv ->
        let uu____15819 = FStar_Syntax_Syntax.bv_to_tm bv  in
        FStar_All.pipe_left ret uu____15819
    | FStar_Reflection_Data.Tv_FVar fv ->
        let uu____15823 = FStar_Syntax_Syntax.fv_to_tm fv  in
        FStar_All.pipe_left ret uu____15823
    | FStar_Reflection_Data.Tv_App (l,(r,q)) ->
        let q' = FStar_Reflection_Basic.pack_aqual q  in
        let uu____15830 = FStar_Syntax_Util.mk_app l [(r, q')]  in
        FStar_All.pipe_left ret uu____15830
    | FStar_Reflection_Data.Tv_Abs (b,t) ->
        let uu____15855 =
          FStar_Syntax_Util.abs [b] t FStar_Pervasives_Native.None  in
        FStar_All.pipe_left ret uu____15855
    | FStar_Reflection_Data.Tv_Arrow (b,c) ->
        let uu____15872 = FStar_Syntax_Util.arrow [b] c  in
        FStar_All.pipe_left ret uu____15872
    | FStar_Reflection_Data.Tv_Type () ->
        FStar_All.pipe_left ret FStar_Syntax_Util.ktype
    | FStar_Reflection_Data.Tv_Refine (bv,t) ->
        let uu____15891 = FStar_Syntax_Util.refine bv t  in
        FStar_All.pipe_left ret uu____15891
    | FStar_Reflection_Data.Tv_Const c ->
        let uu____15895 =
          let uu____15896 =
            let uu____15903 =
              let uu____15904 = FStar_Reflection_Basic.pack_const c  in
              FStar_Syntax_Syntax.Tm_constant uu____15904  in
            FStar_Syntax_Syntax.mk uu____15903  in
          uu____15896 FStar_Pervasives_Native.None FStar_Range.dummyRange  in
        FStar_All.pipe_left ret uu____15895
    | FStar_Reflection_Data.Tv_Uvar (_u,ctx_u_s) ->
        let uu____15909 =
          FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_uvar ctx_u_s)
            FStar_Pervasives_Native.None FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____15909
    | FStar_Reflection_Data.Tv_Let (false ,attrs,bv,t1,t2) ->
        let lb =
          FStar_Syntax_Util.mk_letbinding (FStar_Util.Inl bv) []
            bv.FStar_Syntax_Syntax.sort FStar_Parser_Const.effect_Tot_lid t1
            attrs FStar_Range.dummyRange
           in
        let uu____15923 =
          let uu____15924 =
            let uu____15931 =
              let uu____15932 =
                let uu____15946 =
                  let uu____15949 =
                    let uu____15950 = FStar_Syntax_Syntax.mk_binder bv  in
                    [uu____15950]  in
                  FStar_Syntax_Subst.close uu____15949 t2  in
                ((false, [lb]), uu____15946)  in
              FStar_Syntax_Syntax.Tm_let uu____15932  in
            FStar_Syntax_Syntax.mk uu____15931  in
          uu____15924 FStar_Pervasives_Native.None FStar_Range.dummyRange  in
        FStar_All.pipe_left ret uu____15923
    | FStar_Reflection_Data.Tv_Let (true ,attrs,bv,t1,t2) ->
        let lb =
          FStar_Syntax_Util.mk_letbinding (FStar_Util.Inl bv) []
            bv.FStar_Syntax_Syntax.sort FStar_Parser_Const.effect_Tot_lid t1
            attrs FStar_Range.dummyRange
           in
        let uu____15995 = FStar_Syntax_Subst.close_let_rec [lb] t2  in
        (match uu____15995 with
         | (lbs,body) ->
             let uu____16010 =
               FStar_Syntax_Syntax.mk
                 (FStar_Syntax_Syntax.Tm_let ((true, lbs), body))
                 FStar_Pervasives_Native.None FStar_Range.dummyRange
                in
             FStar_All.pipe_left ret uu____16010)
    | FStar_Reflection_Data.Tv_Match (t,brs) ->
        let wrap v1 =
          {
            FStar_Syntax_Syntax.v = v1;
            FStar_Syntax_Syntax.p = FStar_Range.dummyRange
          }  in
        let rec pack_pat p =
          match p with
          | FStar_Reflection_Data.Pat_Constant c ->
              let uu____16047 =
                let uu____16048 = FStar_Reflection_Basic.pack_const c  in
                FStar_Syntax_Syntax.Pat_constant uu____16048  in
              FStar_All.pipe_left wrap uu____16047
          | FStar_Reflection_Data.Pat_Cons (fv,ps) ->
              let uu____16065 =
                let uu____16066 =
                  let uu____16080 =
                    FStar_List.map
                      (fun uu____16104  ->
                         match uu____16104 with
                         | (p1,b) ->
                             let uu____16119 = pack_pat p1  in
                             (uu____16119, b)) ps
                     in
                  (fv, uu____16080)  in
                FStar_Syntax_Syntax.Pat_cons uu____16066  in
              FStar_All.pipe_left wrap uu____16065
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
            (fun uu___9_16167  ->
               match uu___9_16167 with
               | (pat,t1) ->
                   let uu____16184 = pack_pat pat  in
                   (uu____16184, FStar_Pervasives_Native.None, t1)) brs
           in
        let brs2 = FStar_List.map FStar_Syntax_Subst.close_branch brs1  in
        let uu____16232 =
          FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_match (t, brs2))
            FStar_Pervasives_Native.None FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____16232
    | FStar_Reflection_Data.Tv_AscribedT (e,t,tacopt) ->
        let uu____16260 =
          FStar_Syntax_Syntax.mk
            (FStar_Syntax_Syntax.Tm_ascribed
               (e, ((FStar_Util.Inl t), tacopt),
                 FStar_Pervasives_Native.None)) FStar_Pervasives_Native.None
            FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____16260
    | FStar_Reflection_Data.Tv_AscribedC (e,c,tacopt) ->
        let uu____16306 =
          FStar_Syntax_Syntax.mk
            (FStar_Syntax_Syntax.Tm_ascribed
               (e, ((FStar_Util.Inr c), tacopt),
                 FStar_Pervasives_Native.None)) FStar_Pervasives_Native.None
            FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____16306
    | FStar_Reflection_Data.Tv_Unknown  ->
        let uu____16345 =
          FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown
            FStar_Pervasives_Native.None FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____16345
  
let (lget :
  FStar_Reflection_Data.typ -> Prims.string -> FStar_Syntax_Syntax.term tac)
  =
  fun ty  ->
    fun k  ->
      let uu____16365 =
        bind get
          (fun ps  ->
             let uu____16371 =
               FStar_Util.psmap_try_find ps.FStar_Tactics_Types.local_state k
                in
             match uu____16371 with
             | FStar_Pervasives_Native.None  -> fail "not found"
             | FStar_Pervasives_Native.Some t -> unquote ty t)
         in
      FStar_All.pipe_left (wrap_err "lget") uu____16365
  
let (lset :
  FStar_Reflection_Data.typ ->
    Prims.string -> FStar_Syntax_Syntax.term -> unit tac)
  =
  fun _ty  ->
    fun k  ->
      fun t  ->
        let uu____16405 =
          bind get
            (fun ps  ->
               let ps1 =
                 let uu___2252_16412 = ps  in
                 let uu____16413 =
                   FStar_Util.psmap_add ps.FStar_Tactics_Types.local_state k
                     t
                    in
                 {
                   FStar_Tactics_Types.main_context =
                     (uu___2252_16412.FStar_Tactics_Types.main_context);
                   FStar_Tactics_Types.all_implicits =
                     (uu___2252_16412.FStar_Tactics_Types.all_implicits);
                   FStar_Tactics_Types.goals =
                     (uu___2252_16412.FStar_Tactics_Types.goals);
                   FStar_Tactics_Types.smt_goals =
                     (uu___2252_16412.FStar_Tactics_Types.smt_goals);
                   FStar_Tactics_Types.depth =
                     (uu___2252_16412.FStar_Tactics_Types.depth);
                   FStar_Tactics_Types.__dump =
                     (uu___2252_16412.FStar_Tactics_Types.__dump);
                   FStar_Tactics_Types.psc =
                     (uu___2252_16412.FStar_Tactics_Types.psc);
                   FStar_Tactics_Types.entry_range =
                     (uu___2252_16412.FStar_Tactics_Types.entry_range);
                   FStar_Tactics_Types.guard_policy =
                     (uu___2252_16412.FStar_Tactics_Types.guard_policy);
                   FStar_Tactics_Types.freshness =
                     (uu___2252_16412.FStar_Tactics_Types.freshness);
                   FStar_Tactics_Types.tac_verb_dbg =
                     (uu___2252_16412.FStar_Tactics_Types.tac_verb_dbg);
                   FStar_Tactics_Types.local_state = uu____16413
                 }  in
               set ps1)
           in
        FStar_All.pipe_left (wrap_err "lset") uu____16405
  
let (goal_of_goal_ty :
  env ->
    FStar_Reflection_Data.typ ->
      (FStar_Tactics_Types.goal * FStar_TypeChecker_Common.guard_t))
  =
  fun env  ->
    fun typ  ->
      let uu____16440 =
        FStar_TypeChecker_Util.new_implicit_var "proofstate_of_goal_ty"
          typ.FStar_Syntax_Syntax.pos env typ
         in
      match uu____16440 with
      | (u,ctx_uvars,g_u) ->
          let uu____16473 = FStar_List.hd ctx_uvars  in
          (match uu____16473 with
           | (ctx_uvar,uu____16487) ->
               let g =
                 let uu____16489 = FStar_Options.peek ()  in
                 FStar_Tactics_Types.mk_goal env ctx_uvar uu____16489 false
                   ""
                  in
               (g, g_u))
  
let (tac_env : FStar_TypeChecker_Env.env -> FStar_TypeChecker_Env.env) =
  fun env  ->
    let uu____16498 = FStar_TypeChecker_Env.clear_expected_typ env  in
    match uu____16498 with
    | (env1,uu____16506) ->
        let env2 =
          let uu___2269_16512 = env1  in
          {
            FStar_TypeChecker_Env.solver =
              (uu___2269_16512.FStar_TypeChecker_Env.solver);
            FStar_TypeChecker_Env.range =
              (uu___2269_16512.FStar_TypeChecker_Env.range);
            FStar_TypeChecker_Env.curmodule =
              (uu___2269_16512.FStar_TypeChecker_Env.curmodule);
            FStar_TypeChecker_Env.gamma =
              (uu___2269_16512.FStar_TypeChecker_Env.gamma);
            FStar_TypeChecker_Env.gamma_sig =
              (uu___2269_16512.FStar_TypeChecker_Env.gamma_sig);
            FStar_TypeChecker_Env.gamma_cache =
              (uu___2269_16512.FStar_TypeChecker_Env.gamma_cache);
            FStar_TypeChecker_Env.modules =
              (uu___2269_16512.FStar_TypeChecker_Env.modules);
            FStar_TypeChecker_Env.expected_typ =
              (uu___2269_16512.FStar_TypeChecker_Env.expected_typ);
            FStar_TypeChecker_Env.sigtab =
              (uu___2269_16512.FStar_TypeChecker_Env.sigtab);
            FStar_TypeChecker_Env.attrtab =
              (uu___2269_16512.FStar_TypeChecker_Env.attrtab);
            FStar_TypeChecker_Env.instantiate_imp = false;
            FStar_TypeChecker_Env.effects =
              (uu___2269_16512.FStar_TypeChecker_Env.effects);
            FStar_TypeChecker_Env.generalize =
              (uu___2269_16512.FStar_TypeChecker_Env.generalize);
            FStar_TypeChecker_Env.letrecs =
              (uu___2269_16512.FStar_TypeChecker_Env.letrecs);
            FStar_TypeChecker_Env.top_level =
              (uu___2269_16512.FStar_TypeChecker_Env.top_level);
            FStar_TypeChecker_Env.check_uvars =
              (uu___2269_16512.FStar_TypeChecker_Env.check_uvars);
            FStar_TypeChecker_Env.use_eq =
              (uu___2269_16512.FStar_TypeChecker_Env.use_eq);
            FStar_TypeChecker_Env.use_eq_strict =
              (uu___2269_16512.FStar_TypeChecker_Env.use_eq_strict);
            FStar_TypeChecker_Env.is_iface =
              (uu___2269_16512.FStar_TypeChecker_Env.is_iface);
            FStar_TypeChecker_Env.admit =
              (uu___2269_16512.FStar_TypeChecker_Env.admit);
            FStar_TypeChecker_Env.lax =
              (uu___2269_16512.FStar_TypeChecker_Env.lax);
            FStar_TypeChecker_Env.lax_universes =
              (uu___2269_16512.FStar_TypeChecker_Env.lax_universes);
            FStar_TypeChecker_Env.phase1 =
              (uu___2269_16512.FStar_TypeChecker_Env.phase1);
            FStar_TypeChecker_Env.failhard =
              (uu___2269_16512.FStar_TypeChecker_Env.failhard);
            FStar_TypeChecker_Env.nosynth =
              (uu___2269_16512.FStar_TypeChecker_Env.nosynth);
            FStar_TypeChecker_Env.uvar_subtyping =
              (uu___2269_16512.FStar_TypeChecker_Env.uvar_subtyping);
            FStar_TypeChecker_Env.tc_term =
              (uu___2269_16512.FStar_TypeChecker_Env.tc_term);
            FStar_TypeChecker_Env.type_of =
              (uu___2269_16512.FStar_TypeChecker_Env.type_of);
            FStar_TypeChecker_Env.universe_of =
              (uu___2269_16512.FStar_TypeChecker_Env.universe_of);
            FStar_TypeChecker_Env.check_type_of =
              (uu___2269_16512.FStar_TypeChecker_Env.check_type_of);
            FStar_TypeChecker_Env.use_bv_sorts =
              (uu___2269_16512.FStar_TypeChecker_Env.use_bv_sorts);
            FStar_TypeChecker_Env.qtbl_name_and_index =
              (uu___2269_16512.FStar_TypeChecker_Env.qtbl_name_and_index);
            FStar_TypeChecker_Env.normalized_eff_names =
              (uu___2269_16512.FStar_TypeChecker_Env.normalized_eff_names);
            FStar_TypeChecker_Env.fv_delta_depths =
              (uu___2269_16512.FStar_TypeChecker_Env.fv_delta_depths);
            FStar_TypeChecker_Env.proof_ns =
              (uu___2269_16512.FStar_TypeChecker_Env.proof_ns);
            FStar_TypeChecker_Env.synth_hook =
              (uu___2269_16512.FStar_TypeChecker_Env.synth_hook);
            FStar_TypeChecker_Env.try_solve_implicits_hook =
              (uu___2269_16512.FStar_TypeChecker_Env.try_solve_implicits_hook);
            FStar_TypeChecker_Env.splice =
              (uu___2269_16512.FStar_TypeChecker_Env.splice);
            FStar_TypeChecker_Env.mpreprocess =
              (uu___2269_16512.FStar_TypeChecker_Env.mpreprocess);
            FStar_TypeChecker_Env.postprocess =
              (uu___2269_16512.FStar_TypeChecker_Env.postprocess);
            FStar_TypeChecker_Env.is_native_tactic =
              (uu___2269_16512.FStar_TypeChecker_Env.is_native_tactic);
            FStar_TypeChecker_Env.identifier_info =
              (uu___2269_16512.FStar_TypeChecker_Env.identifier_info);
            FStar_TypeChecker_Env.tc_hooks =
              (uu___2269_16512.FStar_TypeChecker_Env.tc_hooks);
            FStar_TypeChecker_Env.dsenv =
              (uu___2269_16512.FStar_TypeChecker_Env.dsenv);
            FStar_TypeChecker_Env.nbe =
              (uu___2269_16512.FStar_TypeChecker_Env.nbe);
            FStar_TypeChecker_Env.strict_args_tab =
              (uu___2269_16512.FStar_TypeChecker_Env.strict_args_tab);
            FStar_TypeChecker_Env.erasable_types_tab =
              (uu___2269_16512.FStar_TypeChecker_Env.erasable_types_tab)
          }  in
        let env3 =
          let uu___2272_16515 = env2  in
          {
            FStar_TypeChecker_Env.solver =
              (uu___2272_16515.FStar_TypeChecker_Env.solver);
            FStar_TypeChecker_Env.range =
              (uu___2272_16515.FStar_TypeChecker_Env.range);
            FStar_TypeChecker_Env.curmodule =
              (uu___2272_16515.FStar_TypeChecker_Env.curmodule);
            FStar_TypeChecker_Env.gamma =
              (uu___2272_16515.FStar_TypeChecker_Env.gamma);
            FStar_TypeChecker_Env.gamma_sig =
              (uu___2272_16515.FStar_TypeChecker_Env.gamma_sig);
            FStar_TypeChecker_Env.gamma_cache =
              (uu___2272_16515.FStar_TypeChecker_Env.gamma_cache);
            FStar_TypeChecker_Env.modules =
              (uu___2272_16515.FStar_TypeChecker_Env.modules);
            FStar_TypeChecker_Env.expected_typ =
              (uu___2272_16515.FStar_TypeChecker_Env.expected_typ);
            FStar_TypeChecker_Env.sigtab =
              (uu___2272_16515.FStar_TypeChecker_Env.sigtab);
            FStar_TypeChecker_Env.attrtab =
              (uu___2272_16515.FStar_TypeChecker_Env.attrtab);
            FStar_TypeChecker_Env.instantiate_imp =
              (uu___2272_16515.FStar_TypeChecker_Env.instantiate_imp);
            FStar_TypeChecker_Env.effects =
              (uu___2272_16515.FStar_TypeChecker_Env.effects);
            FStar_TypeChecker_Env.generalize =
              (uu___2272_16515.FStar_TypeChecker_Env.generalize);
            FStar_TypeChecker_Env.letrecs =
              (uu___2272_16515.FStar_TypeChecker_Env.letrecs);
            FStar_TypeChecker_Env.top_level =
              (uu___2272_16515.FStar_TypeChecker_Env.top_level);
            FStar_TypeChecker_Env.check_uvars =
              (uu___2272_16515.FStar_TypeChecker_Env.check_uvars);
            FStar_TypeChecker_Env.use_eq =
              (uu___2272_16515.FStar_TypeChecker_Env.use_eq);
            FStar_TypeChecker_Env.use_eq_strict =
              (uu___2272_16515.FStar_TypeChecker_Env.use_eq_strict);
            FStar_TypeChecker_Env.is_iface =
              (uu___2272_16515.FStar_TypeChecker_Env.is_iface);
            FStar_TypeChecker_Env.admit =
              (uu___2272_16515.FStar_TypeChecker_Env.admit);
            FStar_TypeChecker_Env.lax =
              (uu___2272_16515.FStar_TypeChecker_Env.lax);
            FStar_TypeChecker_Env.lax_universes =
              (uu___2272_16515.FStar_TypeChecker_Env.lax_universes);
            FStar_TypeChecker_Env.phase1 =
              (uu___2272_16515.FStar_TypeChecker_Env.phase1);
            FStar_TypeChecker_Env.failhard = true;
            FStar_TypeChecker_Env.nosynth =
              (uu___2272_16515.FStar_TypeChecker_Env.nosynth);
            FStar_TypeChecker_Env.uvar_subtyping =
              (uu___2272_16515.FStar_TypeChecker_Env.uvar_subtyping);
            FStar_TypeChecker_Env.tc_term =
              (uu___2272_16515.FStar_TypeChecker_Env.tc_term);
            FStar_TypeChecker_Env.type_of =
              (uu___2272_16515.FStar_TypeChecker_Env.type_of);
            FStar_TypeChecker_Env.universe_of =
              (uu___2272_16515.FStar_TypeChecker_Env.universe_of);
            FStar_TypeChecker_Env.check_type_of =
              (uu___2272_16515.FStar_TypeChecker_Env.check_type_of);
            FStar_TypeChecker_Env.use_bv_sorts =
              (uu___2272_16515.FStar_TypeChecker_Env.use_bv_sorts);
            FStar_TypeChecker_Env.qtbl_name_and_index =
              (uu___2272_16515.FStar_TypeChecker_Env.qtbl_name_and_index);
            FStar_TypeChecker_Env.normalized_eff_names =
              (uu___2272_16515.FStar_TypeChecker_Env.normalized_eff_names);
            FStar_TypeChecker_Env.fv_delta_depths =
              (uu___2272_16515.FStar_TypeChecker_Env.fv_delta_depths);
            FStar_TypeChecker_Env.proof_ns =
              (uu___2272_16515.FStar_TypeChecker_Env.proof_ns);
            FStar_TypeChecker_Env.synth_hook =
              (uu___2272_16515.FStar_TypeChecker_Env.synth_hook);
            FStar_TypeChecker_Env.try_solve_implicits_hook =
              (uu___2272_16515.FStar_TypeChecker_Env.try_solve_implicits_hook);
            FStar_TypeChecker_Env.splice =
              (uu___2272_16515.FStar_TypeChecker_Env.splice);
            FStar_TypeChecker_Env.mpreprocess =
              (uu___2272_16515.FStar_TypeChecker_Env.mpreprocess);
            FStar_TypeChecker_Env.postprocess =
              (uu___2272_16515.FStar_TypeChecker_Env.postprocess);
            FStar_TypeChecker_Env.is_native_tactic =
              (uu___2272_16515.FStar_TypeChecker_Env.is_native_tactic);
            FStar_TypeChecker_Env.identifier_info =
              (uu___2272_16515.FStar_TypeChecker_Env.identifier_info);
            FStar_TypeChecker_Env.tc_hooks =
              (uu___2272_16515.FStar_TypeChecker_Env.tc_hooks);
            FStar_TypeChecker_Env.dsenv =
              (uu___2272_16515.FStar_TypeChecker_Env.dsenv);
            FStar_TypeChecker_Env.nbe =
              (uu___2272_16515.FStar_TypeChecker_Env.nbe);
            FStar_TypeChecker_Env.strict_args_tab =
              (uu___2272_16515.FStar_TypeChecker_Env.strict_args_tab);
            FStar_TypeChecker_Env.erasable_types_tab =
              (uu___2272_16515.FStar_TypeChecker_Env.erasable_types_tab)
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
            let uu____16548 =
              FStar_TypeChecker_Env.debug env1
                (FStar_Options.Other "TacVerbose")
               in
            let uu____16551 = FStar_Util.psmap_empty ()  in
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
              FStar_Tactics_Types.tac_verb_dbg = uu____16548;
              FStar_Tactics_Types.local_state = uu____16551
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
        let uu____16577 = goal_of_goal_ty env1 typ  in
        match uu____16577 with
        | (g,g_u) ->
            let ps =
              proofstate_of_goals rng env1 [g]
                g_u.FStar_TypeChecker_Common.implicits
               in
            let uu____16589 = FStar_Tactics_Types.goal_witness g  in
            (ps, uu____16589)
  
let (goal_of_implicit :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Env.implicit -> FStar_Tactics_Types.goal)
  =
  fun env  ->
    fun i  ->
      let uu____16601 = FStar_Options.peek ()  in
      FStar_Tactics_Types.mk_goal env i.FStar_TypeChecker_Common.imp_uvar
        uu____16601 false ""
  
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
          let uu____16628 = FStar_List.hd goals  in
          FStar_Tactics_Types.goal_witness uu____16628  in
        let ps =
          let uu____16630 =
            FStar_TypeChecker_Env.debug env
              (FStar_Options.Other "TacVerbose")
             in
          let uu____16633 = FStar_Util.psmap_empty ()  in
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
            FStar_Tactics_Types.tac_verb_dbg = uu____16630;
            FStar_Tactics_Types.local_state = uu____16633
          }  in
        (ps, w)
  