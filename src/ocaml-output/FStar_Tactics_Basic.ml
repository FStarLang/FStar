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
                      (uu___488_3070.FStar_TypeChecker_Env.erasable_types_tab)
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
                      (uu___509_3206.FStar_TypeChecker_Env.erasable_types_tab)
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
                      (uu___534_3357.FStar_TypeChecker_Env.erasable_types_tab)
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
                      (uu___537_3360.FStar_TypeChecker_Env.erasable_types_tab)
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
                             (fun uu____5509  ->
                                match uu____5509 with
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
        let uu____5615 =
          mlog
            (fun uu____5620  ->
               let uu____5621 = FStar_Syntax_Print.term_to_string tm  in
               FStar_Util.print1 "t_apply: tm = %s\n" uu____5621)
            (fun uu____5626  ->
               let uu____5627 = cur_goal ()  in
               bind uu____5627
                 (fun goal  ->
                    let e = FStar_Tactics_Types.goal_env goal  in
                    let uu____5635 = __tc e tm  in
                    bind uu____5635
                      (fun uu____5656  ->
                         match uu____5656 with
                         | (tm1,typ,guard) ->
                             let typ1 = bnorm e typ  in
                             let uu____5669 =
                               let uu____5680 =
                                 FStar_Tactics_Types.goal_type goal  in
                               try_unify_by_application only_match e typ1
                                 uu____5680
                                in
                             bind uu____5669
                               (fun uvs  ->
                                  mlog
                                    (fun uu____5701  ->
                                       let uu____5702 =
                                         FStar_Common.string_of_list
                                           (fun uu____5714  ->
                                              match uu____5714 with
                                              | (t,uu____5723,uu____5724) ->
                                                  FStar_Syntax_Print.term_to_string
                                                    t) uvs
                                          in
                                       FStar_Util.print1
                                         "t_apply: found args = %s\n"
                                         uu____5702)
                                    (fun uu____5732  ->
                                       let fix_qual q =
                                         match q with
                                         | FStar_Pervasives_Native.Some
                                             (FStar_Syntax_Syntax.Meta
                                             uu____5747) ->
                                             FStar_Pervasives_Native.Some
                                               (FStar_Syntax_Syntax.Implicit
                                                  false)
                                         | uu____5749 -> q  in
                                       let w =
                                         FStar_List.fold_right
                                           (fun uu____5772  ->
                                              fun w  ->
                                                match uu____5772 with
                                                | (uvt,q,uu____5790) ->
                                                    FStar_Syntax_Util.mk_app
                                                      w [(uvt, (fix_qual q))])
                                           uvs tm1
                                          in
                                       let uvset =
                                         let uu____5822 =
                                           FStar_Syntax_Free.new_uv_set ()
                                            in
                                         FStar_List.fold_right
                                           (fun uu____5839  ->
                                              fun s  ->
                                                match uu____5839 with
                                                | (uu____5851,uu____5852,uv)
                                                    ->
                                                    let uu____5854 =
                                                      FStar_Syntax_Free.uvars
                                                        uv.FStar_Syntax_Syntax.ctx_uvar_typ
                                                       in
                                                    FStar_Util.set_union s
                                                      uu____5854) uvs
                                           uu____5822
                                          in
                                       let free_in_some_goal uv =
                                         FStar_Util.set_mem uv uvset  in
                                       let uu____5864 = solve' goal w  in
                                       bind uu____5864
                                         (fun uu____5869  ->
                                            let uu____5870 =
                                              mapM
                                                (fun uu____5887  ->
                                                   match uu____5887 with
                                                   | (uvt,q,uv) ->
                                                       let uu____5899 =
                                                         FStar_Syntax_Unionfind.find
                                                           uv.FStar_Syntax_Syntax.ctx_uvar_head
                                                          in
                                                       (match uu____5899 with
                                                        | FStar_Pervasives_Native.Some
                                                            uu____5904 ->
                                                            ret ()
                                                        | FStar_Pervasives_Native.None
                                                             ->
                                                            let uu____5905 =
                                                              uopt &&
                                                                (free_in_some_goal
                                                                   uv)
                                                               in
                                                            if uu____5905
                                                            then ret ()
                                                            else
                                                              (let uu____5912
                                                                 =
                                                                 let uu____5915
                                                                   =
                                                                   bnorm_goal
                                                                    (let uu___899_5918
                                                                    = goal
                                                                     in
                                                                    {
                                                                    FStar_Tactics_Types.goal_main_env
                                                                    =
                                                                    (uu___899_5918.FStar_Tactics_Types.goal_main_env);
                                                                    FStar_Tactics_Types.goal_ctx_uvar
                                                                    = uv;
                                                                    FStar_Tactics_Types.opts
                                                                    =
                                                                    (uu___899_5918.FStar_Tactics_Types.opts);
                                                                    FStar_Tactics_Types.is_guard
                                                                    = false;
                                                                    FStar_Tactics_Types.label
                                                                    =
                                                                    (uu___899_5918.FStar_Tactics_Types.label)
                                                                    })
                                                                    in
                                                                 [uu____5915]
                                                                  in
                                                               add_goals
                                                                 uu____5912)))
                                                uvs
                                               in
                                            bind uu____5870
                                              (fun uu____5923  ->
                                                 proc_guard "apply guard" e
                                                   guard)))))))
           in
        FStar_All.pipe_left (wrap_err "apply") uu____5615
  
let (lemma_or_sq :
  FStar_Syntax_Syntax.comp ->
    (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.option)
  =
  fun c  ->
    let ct = FStar_Syntax_Util.comp_to_comp_typ_nouniv c  in
    let uu____5951 =
      FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
        FStar_Parser_Const.effect_Lemma_lid
       in
    if uu____5951
    then
      let uu____5960 =
        match ct.FStar_Syntax_Syntax.effect_args with
        | pre::post::uu____5975 ->
            ((FStar_Pervasives_Native.fst pre),
              (FStar_Pervasives_Native.fst post))
        | uu____6028 -> failwith "apply_lemma: impossible: not a lemma"  in
      match uu____5960 with
      | (pre,post) ->
          let post1 =
            let uu____6061 =
              let uu____6072 =
                FStar_Syntax_Syntax.as_arg FStar_Syntax_Util.exp_unit  in
              [uu____6072]  in
            FStar_Syntax_Util.mk_app post uu____6061  in
          FStar_Pervasives_Native.Some (pre, post1)
    else
      (let uu____6103 =
         FStar_Syntax_Util.is_pure_effect ct.FStar_Syntax_Syntax.effect_name
          in
       if uu____6103
       then
         let uu____6112 =
           FStar_Syntax_Util.un_squash ct.FStar_Syntax_Syntax.result_typ  in
         FStar_Util.map_opt uu____6112
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
            let uu____6191 = f x e  in
            bind uu____6191 (fun e'  -> fold_left f e' xs1)
  
let (apply_lemma : FStar_Syntax_Syntax.term -> unit tac) =
  fun tm  ->
    let uu____6206 =
      let uu____6209 =
        bind get
          (fun ps  ->
             mlog
               (fun uu____6216  ->
                  let uu____6217 = FStar_Syntax_Print.term_to_string tm  in
                  FStar_Util.print1 "apply_lemma: tm = %s\n" uu____6217)
               (fun uu____6223  ->
                  let is_unit_t t =
                    let uu____6231 =
                      let uu____6232 = FStar_Syntax_Subst.compress t  in
                      uu____6232.FStar_Syntax_Syntax.n  in
                    match uu____6231 with
                    | FStar_Syntax_Syntax.Tm_fvar fv when
                        FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.unit_lid
                        -> true
                    | uu____6238 -> false  in
                  let uu____6240 = cur_goal ()  in
                  bind uu____6240
                    (fun goal  ->
                       let uu____6246 =
                         let uu____6255 = FStar_Tactics_Types.goal_env goal
                            in
                         __tc uu____6255 tm  in
                       bind uu____6246
                         (fun uu____6270  ->
                            match uu____6270 with
                            | (tm1,t,guard) ->
                                let uu____6282 =
                                  FStar_Syntax_Util.arrow_formals_comp t  in
                                (match uu____6282 with
                                 | (bs,comp) ->
                                     let uu____6291 = lemma_or_sq comp  in
                                     (match uu____6291 with
                                      | FStar_Pervasives_Native.None  ->
                                          fail
                                            "not a lemma or squashed function"
                                      | FStar_Pervasives_Native.Some
                                          (pre,post) ->
                                          let uu____6311 =
                                            fold_left
                                              (fun uu____6373  ->
                                                 fun uu____6374  ->
                                                   match (uu____6373,
                                                           uu____6374)
                                                   with
                                                   | ((b,aq),(uvs,imps,subst1))
                                                       ->
                                                       let b_t =
                                                         FStar_Syntax_Subst.subst
                                                           subst1
                                                           b.FStar_Syntax_Syntax.sort
                                                          in
                                                       let uu____6525 =
                                                         is_unit_t b_t  in
                                                       if uu____6525
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
                                                         (let uu____6648 =
                                                            let uu____6655 =
                                                              FStar_Tactics_Types.goal_env
                                                                goal
                                                               in
                                                            new_uvar
                                                              "apply_lemma"
                                                              uu____6655 b_t
                                                             in
                                                          bind uu____6648
                                                            (fun uu____6686 
                                                               ->
                                                               match uu____6686
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
                                          bind uu____6311
                                            (fun uu____6872  ->
                                               match uu____6872 with
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
                                                   let uu____6960 =
                                                     let uu____6964 =
                                                       FStar_Tactics_Types.goal_env
                                                         goal
                                                        in
                                                     let uu____6965 =
                                                       FStar_Syntax_Util.mk_squash
                                                         FStar_Syntax_Syntax.U_zero
                                                         post1
                                                        in
                                                     let uu____6966 =
                                                       FStar_Tactics_Types.goal_type
                                                         goal
                                                        in
                                                     do_unify uu____6964
                                                       uu____6965 uu____6966
                                                      in
                                                   bind uu____6960
                                                     (fun b  ->
                                                        if
                                                          Prims.op_Negation b
                                                        then
                                                          let uu____6978 =
                                                            let uu____6985 =
                                                              let uu____6991
                                                                =
                                                                FStar_Tactics_Types.goal_env
                                                                  goal
                                                                 in
                                                              tts uu____6991
                                                               in
                                                            let uu____6992 =
                                                              FStar_Syntax_Util.mk_squash
                                                                FStar_Syntax_Syntax.U_zero
                                                                post1
                                                               in
                                                            let uu____6993 =
                                                              FStar_Tactics_Types.goal_type
                                                                goal
                                                               in
                                                            FStar_TypeChecker_Err.print_discrepancy
                                                              uu____6985
                                                              uu____6992
                                                              uu____6993
                                                             in
                                                          match uu____6978
                                                          with
                                                          | (post2,goalt) ->
                                                              let uu____7002
                                                                =
                                                                let uu____7004
                                                                  =
                                                                  FStar_Tactics_Types.goal_env
                                                                    goal
                                                                   in
                                                                tts
                                                                  uu____7004
                                                                  tm1
                                                                 in
                                                              fail3
                                                                "Cannot instantiate lemma %s (with postcondition: %s) to match goal (%s)"
                                                                uu____7002
                                                                post2 goalt
                                                        else
                                                          (let uu____7008 =
                                                             solve' goal
                                                               FStar_Syntax_Util.exp_unit
                                                              in
                                                           bind uu____7008
                                                             (fun uu____7016 
                                                                ->
                                                                let is_free_uvar
                                                                  uv t1 =
                                                                  let free_uvars
                                                                    =
                                                                    let uu____7042
                                                                    =
                                                                    let uu____7045
                                                                    =
                                                                    FStar_Syntax_Free.uvars
                                                                    t1  in
                                                                    FStar_Util.set_elements
                                                                    uu____7045
                                                                     in
                                                                    FStar_List.map
                                                                    (fun x 
                                                                    ->
                                                                    x.FStar_Syntax_Syntax.ctx_uvar_head)
                                                                    uu____7042
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
                                                                    let uu____7081
                                                                    =
                                                                    FStar_Tactics_Types.goal_type
                                                                    g'  in
                                                                    is_free_uvar
                                                                    uv
                                                                    uu____7081)
                                                                    goals
                                                                   in
                                                                let checkone
                                                                  t1 goals =
                                                                  let uu____7098
                                                                    =
                                                                    FStar_Syntax_Util.head_and_args
                                                                    t1  in
                                                                  match uu____7098
                                                                  with
                                                                  | (hd1,uu____7117)
                                                                    ->
                                                                    (match 
                                                                    hd1.FStar_Syntax_Syntax.n
                                                                    with
                                                                    | 
                                                                    FStar_Syntax_Syntax.Tm_uvar
                                                                    (uv,uu____7144)
                                                                    ->
                                                                    appears
                                                                    uv.FStar_Syntax_Syntax.ctx_uvar_head
                                                                    goals
                                                                    | 
                                                                    uu____7161
                                                                    -> false)
                                                                   in
                                                                let uu____7163
                                                                  =
                                                                  FStar_All.pipe_right
                                                                    implicits1
                                                                    (
                                                                    mapM
                                                                    (fun imp 
                                                                    ->
                                                                    let uu____7204
                                                                    = imp  in
                                                                    match uu____7204
                                                                    with
                                                                    | 
                                                                    (term,ctx_uvar)
                                                                    ->
                                                                    let uu____7215
                                                                    =
                                                                    FStar_Syntax_Util.head_and_args
                                                                    term  in
                                                                    (match uu____7215
                                                                    with
                                                                    | 
                                                                    (hd1,uu____7237)
                                                                    ->
                                                                    let uu____7262
                                                                    =
                                                                    let uu____7263
                                                                    =
                                                                    FStar_Syntax_Subst.compress
                                                                    hd1  in
                                                                    uu____7263.FStar_Syntax_Syntax.n
                                                                     in
                                                                    (match uu____7262
                                                                    with
                                                                    | 
                                                                    FStar_Syntax_Syntax.Tm_uvar
                                                                    (ctx_uvar1,uu____7271)
                                                                    ->
                                                                    let goal1
                                                                    =
                                                                    bnorm_goal
                                                                    (let uu___1016_7291
                                                                    = goal
                                                                     in
                                                                    {
                                                                    FStar_Tactics_Types.goal_main_env
                                                                    =
                                                                    (uu___1016_7291.FStar_Tactics_Types.goal_main_env);
                                                                    FStar_Tactics_Types.goal_ctx_uvar
                                                                    =
                                                                    ctx_uvar1;
                                                                    FStar_Tactics_Types.opts
                                                                    =
                                                                    (uu___1016_7291.FStar_Tactics_Types.opts);
                                                                    FStar_Tactics_Types.is_guard
                                                                    =
                                                                    (uu___1016_7291.FStar_Tactics_Types.is_guard);
                                                                    FStar_Tactics_Types.label
                                                                    =
                                                                    (uu___1016_7291.FStar_Tactics_Types.label)
                                                                    })  in
                                                                    ret
                                                                    [goal1]
                                                                    | 
                                                                    uu____7294
                                                                    ->
                                                                    mlog
                                                                    (fun
                                                                    uu____7300
                                                                     ->
                                                                    let uu____7301
                                                                    =
                                                                    FStar_Syntax_Print.uvar_to_string
                                                                    ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_head
                                                                     in
                                                                    let uu____7303
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    term  in
                                                                    FStar_Util.print2
                                                                    "apply_lemma: arg %s unified to (%s)\n"
                                                                    uu____7301
                                                                    uu____7303)
                                                                    (fun
                                                                    uu____7309
                                                                     ->
                                                                    let g_typ
                                                                    =
                                                                    let uu____7311
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    goal  in
                                                                    FStar_TypeChecker_TcTerm.check_type_of_well_typed_term'
                                                                    true
                                                                    uu____7311
                                                                    term
                                                                    ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_typ
                                                                     in
                                                                    let uu____7313
                                                                    =
                                                                    let uu____7316
                                                                    =
                                                                    if
                                                                    ps.FStar_Tactics_Types.tac_verb_dbg
                                                                    then
                                                                    let uu____7320
                                                                    =
                                                                    FStar_Syntax_Print.ctx_uvar_to_string
                                                                    ctx_uvar
                                                                     in
                                                                    let uu____7322
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    term  in
                                                                    FStar_Util.format2
                                                                    "apply_lemma solved arg %s to %s\n"
                                                                    uu____7320
                                                                    uu____7322
                                                                    else
                                                                    "apply_lemma solved arg"
                                                                     in
                                                                    let uu____7328
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    goal  in
                                                                    proc_guard
                                                                    uu____7316
                                                                    uu____7328
                                                                    g_typ  in
                                                                    bind
                                                                    uu____7313
                                                                    (fun
                                                                    uu____7332
                                                                     ->
                                                                    ret []))))))
                                                                   in
                                                                bind
                                                                  uu____7163
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
                                                                    let uu____7396
                                                                    = f x xs1
                                                                     in
                                                                    if
                                                                    uu____7396
                                                                    then
                                                                    let uu____7401
                                                                    =
                                                                    filter' f
                                                                    xs1  in x
                                                                    ::
                                                                    uu____7401
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
                                                                    let uu____7416
                                                                    =
                                                                    let uu____7418
                                                                    =
                                                                    FStar_Tactics_Types.goal_witness
                                                                    g  in
                                                                    checkone
                                                                    uu____7418
                                                                    goals  in
                                                                    Prims.op_Negation
                                                                    uu____7416)
                                                                    sub_goals1
                                                                     in
                                                                    let uu____7419
                                                                    =
                                                                    let uu____7422
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    goal  in
                                                                    proc_guard
                                                                    "apply_lemma guard"
                                                                    uu____7422
                                                                    guard  in
                                                                    bind
                                                                    uu____7419
                                                                    (fun
                                                                    uu____7426
                                                                     ->
                                                                    let uu____7427
                                                                    =
                                                                    let uu____7430
                                                                    =
                                                                    let uu____7432
                                                                    =
                                                                    let uu____7434
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    goal  in
                                                                    let uu____7435
                                                                    =
                                                                    FStar_Syntax_Util.mk_squash
                                                                    FStar_Syntax_Syntax.U_zero
                                                                    pre1  in
                                                                    istrivial
                                                                    uu____7434
                                                                    uu____7435
                                                                     in
                                                                    Prims.op_Negation
                                                                    uu____7432
                                                                     in
                                                                    if
                                                                    uu____7430
                                                                    then
                                                                    let uu____7439
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    goal  in
                                                                    add_irrelevant_goal
                                                                    "apply_lemma precondition"
                                                                    uu____7439
                                                                    pre1
                                                                    goal.FStar_Tactics_Types.opts
                                                                    goal.FStar_Tactics_Types.label
                                                                    else
                                                                    ret ()
                                                                     in
                                                                    bind
                                                                    uu____7427
                                                                    (fun
                                                                    uu____7444
                                                                     ->
                                                                    add_goals
                                                                    sub_goals2)))))))))))))
         in
      focus uu____6209  in
    FStar_All.pipe_left (wrap_err "apply_lemma") uu____6206
  
let (destruct_eq' :
  FStar_Reflection_Data.typ ->
    (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.option)
  =
  fun typ  ->
    let uu____7468 = FStar_Syntax_Util.destruct_typ_as_formula typ  in
    match uu____7468 with
    | FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn
        (l,uu____7478::(e1,FStar_Pervasives_Native.None )::(e2,FStar_Pervasives_Native.None
                                                            )::[]))
        when
        (FStar_Ident.lid_equals l FStar_Parser_Const.eq2_lid) ||
          (FStar_Ident.lid_equals l FStar_Parser_Const.c_eq2_lid)
        -> FStar_Pervasives_Native.Some (e1, e2)
    | FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn
        (l,uu____7538::uu____7539::(e1,uu____7541)::(e2,uu____7543)::[]))
        when FStar_Ident.lid_equals l FStar_Parser_Const.eq3_lid ->
        FStar_Pervasives_Native.Some (e1, e2)
    | uu____7620 ->
        let uu____7623 = FStar_Syntax_Util.unb2t typ  in
        (match uu____7623 with
         | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
         | FStar_Pervasives_Native.Some t ->
             let uu____7637 = FStar_Syntax_Util.head_and_args t  in
             (match uu____7637 with
              | (hd1,args) ->
                  let uu____7686 =
                    let uu____7701 =
                      let uu____7702 = FStar_Syntax_Subst.compress hd1  in
                      uu____7702.FStar_Syntax_Syntax.n  in
                    (uu____7701, args)  in
                  (match uu____7686 with
                   | (FStar_Syntax_Syntax.Tm_fvar
                      fv,(uu____7722,FStar_Pervasives_Native.Some
                          (FStar_Syntax_Syntax.Implicit uu____7723))::
                      (e1,FStar_Pervasives_Native.None )::(e2,FStar_Pervasives_Native.None
                                                           )::[])
                       when
                       FStar_Syntax_Syntax.fv_eq_lid fv
                         FStar_Parser_Const.op_Eq
                       -> FStar_Pervasives_Native.Some (e1, e2)
                   | uu____7791 -> FStar_Pervasives_Native.None)))
  
let (destruct_eq :
  FStar_Reflection_Data.typ ->
    (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.option)
  =
  fun typ  ->
    let uu____7828 = destruct_eq' typ  in
    match uu____7828 with
    | FStar_Pervasives_Native.Some t -> FStar_Pervasives_Native.Some t
    | FStar_Pervasives_Native.None  ->
        let uu____7858 = FStar_Syntax_Util.un_squash typ  in
        (match uu____7858 with
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
        let uu____7927 = FStar_TypeChecker_Env.pop_bv e1  in
        match uu____7927 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (bv',e') ->
            if FStar_Syntax_Syntax.bv_eq bvar bv'
            then FStar_Pervasives_Native.Some (e', bv', [])
            else
              (let uu____7985 = aux e'  in
               FStar_Util.map_opt uu____7985
                 (fun uu____8016  ->
                    match uu____8016 with
                    | (e'',bv,bvs) -> (e'', bv, (bv' :: bvs))))
         in
      let uu____8042 = aux e  in
      FStar_Util.map_opt uu____8042
        (fun uu____8073  ->
           match uu____8073 with
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
          let uu____8151 =
            let uu____8162 = FStar_Tactics_Types.goal_env g  in
            split_env b1 uu____8162  in
          match uu____8151 with
          | FStar_Pervasives_Native.Some (e0,b11,bvs) ->
              let s1 bv =
                let uu___1127_8188 = bv  in
                let uu____8189 =
                  FStar_Syntax_Subst.subst s bv.FStar_Syntax_Syntax.sort  in
                {
                  FStar_Syntax_Syntax.ppname =
                    (uu___1127_8188.FStar_Syntax_Syntax.ppname);
                  FStar_Syntax_Syntax.index =
                    (uu___1127_8188.FStar_Syntax_Syntax.index);
                  FStar_Syntax_Syntax.sort = uu____8189
                }  in
              let bvs' = FStar_List.map s1 bvs  in
              let new_env = push_bvs e0 (b2 :: bvs')  in
              let new_goal_ty =
                let uu____8197 = FStar_Tactics_Types.goal_type g  in
                FStar_Syntax_Subst.subst s uu____8197  in
              let uu____8198 = __tc_lax new_env new_goal_ty  in
              bind uu____8198
                (fun uu____8220  ->
                   match uu____8220 with
                   | (new_goal_ty1,uu____8232,uu____8233) ->
                       let uu____8234 =
                         new_uvar "subst_goal" new_env new_goal_ty1  in
                       bind uu____8234
                         (fun uu____8254  ->
                            match uu____8254 with
                            | (uvt,uv) ->
                                let goal' =
                                  FStar_Tactics_Types.mk_goal new_env uv
                                    g.FStar_Tactics_Types.opts
                                    g.FStar_Tactics_Types.is_guard
                                    g.FStar_Tactics_Types.label
                                   in
                                let sol =
                                  let uu____8269 =
                                    let uu____8272 =
                                      FStar_List.map
                                        FStar_Syntax_Syntax.mk_binder (b2 ::
                                        bvs')
                                       in
                                    FStar_Syntax_Util.abs uu____8272 uvt
                                      FStar_Pervasives_Native.None
                                     in
                                  let uu____8279 =
                                    FStar_List.map
                                      (fun bv  ->
                                         let uu____8293 =
                                           FStar_Syntax_Syntax.bv_to_name bv
                                            in
                                         FStar_Syntax_Syntax.as_arg
                                           uu____8293) (b11 :: bvs)
                                     in
                                  FStar_Syntax_Util.mk_app uu____8269
                                    uu____8279
                                   in
                                let uu____8294 =
                                  let uu____8303 =
                                    FStar_Tactics_Types.goal_env g  in
                                  __tc_lax uu____8303 sol  in
                                bind uu____8294
                                  (fun uu____8317  ->
                                     match uu____8317 with
                                     | (sol1,uu____8329,uu____8330) ->
                                         let uu____8331 = set_solution g sol1
                                            in
                                         bind uu____8331
                                           (fun uu____8337  ->
                                              ret
                                                (FStar_Pervasives_Native.Some
                                                   goal')))))
          | FStar_Pervasives_Native.None  -> ret FStar_Pervasives_Native.None
  
let (rewrite : FStar_Syntax_Syntax.binder -> unit tac) =
  fun h  ->
    let uu____8360 =
      let uu____8363 = cur_goal ()  in
      bind uu____8363
        (fun goal  ->
           let uu____8371 = h  in
           match uu____8371 with
           | (bv,uu____8375) ->
               mlog
                 (fun uu____8383  ->
                    let uu____8384 = FStar_Syntax_Print.bv_to_string bv  in
                    let uu____8386 =
                      FStar_Syntax_Print.term_to_string
                        bv.FStar_Syntax_Syntax.sort
                       in
                    FStar_Util.print2 "+++Rewrite %s : %s\n" uu____8384
                      uu____8386)
                 (fun uu____8391  ->
                    let uu____8392 =
                      let uu____8403 = FStar_Tactics_Types.goal_env goal  in
                      split_env bv uu____8403  in
                    match uu____8392 with
                    | FStar_Pervasives_Native.None  ->
                        fail "binder not found in environment"
                    | FStar_Pervasives_Native.Some (e0,bv1,bvs) ->
                        let uu____8430 =
                          destruct_eq bv1.FStar_Syntax_Syntax.sort  in
                        (match uu____8430 with
                         | FStar_Pervasives_Native.Some (x,e) ->
                             let uu____8445 =
                               let uu____8446 = FStar_Syntax_Subst.compress x
                                  in
                               uu____8446.FStar_Syntax_Syntax.n  in
                             (match uu____8445 with
                              | FStar_Syntax_Syntax.Tm_name x1 ->
                                  let s = [FStar_Syntax_Syntax.NT (x1, e)]
                                     in
                                  let s1 bv2 =
                                    let uu___1169_8463 = bv2  in
                                    let uu____8464 =
                                      FStar_Syntax_Subst.subst s
                                        bv2.FStar_Syntax_Syntax.sort
                                       in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___1169_8463.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___1169_8463.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = uu____8464
                                    }  in
                                  let bvs' = FStar_List.map s1 bvs  in
                                  let new_env = push_bvs e0 (bv1 :: bvs')  in
                                  let new_goal_ty =
                                    let uu____8472 =
                                      FStar_Tactics_Types.goal_type goal  in
                                    FStar_Syntax_Subst.subst s uu____8472  in
                                  let uu____8473 =
                                    __tc_lax new_env new_goal_ty  in
                                  bind uu____8473
                                    (fun uu____8493  ->
                                       match uu____8493 with
                                       | (new_goal_ty1,uu____8503,uu____8504)
                                           ->
                                           let uu____8505 =
                                             new_uvar "rewrite" new_env
                                               new_goal_ty1
                                              in
                                           bind uu____8505
                                             (fun uu____8523  ->
                                                match uu____8523 with
                                                | (uvt,uv) ->
                                                    let goal' =
                                                      FStar_Tactics_Types.mk_goal
                                                        new_env uv
                                                        goal.FStar_Tactics_Types.opts
                                                        goal.FStar_Tactics_Types.is_guard
                                                        goal.FStar_Tactics_Types.label
                                                       in
                                                    let sol =
                                                      let uu____8536 =
                                                        let uu____8539 =
                                                          FStar_List.map
                                                            FStar_Syntax_Syntax.mk_binder
                                                            bvs'
                                                           in
                                                        FStar_Syntax_Util.abs
                                                          uu____8539 uvt
                                                          FStar_Pervasives_Native.None
                                                         in
                                                      let uu____8546 =
                                                        FStar_List.map
                                                          (fun bv2  ->
                                                             let uu____8560 =
                                                               FStar_Syntax_Syntax.bv_to_name
                                                                 bv2
                                                                in
                                                             FStar_Syntax_Syntax.as_arg
                                                               uu____8560)
                                                          bvs
                                                         in
                                                      FStar_Syntax_Util.mk_app
                                                        uu____8536 uu____8546
                                                       in
                                                    let uu____8561 =
                                                      let uu____8570 =
                                                        FStar_Tactics_Types.goal_env
                                                          goal
                                                         in
                                                      __tc_lax uu____8570 sol
                                                       in
                                                    bind uu____8561
                                                      (fun uu____8582  ->
                                                         match uu____8582
                                                         with
                                                         | (sol1,uu____8592,uu____8593)
                                                             ->
                                                             let uu____8594 =
                                                               set_solution
                                                                 goal sol1
                                                                in
                                                             bind uu____8594
                                                               (fun
                                                                  uu____8598 
                                                                  ->
                                                                  replace_cur
                                                                    goal'))))
                              | uu____8599 ->
                                  fail
                                    "Not an equality hypothesis with a variable on the LHS")
                         | uu____8601 -> fail "Not an equality hypothesis")))
       in
    FStar_All.pipe_left (wrap_err "rewrite") uu____8360
  
let (rename_to :
  FStar_Syntax_Syntax.binder ->
    Prims.string -> FStar_Syntax_Syntax.binder tac)
  =
  fun b  ->
    fun s  ->
      let uu____8631 =
        let uu____8640 = cur_goal ()  in
        bind uu____8640
          (fun goal  ->
             let uu____8657 = b  in
             match uu____8657 with
             | (bv,q) ->
                 let bv' =
                   let uu____8673 =
                     let uu___1198_8674 = bv  in
                     let uu____8675 =
                       FStar_Ident.mk_ident
                         (s,
                           ((bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange))
                        in
                     {
                       FStar_Syntax_Syntax.ppname = uu____8675;
                       FStar_Syntax_Syntax.index =
                         (uu___1198_8674.FStar_Syntax_Syntax.index);
                       FStar_Syntax_Syntax.sort =
                         (uu___1198_8674.FStar_Syntax_Syntax.sort)
                     }  in
                   FStar_Syntax_Syntax.freshen_bv uu____8673  in
                 let s1 =
                   let uu____8680 =
                     let uu____8681 =
                       let uu____8688 = FStar_Syntax_Syntax.bv_to_name bv'
                          in
                       (bv, uu____8688)  in
                     FStar_Syntax_Syntax.NT uu____8681  in
                   [uu____8680]  in
                 let uu____8693 = subst_goal bv bv' s1 goal  in
                 bind uu____8693
                   (fun uu___4_8707  ->
                      match uu___4_8707 with
                      | FStar_Pervasives_Native.None  ->
                          fail "binder not found in environment"
                      | FStar_Pervasives_Native.Some goal1 ->
                          let uu____8726 = replace_cur goal1  in
                          bind uu____8726 (fun uu____8736  -> ret (bv', q))))
         in
      FStar_All.pipe_left (wrap_err "rename_to") uu____8631
  
let (binder_retype : FStar_Syntax_Syntax.binder -> unit tac) =
  fun b  ->
    let uu____8772 =
      let uu____8775 = cur_goal ()  in
      bind uu____8775
        (fun goal  ->
           let uu____8784 = b  in
           match uu____8784 with
           | (bv,uu____8788) ->
               let uu____8793 =
                 let uu____8804 = FStar_Tactics_Types.goal_env goal  in
                 split_env bv uu____8804  in
               (match uu____8793 with
                | FStar_Pervasives_Native.None  ->
                    fail "binder is not present in environment"
                | FStar_Pervasives_Native.Some (e0,bv1,bvs) ->
                    let uu____8831 = FStar_Syntax_Util.type_u ()  in
                    (match uu____8831 with
                     | (ty,u) ->
                         let uu____8840 = new_uvar "binder_retype" e0 ty  in
                         bind uu____8840
                           (fun uu____8859  ->
                              match uu____8859 with
                              | (t',u_t') ->
                                  let bv'' =
                                    let uu___1224_8869 = bv1  in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___1224_8869.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___1224_8869.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = t'
                                    }  in
                                  let s =
                                    let uu____8873 =
                                      let uu____8874 =
                                        let uu____8881 =
                                          FStar_Syntax_Syntax.bv_to_name bv''
                                           in
                                        (bv1, uu____8881)  in
                                      FStar_Syntax_Syntax.NT uu____8874  in
                                    [uu____8873]  in
                                  let bvs1 =
                                    FStar_List.map
                                      (fun b1  ->
                                         let uu___1229_8893 = b1  in
                                         let uu____8894 =
                                           FStar_Syntax_Subst.subst s
                                             b1.FStar_Syntax_Syntax.sort
                                            in
                                         {
                                           FStar_Syntax_Syntax.ppname =
                                             (uu___1229_8893.FStar_Syntax_Syntax.ppname);
                                           FStar_Syntax_Syntax.index =
                                             (uu___1229_8893.FStar_Syntax_Syntax.index);
                                           FStar_Syntax_Syntax.sort =
                                             uu____8894
                                         }) bvs
                                     in
                                  let env' = push_bvs e0 (bv'' :: bvs1)  in
                                  bind __dismiss
                                    (fun uu____8901  ->
                                       let new_goal =
                                         let uu____8903 =
                                           FStar_Tactics_Types.goal_with_env
                                             goal env'
                                            in
                                         let uu____8904 =
                                           let uu____8905 =
                                             FStar_Tactics_Types.goal_type
                                               goal
                                              in
                                           FStar_Syntax_Subst.subst s
                                             uu____8905
                                            in
                                         FStar_Tactics_Types.goal_with_type
                                           uu____8903 uu____8904
                                          in
                                       let uu____8906 = add_goals [new_goal]
                                          in
                                       bind uu____8906
                                         (fun uu____8911  ->
                                            let uu____8912 =
                                              FStar_Syntax_Util.mk_eq2
                                                (FStar_Syntax_Syntax.U_succ u)
                                                ty
                                                bv1.FStar_Syntax_Syntax.sort
                                                t'
                                               in
                                            add_irrelevant_goal
                                              "binder_retype equation" e0
                                              uu____8912
                                              goal.FStar_Tactics_Types.opts
                                              goal.FStar_Tactics_Types.label))))))
       in
    FStar_All.pipe_left (wrap_err "binder_retype") uu____8772
  
let (norm_binder_type :
  FStar_Syntax_Embeddings.norm_step Prims.list ->
    FStar_Syntax_Syntax.binder -> unit tac)
  =
  fun s  ->
    fun b  ->
      let uu____8938 =
        let uu____8941 = cur_goal ()  in
        bind uu____8941
          (fun goal  ->
             let uu____8950 = b  in
             match uu____8950 with
             | (bv,uu____8954) ->
                 let uu____8959 =
                   let uu____8970 = FStar_Tactics_Types.goal_env goal  in
                   split_env bv uu____8970  in
                 (match uu____8959 with
                  | FStar_Pervasives_Native.None  ->
                      fail "binder is not present in environment"
                  | FStar_Pervasives_Native.Some (e0,bv1,bvs) ->
                      let steps =
                        let uu____9000 =
                          FStar_TypeChecker_Normalize.tr_norm_steps s  in
                        FStar_List.append
                          [FStar_TypeChecker_Env.Reify;
                          FStar_TypeChecker_Env.UnfoldTac] uu____9000
                         in
                      let sort' =
                        normalize steps e0 bv1.FStar_Syntax_Syntax.sort  in
                      let bv' =
                        let uu___1250_9005 = bv1  in
                        {
                          FStar_Syntax_Syntax.ppname =
                            (uu___1250_9005.FStar_Syntax_Syntax.ppname);
                          FStar_Syntax_Syntax.index =
                            (uu___1250_9005.FStar_Syntax_Syntax.index);
                          FStar_Syntax_Syntax.sort = sort'
                        }  in
                      let env' = push_bvs e0 (bv' :: bvs)  in
                      let uu____9007 =
                        FStar_Tactics_Types.goal_with_env goal env'  in
                      replace_cur uu____9007))
         in
      FStar_All.pipe_left (wrap_err "norm_binder_type") uu____8938
  
let (revert : unit -> unit tac) =
  fun uu____9020  ->
    let uu____9023 = cur_goal ()  in
    bind uu____9023
      (fun goal  ->
         let uu____9029 =
           let uu____9036 = FStar_Tactics_Types.goal_env goal  in
           FStar_TypeChecker_Env.pop_bv uu____9036  in
         match uu____9029 with
         | FStar_Pervasives_Native.None  ->
             fail "Cannot revert; empty context"
         | FStar_Pervasives_Native.Some (x,env') ->
             let typ' =
               let uu____9053 =
                 let uu____9056 = FStar_Tactics_Types.goal_type goal  in
                 FStar_Syntax_Syntax.mk_Total uu____9056  in
               FStar_Syntax_Util.arrow [(x, FStar_Pervasives_Native.None)]
                 uu____9053
                in
             let uu____9071 = new_uvar "revert" env' typ'  in
             bind uu____9071
               (fun uu____9087  ->
                  match uu____9087 with
                  | (r,u_r) ->
                      let uu____9096 =
                        let uu____9099 =
                          let uu____9100 =
                            let uu____9101 =
                              FStar_Tactics_Types.goal_type goal  in
                            uu____9101.FStar_Syntax_Syntax.pos  in
                          let uu____9104 =
                            let uu____9109 =
                              let uu____9110 =
                                let uu____9119 =
                                  FStar_Syntax_Syntax.bv_to_name x  in
                                FStar_Syntax_Syntax.as_arg uu____9119  in
                              [uu____9110]  in
                            FStar_Syntax_Syntax.mk_Tm_app r uu____9109  in
                          uu____9104 FStar_Pervasives_Native.None uu____9100
                           in
                        set_solution goal uu____9099  in
                      bind uu____9096
                        (fun uu____9138  ->
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
      let uu____9152 = FStar_Syntax_Free.names t  in
      FStar_Util.set_mem bv uu____9152
  
let (clear : FStar_Syntax_Syntax.binder -> unit tac) =
  fun b  ->
    let bv = FStar_Pervasives_Native.fst b  in
    let uu____9168 = cur_goal ()  in
    bind uu____9168
      (fun goal  ->
         mlog
           (fun uu____9176  ->
              let uu____9177 = FStar_Syntax_Print.binder_to_string b  in
              let uu____9179 =
                let uu____9181 =
                  let uu____9183 =
                    let uu____9192 = FStar_Tactics_Types.goal_env goal  in
                    FStar_TypeChecker_Env.all_binders uu____9192  in
                  FStar_All.pipe_right uu____9183 FStar_List.length  in
                FStar_All.pipe_right uu____9181 FStar_Util.string_of_int  in
              FStar_Util.print2 "Clear of (%s), env has %s binders\n"
                uu____9177 uu____9179)
           (fun uu____9213  ->
              let uu____9214 =
                let uu____9225 = FStar_Tactics_Types.goal_env goal  in
                split_env bv uu____9225  in
              match uu____9214 with
              | FStar_Pervasives_Native.None  ->
                  fail "Cannot clear; binder not in environment"
              | FStar_Pervasives_Native.Some (e',bv1,bvs) ->
                  let rec check1 bvs1 =
                    match bvs1 with
                    | [] -> ret ()
                    | bv'::bvs2 ->
                        let uu____9270 =
                          free_in bv1 bv'.FStar_Syntax_Syntax.sort  in
                        if uu____9270
                        then
                          let uu____9275 =
                            let uu____9277 =
                              FStar_Syntax_Print.bv_to_string bv'  in
                            FStar_Util.format1
                              "Cannot clear; binder present in the type of %s"
                              uu____9277
                             in
                          fail uu____9275
                        else check1 bvs2
                     in
                  let uu____9282 =
                    let uu____9284 = FStar_Tactics_Types.goal_type goal  in
                    free_in bv1 uu____9284  in
                  if uu____9282
                  then fail "Cannot clear; binder present in goal"
                  else
                    (let uu____9291 = check1 bvs  in
                     bind uu____9291
                       (fun uu____9297  ->
                          let env' = push_bvs e' bvs  in
                          let uu____9299 =
                            let uu____9306 =
                              FStar_Tactics_Types.goal_type goal  in
                            new_uvar "clear.witness" env' uu____9306  in
                          bind uu____9299
                            (fun uu____9316  ->
                               match uu____9316 with
                               | (ut,uvar_ut) ->
                                   let uu____9325 = set_solution goal ut  in
                                   bind uu____9325
                                     (fun uu____9330  ->
                                        let uu____9331 =
                                          FStar_Tactics_Types.mk_goal env'
                                            uvar_ut
                                            goal.FStar_Tactics_Types.opts
                                            goal.FStar_Tactics_Types.is_guard
                                            goal.FStar_Tactics_Types.label
                                           in
                                        replace_cur uu____9331))))))
  
let (clear_top : unit -> unit tac) =
  fun uu____9339  ->
    let uu____9342 = cur_goal ()  in
    bind uu____9342
      (fun goal  ->
         let uu____9348 =
           let uu____9355 = FStar_Tactics_Types.goal_env goal  in
           FStar_TypeChecker_Env.pop_bv uu____9355  in
         match uu____9348 with
         | FStar_Pervasives_Native.None  ->
             fail "Cannot clear; empty context"
         | FStar_Pervasives_Native.Some (x,uu____9364) ->
             let uu____9369 = FStar_Syntax_Syntax.mk_binder x  in
             clear uu____9369)
  
let (prune : Prims.string -> unit tac) =
  fun s  ->
    let uu____9382 = cur_goal ()  in
    bind uu____9382
      (fun g  ->
         let ctx = FStar_Tactics_Types.goal_env g  in
         let ctx' =
           let uu____9392 = FStar_Ident.path_of_text s  in
           FStar_TypeChecker_Env.rem_proof_ns ctx uu____9392  in
         let g' = FStar_Tactics_Types.goal_with_env g ctx'  in replace_cur g')
  
let (addns : Prims.string -> unit tac) =
  fun s  ->
    let uu____9406 = cur_goal ()  in
    bind uu____9406
      (fun g  ->
         let ctx = FStar_Tactics_Types.goal_env g  in
         let ctx' =
           let uu____9416 = FStar_Ident.path_of_text s  in
           FStar_TypeChecker_Env.add_proof_ns ctx uu____9416  in
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
            let uu____9458 = FStar_Syntax_Subst.compress t  in
            uu____9458.FStar_Syntax_Syntax.n  in
          let uu____9461 =
            if d = FStar_Tactics_Types.TopDown
            then
              f env
                (let uu___1432_9468 = t  in
                 {
                   FStar_Syntax_Syntax.n = tn;
                   FStar_Syntax_Syntax.pos =
                     (uu___1432_9468.FStar_Syntax_Syntax.pos);
                   FStar_Syntax_Syntax.vars =
                     (uu___1432_9468.FStar_Syntax_Syntax.vars)
                 })
            else ret t  in
          bind uu____9461
            (fun t1  ->
               let ff = tac_fold_env d f env  in
               let tn1 =
                 let uu____9485 =
                   let uu____9486 = FStar_Syntax_Subst.compress t1  in
                   uu____9486.FStar_Syntax_Syntax.n  in
                 match uu____9485 with
                 | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
                     let uu____9517 = ff hd1  in
                     bind uu____9517
                       (fun hd2  ->
                          let fa uu____9543 =
                            match uu____9543 with
                            | (a,q) ->
                                let uu____9564 = ff a  in
                                bind uu____9564 (fun a1  -> ret (a1, q))
                             in
                          let uu____9583 = mapM fa args  in
                          bind uu____9583
                            (fun args1  ->
                               ret (FStar_Syntax_Syntax.Tm_app (hd2, args1))))
                 | FStar_Syntax_Syntax.Tm_abs (bs,t2,k) ->
                     let uu____9665 = FStar_Syntax_Subst.open_term bs t2  in
                     (match uu____9665 with
                      | (bs1,t') ->
                          let uu____9674 =
                            let uu____9677 =
                              FStar_TypeChecker_Env.push_binders env bs1  in
                            tac_fold_env d f uu____9677 t'  in
                          bind uu____9674
                            (fun t''  ->
                               let uu____9681 =
                                 let uu____9682 =
                                   let uu____9701 =
                                     FStar_Syntax_Subst.close_binders bs1  in
                                   let uu____9710 =
                                     FStar_Syntax_Subst.close bs1 t''  in
                                   (uu____9701, uu____9710, k)  in
                                 FStar_Syntax_Syntax.Tm_abs uu____9682  in
                               ret uu____9681))
                 | FStar_Syntax_Syntax.Tm_arrow (bs,k) -> ret tn
                 | FStar_Syntax_Syntax.Tm_match (hd1,brs) ->
                     let uu____9785 = ff hd1  in
                     bind uu____9785
                       (fun hd2  ->
                          let ffb br =
                            let uu____9800 =
                              FStar_Syntax_Subst.open_branch br  in
                            match uu____9800 with
                            | (pat,w,e) ->
                                let bvs = FStar_Syntax_Syntax.pat_bvs pat  in
                                let ff1 =
                                  let uu____9832 =
                                    FStar_TypeChecker_Env.push_bvs env bvs
                                     in
                                  tac_fold_env d f uu____9832  in
                                let uu____9833 = ff1 e  in
                                bind uu____9833
                                  (fun e1  ->
                                     let br1 =
                                       FStar_Syntax_Subst.close_branch
                                         (pat, w, e1)
                                        in
                                     ret br1)
                             in
                          let uu____9848 = mapM ffb brs  in
                          bind uu____9848
                            (fun brs1  ->
                               ret (FStar_Syntax_Syntax.Tm_match (hd2, brs1))))
                 | FStar_Syntax_Syntax.Tm_let
                     ((false
                       ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inl bv;
                          FStar_Syntax_Syntax.lbunivs = uu____9892;
                          FStar_Syntax_Syntax.lbtyp = uu____9893;
                          FStar_Syntax_Syntax.lbeff = uu____9894;
                          FStar_Syntax_Syntax.lbdef = def;
                          FStar_Syntax_Syntax.lbattrs = uu____9896;
                          FStar_Syntax_Syntax.lbpos = uu____9897;_}::[]),e)
                     ->
                     let lb =
                       let uu____9925 =
                         let uu____9926 = FStar_Syntax_Subst.compress t1  in
                         uu____9926.FStar_Syntax_Syntax.n  in
                       match uu____9925 with
                       | FStar_Syntax_Syntax.Tm_let
                           ((false ,lb::[]),uu____9930) -> lb
                       | uu____9946 -> failwith "impossible"  in
                     let fflb lb1 =
                       let uu____9956 = ff lb1.FStar_Syntax_Syntax.lbdef  in
                       bind uu____9956
                         (fun def1  ->
                            ret
                              (let uu___1385_9962 = lb1  in
                               {
                                 FStar_Syntax_Syntax.lbname =
                                   (uu___1385_9962.FStar_Syntax_Syntax.lbname);
                                 FStar_Syntax_Syntax.lbunivs =
                                   (uu___1385_9962.FStar_Syntax_Syntax.lbunivs);
                                 FStar_Syntax_Syntax.lbtyp =
                                   (uu___1385_9962.FStar_Syntax_Syntax.lbtyp);
                                 FStar_Syntax_Syntax.lbeff =
                                   (uu___1385_9962.FStar_Syntax_Syntax.lbeff);
                                 FStar_Syntax_Syntax.lbdef = def1;
                                 FStar_Syntax_Syntax.lbattrs =
                                   (uu___1385_9962.FStar_Syntax_Syntax.lbattrs);
                                 FStar_Syntax_Syntax.lbpos =
                                   (uu___1385_9962.FStar_Syntax_Syntax.lbpos)
                               }))
                        in
                     let uu____9963 = fflb lb  in
                     bind uu____9963
                       (fun lb1  ->
                          let uu____9973 =
                            let uu____9978 =
                              let uu____9979 =
                                FStar_Syntax_Syntax.mk_binder bv  in
                              [uu____9979]  in
                            FStar_Syntax_Subst.open_term uu____9978 e  in
                          match uu____9973 with
                          | (bs,e1) ->
                              let ff1 =
                                let uu____10009 =
                                  FStar_TypeChecker_Env.push_binders env bs
                                   in
                                tac_fold_env d f uu____10009  in
                              let uu____10010 = ff1 e1  in
                              bind uu____10010
                                (fun e2  ->
                                   let e3 = FStar_Syntax_Subst.close bs e2
                                      in
                                   ret
                                     (FStar_Syntax_Syntax.Tm_let
                                        ((false, [lb1]), e3))))
                 | FStar_Syntax_Syntax.Tm_let ((true ,lbs),e) ->
                     let fflb lb =
                       let uu____10057 = ff lb.FStar_Syntax_Syntax.lbdef  in
                       bind uu____10057
                         (fun def  ->
                            ret
                              (let uu___1403_10063 = lb  in
                               {
                                 FStar_Syntax_Syntax.lbname =
                                   (uu___1403_10063.FStar_Syntax_Syntax.lbname);
                                 FStar_Syntax_Syntax.lbunivs =
                                   (uu___1403_10063.FStar_Syntax_Syntax.lbunivs);
                                 FStar_Syntax_Syntax.lbtyp =
                                   (uu___1403_10063.FStar_Syntax_Syntax.lbtyp);
                                 FStar_Syntax_Syntax.lbeff =
                                   (uu___1403_10063.FStar_Syntax_Syntax.lbeff);
                                 FStar_Syntax_Syntax.lbdef = def;
                                 FStar_Syntax_Syntax.lbattrs =
                                   (uu___1403_10063.FStar_Syntax_Syntax.lbattrs);
                                 FStar_Syntax_Syntax.lbpos =
                                   (uu___1403_10063.FStar_Syntax_Syntax.lbpos)
                               }))
                        in
                     let uu____10064 = FStar_Syntax_Subst.open_let_rec lbs e
                        in
                     (match uu____10064 with
                      | (lbs1,e1) ->
                          let uu____10079 = mapM fflb lbs1  in
                          bind uu____10079
                            (fun lbs2  ->
                               let uu____10091 = ff e1  in
                               bind uu____10091
                                 (fun e2  ->
                                    let uu____10099 =
                                      FStar_Syntax_Subst.close_let_rec lbs2
                                        e2
                                       in
                                    match uu____10099 with
                                    | (lbs3,e3) ->
                                        ret
                                          (FStar_Syntax_Syntax.Tm_let
                                             ((true, lbs3), e3)))))
                 | FStar_Syntax_Syntax.Tm_ascribed (t2,asc,eff) ->
                     let uu____10170 = ff t2  in
                     bind uu____10170
                       (fun t3  ->
                          ret
                            (FStar_Syntax_Syntax.Tm_ascribed (t3, asc, eff)))
                 | FStar_Syntax_Syntax.Tm_meta (t2,m) ->
                     let uu____10201 = ff t2  in
                     bind uu____10201
                       (fun t3  -> ret (FStar_Syntax_Syntax.Tm_meta (t3, m)))
                 | uu____10208 -> ret tn  in
               bind tn1
                 (fun tn2  ->
                    let t' =
                      let uu___1427_10215 = t1  in
                      {
                        FStar_Syntax_Syntax.n = tn2;
                        FStar_Syntax_Syntax.pos =
                          (uu___1427_10215.FStar_Syntax_Syntax.pos);
                        FStar_Syntax_Syntax.vars =
                          (uu___1427_10215.FStar_Syntax_Syntax.vars)
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
              let uu____10262 =
                FStar_TypeChecker_TcTerm.tc_term
                  (let uu___1440_10271 = env  in
                   {
                     FStar_TypeChecker_Env.solver =
                       (uu___1440_10271.FStar_TypeChecker_Env.solver);
                     FStar_TypeChecker_Env.range =
                       (uu___1440_10271.FStar_TypeChecker_Env.range);
                     FStar_TypeChecker_Env.curmodule =
                       (uu___1440_10271.FStar_TypeChecker_Env.curmodule);
                     FStar_TypeChecker_Env.gamma =
                       (uu___1440_10271.FStar_TypeChecker_Env.gamma);
                     FStar_TypeChecker_Env.gamma_sig =
                       (uu___1440_10271.FStar_TypeChecker_Env.gamma_sig);
                     FStar_TypeChecker_Env.gamma_cache =
                       (uu___1440_10271.FStar_TypeChecker_Env.gamma_cache);
                     FStar_TypeChecker_Env.modules =
                       (uu___1440_10271.FStar_TypeChecker_Env.modules);
                     FStar_TypeChecker_Env.expected_typ =
                       (uu___1440_10271.FStar_TypeChecker_Env.expected_typ);
                     FStar_TypeChecker_Env.sigtab =
                       (uu___1440_10271.FStar_TypeChecker_Env.sigtab);
                     FStar_TypeChecker_Env.attrtab =
                       (uu___1440_10271.FStar_TypeChecker_Env.attrtab);
                     FStar_TypeChecker_Env.instantiate_imp =
                       (uu___1440_10271.FStar_TypeChecker_Env.instantiate_imp);
                     FStar_TypeChecker_Env.effects =
                       (uu___1440_10271.FStar_TypeChecker_Env.effects);
                     FStar_TypeChecker_Env.generalize =
                       (uu___1440_10271.FStar_TypeChecker_Env.generalize);
                     FStar_TypeChecker_Env.letrecs =
                       (uu___1440_10271.FStar_TypeChecker_Env.letrecs);
                     FStar_TypeChecker_Env.top_level =
                       (uu___1440_10271.FStar_TypeChecker_Env.top_level);
                     FStar_TypeChecker_Env.check_uvars =
                       (uu___1440_10271.FStar_TypeChecker_Env.check_uvars);
                     FStar_TypeChecker_Env.use_eq =
                       (uu___1440_10271.FStar_TypeChecker_Env.use_eq);
                     FStar_TypeChecker_Env.use_eq_strict =
                       (uu___1440_10271.FStar_TypeChecker_Env.use_eq_strict);
                     FStar_TypeChecker_Env.is_iface =
                       (uu___1440_10271.FStar_TypeChecker_Env.is_iface);
                     FStar_TypeChecker_Env.admit =
                       (uu___1440_10271.FStar_TypeChecker_Env.admit);
                     FStar_TypeChecker_Env.lax = true;
                     FStar_TypeChecker_Env.lax_universes =
                       (uu___1440_10271.FStar_TypeChecker_Env.lax_universes);
                     FStar_TypeChecker_Env.phase1 =
                       (uu___1440_10271.FStar_TypeChecker_Env.phase1);
                     FStar_TypeChecker_Env.failhard =
                       (uu___1440_10271.FStar_TypeChecker_Env.failhard);
                     FStar_TypeChecker_Env.nosynth =
                       (uu___1440_10271.FStar_TypeChecker_Env.nosynth);
                     FStar_TypeChecker_Env.uvar_subtyping =
                       (uu___1440_10271.FStar_TypeChecker_Env.uvar_subtyping);
                     FStar_TypeChecker_Env.tc_term =
                       (uu___1440_10271.FStar_TypeChecker_Env.tc_term);
                     FStar_TypeChecker_Env.type_of =
                       (uu___1440_10271.FStar_TypeChecker_Env.type_of);
                     FStar_TypeChecker_Env.universe_of =
                       (uu___1440_10271.FStar_TypeChecker_Env.universe_of);
                     FStar_TypeChecker_Env.check_type_of =
                       (uu___1440_10271.FStar_TypeChecker_Env.check_type_of);
                     FStar_TypeChecker_Env.use_bv_sorts =
                       (uu___1440_10271.FStar_TypeChecker_Env.use_bv_sorts);
                     FStar_TypeChecker_Env.qtbl_name_and_index =
                       (uu___1440_10271.FStar_TypeChecker_Env.qtbl_name_and_index);
                     FStar_TypeChecker_Env.normalized_eff_names =
                       (uu___1440_10271.FStar_TypeChecker_Env.normalized_eff_names);
                     FStar_TypeChecker_Env.fv_delta_depths =
                       (uu___1440_10271.FStar_TypeChecker_Env.fv_delta_depths);
                     FStar_TypeChecker_Env.proof_ns =
                       (uu___1440_10271.FStar_TypeChecker_Env.proof_ns);
                     FStar_TypeChecker_Env.synth_hook =
                       (uu___1440_10271.FStar_TypeChecker_Env.synth_hook);
                     FStar_TypeChecker_Env.try_solve_implicits_hook =
                       (uu___1440_10271.FStar_TypeChecker_Env.try_solve_implicits_hook);
                     FStar_TypeChecker_Env.splice =
                       (uu___1440_10271.FStar_TypeChecker_Env.splice);
                     FStar_TypeChecker_Env.mpreprocess =
                       (uu___1440_10271.FStar_TypeChecker_Env.mpreprocess);
                     FStar_TypeChecker_Env.postprocess =
                       (uu___1440_10271.FStar_TypeChecker_Env.postprocess);
                     FStar_TypeChecker_Env.is_native_tactic =
                       (uu___1440_10271.FStar_TypeChecker_Env.is_native_tactic);
                     FStar_TypeChecker_Env.identifier_info =
                       (uu___1440_10271.FStar_TypeChecker_Env.identifier_info);
                     FStar_TypeChecker_Env.tc_hooks =
                       (uu___1440_10271.FStar_TypeChecker_Env.tc_hooks);
                     FStar_TypeChecker_Env.dsenv =
                       (uu___1440_10271.FStar_TypeChecker_Env.dsenv);
                     FStar_TypeChecker_Env.nbe =
                       (uu___1440_10271.FStar_TypeChecker_Env.nbe);
                     FStar_TypeChecker_Env.strict_args_tab =
                       (uu___1440_10271.FStar_TypeChecker_Env.strict_args_tab);
                     FStar_TypeChecker_Env.erasable_types_tab =
                       (uu___1440_10271.FStar_TypeChecker_Env.erasable_types_tab)
                   }) t
                 in
              match uu____10262 with
              | (uu____10275,lcomp,g) ->
                  let uu____10278 =
                    (let uu____10282 =
                       FStar_TypeChecker_Common.is_pure_or_ghost_lcomp lcomp
                        in
                     Prims.op_Negation uu____10282) ||
                      (let uu____10285 = FStar_TypeChecker_Env.is_trivial g
                          in
                       Prims.op_Negation uu____10285)
                     in
                  if uu____10278
                  then ret t
                  else
                    (let rewrite_eq =
                       let typ = lcomp.FStar_TypeChecker_Common.res_typ  in
                       let uu____10296 = new_uvar "pointwise_rec" env typ  in
                       bind uu____10296
                         (fun uu____10313  ->
                            match uu____10313 with
                            | (ut,uvar_ut) ->
                                (log ps
                                   (fun uu____10326  ->
                                      let uu____10327 =
                                        FStar_Syntax_Print.term_to_string t
                                         in
                                      let uu____10329 =
                                        FStar_Syntax_Print.term_to_string ut
                                         in
                                      FStar_Util.print2
                                        "Pointwise_rec: making equality\n\t%s ==\n\t%s\n"
                                        uu____10327 uu____10329);
                                 (let uu____10332 =
                                    let uu____10335 =
                                      let uu____10336 =
                                        FStar_TypeChecker_TcTerm.universe_of
                                          env typ
                                         in
                                      FStar_Syntax_Util.mk_eq2 uu____10336
                                        typ t ut
                                       in
                                    add_irrelevant_goal
                                      "pointwise_rec equation" env
                                      uu____10335 opts label1
                                     in
                                  bind uu____10332
                                    (fun uu____10340  ->
                                       let uu____10341 =
                                         bind tau
                                           (fun uu____10347  ->
                                              let ut1 =
                                                FStar_TypeChecker_Normalize.reduce_uvar_solutions
                                                  env ut
                                                 in
                                              log ps
                                                (fun uu____10353  ->
                                                   let uu____10354 =
                                                     FStar_Syntax_Print.term_to_string
                                                       t
                                                      in
                                                   let uu____10356 =
                                                     FStar_Syntax_Print.term_to_string
                                                       ut1
                                                      in
                                                   FStar_Util.print2
                                                     "pointwise_rec: succeeded rewriting\n\t%s to\n\t%s\n"
                                                     uu____10354 uu____10356);
                                              ret ut1)
                                          in
                                       focus uu____10341))))
                        in
                     let uu____10359 = catch rewrite_eq  in
                     bind uu____10359
                       (fun uu___5_10371  ->
                          match uu___5_10371 with
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
          let uu____10571 = FStar_Syntax_Subst.compress t  in
          maybe_continue ctrl uu____10571
            (fun t1  ->
               let uu____10579 =
                 f env
                   (let uu___1517_10587 = t1  in
                    {
                      FStar_Syntax_Syntax.n = (t1.FStar_Syntax_Syntax.n);
                      FStar_Syntax_Syntax.pos =
                        (uu___1517_10587.FStar_Syntax_Syntax.pos);
                      FStar_Syntax_Syntax.vars =
                        (uu___1517_10587.FStar_Syntax_Syntax.vars)
                    })
                  in
               bind uu____10579
                 (fun uu____10603  ->
                    match uu____10603 with
                    | (t2,ctrl1) ->
                        maybe_continue ctrl1 t2
                          (fun t3  ->
                             let uu____10626 =
                               let uu____10627 =
                                 FStar_Syntax_Subst.compress t3  in
                               uu____10627.FStar_Syntax_Syntax.n  in
                             match uu____10626 with
                             | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
                                 let uu____10664 =
                                   ctrl_tac_fold f env ctrl1 hd1  in
                                 bind uu____10664
                                   (fun uu____10686  ->
                                      match uu____10686 with
                                      | (hd2,ctrl2) ->
                                          let ctrl3 = keep_going ctrl2  in
                                          let uu____10702 =
                                            ctrl_tac_fold_args f env ctrl3
                                              args
                                             in
                                          bind uu____10702
                                            (fun uu____10726  ->
                                               match uu____10726 with
                                               | (args1,ctrl4) ->
                                                   ret
                                                     ((let uu___1497_10756 =
                                                         t3  in
                                                       {
                                                         FStar_Syntax_Syntax.n
                                                           =
                                                           (FStar_Syntax_Syntax.Tm_app
                                                              (hd2, args1));
                                                         FStar_Syntax_Syntax.pos
                                                           =
                                                           (uu___1497_10756.FStar_Syntax_Syntax.pos);
                                                         FStar_Syntax_Syntax.vars
                                                           =
                                                           (uu___1497_10756.FStar_Syntax_Syntax.vars)
                                                       }), ctrl4)))
                             | FStar_Syntax_Syntax.Tm_abs (bs,t4,k) ->
                                 let uu____10798 =
                                   FStar_Syntax_Subst.open_term bs t4  in
                                 (match uu____10798 with
                                  | (bs1,t') ->
                                      let uu____10813 =
                                        let uu____10820 =
                                          FStar_TypeChecker_Env.push_binders
                                            env bs1
                                           in
                                        ctrl_tac_fold f uu____10820 ctrl1 t'
                                         in
                                      bind uu____10813
                                        (fun uu____10835  ->
                                           match uu____10835 with
                                           | (t'',ctrl2) ->
                                               let uu____10850 =
                                                 let uu____10857 =
                                                   let uu___1510_10860 = t4
                                                      in
                                                   let uu____10863 =
                                                     let uu____10864 =
                                                       let uu____10883 =
                                                         FStar_Syntax_Subst.close_binders
                                                           bs1
                                                          in
                                                       let uu____10892 =
                                                         FStar_Syntax_Subst.close
                                                           bs1 t''
                                                          in
                                                       (uu____10883,
                                                         uu____10892, k)
                                                        in
                                                     FStar_Syntax_Syntax.Tm_abs
                                                       uu____10864
                                                      in
                                                   {
                                                     FStar_Syntax_Syntax.n =
                                                       uu____10863;
                                                     FStar_Syntax_Syntax.pos
                                                       =
                                                       (uu___1510_10860.FStar_Syntax_Syntax.pos);
                                                     FStar_Syntax_Syntax.vars
                                                       =
                                                       (uu___1510_10860.FStar_Syntax_Syntax.vars)
                                                   }  in
                                                 (uu____10857, ctrl2)  in
                                               ret uu____10850))
                             | FStar_Syntax_Syntax.Tm_arrow (bs,k) ->
                                 ret (t3, ctrl1)
                             | uu____10945 -> ret (t3, ctrl1))))

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
              let uu____10991 = ctrl_tac_fold f env ctrl t  in
              bind uu____10991
                (fun uu____11012  ->
                   match uu____11012 with
                   | (t1,ctrl1) ->
                       let uu____11027 = ctrl_tac_fold_args f env ctrl1 ts1
                          in
                       bind uu____11027
                         (fun uu____11051  ->
                            match uu____11051 with
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
                let uu____11142 =
                  let uu____11150 =
                    add_irrelevant_goal "dummy" env FStar_Syntax_Util.t_true
                      opts label1
                     in
                  bind uu____11150
                    (fun uu____11161  ->
                       let uu____11162 = ctrl t1  in
                       bind uu____11162
                         (fun res  ->
                            let uu____11188 = trivial ()  in
                            bind uu____11188 (fun uu____11197  -> ret res)))
                   in
                bind uu____11142
                  (fun uu____11215  ->
                     match uu____11215 with
                     | (should_rewrite,ctrl1) ->
                         if Prims.op_Negation should_rewrite
                         then ret (t1, ctrl1)
                         else
                           (let uu____11244 =
                              FStar_TypeChecker_TcTerm.tc_term
                                (let uu___1547_11253 = env  in
                                 {
                                   FStar_TypeChecker_Env.solver =
                                     (uu___1547_11253.FStar_TypeChecker_Env.solver);
                                   FStar_TypeChecker_Env.range =
                                     (uu___1547_11253.FStar_TypeChecker_Env.range);
                                   FStar_TypeChecker_Env.curmodule =
                                     (uu___1547_11253.FStar_TypeChecker_Env.curmodule);
                                   FStar_TypeChecker_Env.gamma =
                                     (uu___1547_11253.FStar_TypeChecker_Env.gamma);
                                   FStar_TypeChecker_Env.gamma_sig =
                                     (uu___1547_11253.FStar_TypeChecker_Env.gamma_sig);
                                   FStar_TypeChecker_Env.gamma_cache =
                                     (uu___1547_11253.FStar_TypeChecker_Env.gamma_cache);
                                   FStar_TypeChecker_Env.modules =
                                     (uu___1547_11253.FStar_TypeChecker_Env.modules);
                                   FStar_TypeChecker_Env.expected_typ =
                                     (uu___1547_11253.FStar_TypeChecker_Env.expected_typ);
                                   FStar_TypeChecker_Env.sigtab =
                                     (uu___1547_11253.FStar_TypeChecker_Env.sigtab);
                                   FStar_TypeChecker_Env.attrtab =
                                     (uu___1547_11253.FStar_TypeChecker_Env.attrtab);
                                   FStar_TypeChecker_Env.instantiate_imp =
                                     (uu___1547_11253.FStar_TypeChecker_Env.instantiate_imp);
                                   FStar_TypeChecker_Env.effects =
                                     (uu___1547_11253.FStar_TypeChecker_Env.effects);
                                   FStar_TypeChecker_Env.generalize =
                                     (uu___1547_11253.FStar_TypeChecker_Env.generalize);
                                   FStar_TypeChecker_Env.letrecs =
                                     (uu___1547_11253.FStar_TypeChecker_Env.letrecs);
                                   FStar_TypeChecker_Env.top_level =
                                     (uu___1547_11253.FStar_TypeChecker_Env.top_level);
                                   FStar_TypeChecker_Env.check_uvars =
                                     (uu___1547_11253.FStar_TypeChecker_Env.check_uvars);
                                   FStar_TypeChecker_Env.use_eq =
                                     (uu___1547_11253.FStar_TypeChecker_Env.use_eq);
                                   FStar_TypeChecker_Env.use_eq_strict =
                                     (uu___1547_11253.FStar_TypeChecker_Env.use_eq_strict);
                                   FStar_TypeChecker_Env.is_iface =
                                     (uu___1547_11253.FStar_TypeChecker_Env.is_iface);
                                   FStar_TypeChecker_Env.admit =
                                     (uu___1547_11253.FStar_TypeChecker_Env.admit);
                                   FStar_TypeChecker_Env.lax = true;
                                   FStar_TypeChecker_Env.lax_universes =
                                     (uu___1547_11253.FStar_TypeChecker_Env.lax_universes);
                                   FStar_TypeChecker_Env.phase1 =
                                     (uu___1547_11253.FStar_TypeChecker_Env.phase1);
                                   FStar_TypeChecker_Env.failhard =
                                     (uu___1547_11253.FStar_TypeChecker_Env.failhard);
                                   FStar_TypeChecker_Env.nosynth =
                                     (uu___1547_11253.FStar_TypeChecker_Env.nosynth);
                                   FStar_TypeChecker_Env.uvar_subtyping =
                                     (uu___1547_11253.FStar_TypeChecker_Env.uvar_subtyping);
                                   FStar_TypeChecker_Env.tc_term =
                                     (uu___1547_11253.FStar_TypeChecker_Env.tc_term);
                                   FStar_TypeChecker_Env.type_of =
                                     (uu___1547_11253.FStar_TypeChecker_Env.type_of);
                                   FStar_TypeChecker_Env.universe_of =
                                     (uu___1547_11253.FStar_TypeChecker_Env.universe_of);
                                   FStar_TypeChecker_Env.check_type_of =
                                     (uu___1547_11253.FStar_TypeChecker_Env.check_type_of);
                                   FStar_TypeChecker_Env.use_bv_sorts =
                                     (uu___1547_11253.FStar_TypeChecker_Env.use_bv_sorts);
                                   FStar_TypeChecker_Env.qtbl_name_and_index
                                     =
                                     (uu___1547_11253.FStar_TypeChecker_Env.qtbl_name_and_index);
                                   FStar_TypeChecker_Env.normalized_eff_names
                                     =
                                     (uu___1547_11253.FStar_TypeChecker_Env.normalized_eff_names);
                                   FStar_TypeChecker_Env.fv_delta_depths =
                                     (uu___1547_11253.FStar_TypeChecker_Env.fv_delta_depths);
                                   FStar_TypeChecker_Env.proof_ns =
                                     (uu___1547_11253.FStar_TypeChecker_Env.proof_ns);
                                   FStar_TypeChecker_Env.synth_hook =
                                     (uu___1547_11253.FStar_TypeChecker_Env.synth_hook);
                                   FStar_TypeChecker_Env.try_solve_implicits_hook
                                     =
                                     (uu___1547_11253.FStar_TypeChecker_Env.try_solve_implicits_hook);
                                   FStar_TypeChecker_Env.splice =
                                     (uu___1547_11253.FStar_TypeChecker_Env.splice);
                                   FStar_TypeChecker_Env.mpreprocess =
                                     (uu___1547_11253.FStar_TypeChecker_Env.mpreprocess);
                                   FStar_TypeChecker_Env.postprocess =
                                     (uu___1547_11253.FStar_TypeChecker_Env.postprocess);
                                   FStar_TypeChecker_Env.is_native_tactic =
                                     (uu___1547_11253.FStar_TypeChecker_Env.is_native_tactic);
                                   FStar_TypeChecker_Env.identifier_info =
                                     (uu___1547_11253.FStar_TypeChecker_Env.identifier_info);
                                   FStar_TypeChecker_Env.tc_hooks =
                                     (uu___1547_11253.FStar_TypeChecker_Env.tc_hooks);
                                   FStar_TypeChecker_Env.dsenv =
                                     (uu___1547_11253.FStar_TypeChecker_Env.dsenv);
                                   FStar_TypeChecker_Env.nbe =
                                     (uu___1547_11253.FStar_TypeChecker_Env.nbe);
                                   FStar_TypeChecker_Env.strict_args_tab =
                                     (uu___1547_11253.FStar_TypeChecker_Env.strict_args_tab);
                                   FStar_TypeChecker_Env.erasable_types_tab =
                                     (uu___1547_11253.FStar_TypeChecker_Env.erasable_types_tab)
                                 }) t1
                               in
                            match uu____11244 with
                            | (t2,lcomp,g) ->
                                let uu____11264 =
                                  (let uu____11268 =
                                     FStar_TypeChecker_Common.is_pure_or_ghost_lcomp
                                       lcomp
                                      in
                                   Prims.op_Negation uu____11268) ||
                                    (let uu____11271 =
                                       FStar_TypeChecker_Env.is_trivial g  in
                                     Prims.op_Negation uu____11271)
                                   in
                                if uu____11264
                                then ret (t2, globalStop)
                                else
                                  (let typ =
                                     lcomp.FStar_TypeChecker_Common.res_typ
                                      in
                                   let uu____11287 =
                                     new_uvar "pointwise_rec" env typ  in
                                   bind uu____11287
                                     (fun uu____11308  ->
                                        match uu____11308 with
                                        | (ut,uvar_ut) ->
                                            (log ps
                                               (fun uu____11325  ->
                                                  let uu____11326 =
                                                    FStar_Syntax_Print.term_to_string
                                                      t2
                                                     in
                                                  let uu____11328 =
                                                    FStar_Syntax_Print.term_to_string
                                                      ut
                                                     in
                                                  FStar_Util.print2
                                                    "Pointwise_rec: making equality\n\t%s ==\n\t%s\n"
                                                    uu____11326 uu____11328);
                                             (let uu____11331 =
                                                let uu____11334 =
                                                  let uu____11335 =
                                                    FStar_TypeChecker_TcTerm.universe_of
                                                      env typ
                                                     in
                                                  FStar_Syntax_Util.mk_eq2
                                                    uu____11335 typ t2 ut
                                                   in
                                                add_irrelevant_goal
                                                  "rewrite_rec equation" env
                                                  uu____11334 opts label1
                                                 in
                                              bind uu____11331
                                                (fun uu____11343  ->
                                                   let uu____11344 =
                                                     bind rewriter
                                                       (fun uu____11358  ->
                                                          let ut1 =
                                                            FStar_TypeChecker_Normalize.reduce_uvar_solutions
                                                              env ut
                                                             in
                                                          log ps
                                                            (fun uu____11364 
                                                               ->
                                                               let uu____11365
                                                                 =
                                                                 FStar_Syntax_Print.term_to_string
                                                                   t2
                                                                  in
                                                               let uu____11367
                                                                 =
                                                                 FStar_Syntax_Print.term_to_string
                                                                   ut1
                                                                  in
                                                               FStar_Util.print2
                                                                 "rewrite_rec: succeeded rewriting\n\t%s to\n\t%s\n"
                                                                 uu____11365
                                                                 uu____11367);
                                                          ret (ut1, ctrl1))
                                                      in
                                                   focus uu____11344)))))))
  
let (topdown_rewrite :
  (FStar_Syntax_Syntax.term -> (Prims.bool * FStar_BigInt.t) tac) ->
    unit tac -> unit tac)
  =
  fun ctrl  ->
    fun rewriter  ->
      let uu____11412 =
        bind get
          (fun ps  ->
             let uu____11422 =
               match ps.FStar_Tactics_Types.goals with
               | g::gs -> (g, gs)
               | [] -> failwith "no goals"  in
             match uu____11422 with
             | (g,gs) ->
                 let gt1 = FStar_Tactics_Types.goal_type g  in
                 (log ps
                    (fun uu____11460  ->
                       let uu____11461 =
                         FStar_Syntax_Print.term_to_string gt1  in
                       FStar_Util.print1 "Topdown_rewrite starting with %s\n"
                         uu____11461);
                  bind dismiss_all
                    (fun uu____11466  ->
                       let uu____11467 =
                         let uu____11474 = FStar_Tactics_Types.goal_env g  in
                         ctrl_tac_fold
                           (rewrite_rec ps ctrl rewriter
                              g.FStar_Tactics_Types.opts
                              g.FStar_Tactics_Types.label) uu____11474
                           keepGoing gt1
                          in
                       bind uu____11467
                         (fun uu____11484  ->
                            match uu____11484 with
                            | (gt',uu____11492) ->
                                (log ps
                                   (fun uu____11496  ->
                                      let uu____11497 =
                                        FStar_Syntax_Print.term_to_string gt'
                                         in
                                      FStar_Util.print1
                                        "Topdown_rewrite seems to have succeded with %s\n"
                                        uu____11497);
                                 (let uu____11500 = push_goals gs  in
                                  bind uu____11500
                                    (fun uu____11505  ->
                                       let uu____11506 =
                                         let uu____11509 =
                                           let uu____11510 =
                                             FStar_Tactics_Types.goal_with_type
                                               g gt'
                                              in
                                           FStar_All.pipe_right uu____11510
                                             bnorm_goal
                                            in
                                         [uu____11509]  in
                                       add_goals uu____11506)))))))
         in
      FStar_All.pipe_left (wrap_err "topdown_rewrite") uu____11412
  
let (t_pointwise : FStar_Tactics_Types.direction -> unit tac -> unit tac) =
  fun d  ->
    fun tau  ->
      let uu____11535 =
        bind get
          (fun ps  ->
             let uu____11545 =
               match ps.FStar_Tactics_Types.goals with
               | g::gs -> (g, gs)
               | [] -> failwith "no goals"  in
             match uu____11545 with
             | (g,gs) ->
                 let gt1 = FStar_Tactics_Types.goal_type g  in
                 (log ps
                    (fun uu____11583  ->
                       let uu____11584 =
                         FStar_Syntax_Print.term_to_string gt1  in
                       FStar_Util.print1 "Pointwise starting with %s\n"
                         uu____11584);
                  bind dismiss_all
                    (fun uu____11589  ->
                       let uu____11590 =
                         let uu____11593 = FStar_Tactics_Types.goal_env g  in
                         tac_fold_env d
                           (pointwise_rec ps tau g.FStar_Tactics_Types.opts
                              g.FStar_Tactics_Types.label) uu____11593 gt1
                          in
                       bind uu____11590
                         (fun gt'  ->
                            log ps
                              (fun uu____11601  ->
                                 let uu____11602 =
                                   FStar_Syntax_Print.term_to_string gt'  in
                                 FStar_Util.print1
                                   "Pointwise seems to have succeded with %s\n"
                                   uu____11602);
                            (let uu____11605 = push_goals gs  in
                             bind uu____11605
                               (fun uu____11610  ->
                                  let uu____11611 =
                                    let uu____11614 =
                                      let uu____11615 =
                                        FStar_Tactics_Types.goal_with_type g
                                          gt'
                                         in
                                      FStar_All.pipe_right uu____11615
                                        bnorm_goal
                                       in
                                    [uu____11614]  in
                                  add_goals uu____11611))))))
         in
      FStar_All.pipe_left (wrap_err "t_pointwise") uu____11535
  
let (_trefl :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> unit tac) =
  fun l  ->
    fun r  ->
      let uu____11636 = cur_goal ()  in
      bind uu____11636
        (fun g  ->
           let uu____11642 =
             let uu____11646 = FStar_Tactics_Types.goal_env g  in
             do_unify uu____11646 l r  in
           bind uu____11642
             (fun b  ->
                if b
                then solve' g FStar_Syntax_Util.exp_unit
                else
                  (let l1 =
                     let uu____11657 = FStar_Tactics_Types.goal_env g  in
                     FStar_TypeChecker_Normalize.normalize
                       [FStar_TypeChecker_Env.UnfoldUntil
                          FStar_Syntax_Syntax.delta_constant;
                       FStar_TypeChecker_Env.Primops;
                       FStar_TypeChecker_Env.UnfoldTac] uu____11657 l
                      in
                   let r1 =
                     let uu____11659 = FStar_Tactics_Types.goal_env g  in
                     FStar_TypeChecker_Normalize.normalize
                       [FStar_TypeChecker_Env.UnfoldUntil
                          FStar_Syntax_Syntax.delta_constant;
                       FStar_TypeChecker_Env.Primops;
                       FStar_TypeChecker_Env.UnfoldTac] uu____11659 r
                      in
                   let uu____11660 =
                     let uu____11664 = FStar_Tactics_Types.goal_env g  in
                     do_unify uu____11664 l1 r1  in
                   bind uu____11660
                     (fun b1  ->
                        if b1
                        then solve' g FStar_Syntax_Util.exp_unit
                        else
                          (let uu____11674 =
                             let uu____11681 =
                               let uu____11687 =
                                 FStar_Tactics_Types.goal_env g  in
                               tts uu____11687  in
                             FStar_TypeChecker_Err.print_discrepancy
                               uu____11681 l1 r1
                              in
                           match uu____11674 with
                           | (ls,rs) ->
                               fail2 "not a trivial equality ((%s) vs (%s))"
                                 ls rs)))))
  
let (trefl : unit -> unit tac) =
  fun uu____11704  ->
    let uu____11707 =
      let uu____11710 = cur_goal ()  in
      bind uu____11710
        (fun g  ->
           let uu____11718 =
             let uu____11725 =
               let uu____11726 = FStar_Tactics_Types.goal_env g  in
               let uu____11727 = FStar_Tactics_Types.goal_type g  in
               bnorm uu____11726 uu____11727  in
             destruct_eq uu____11725  in
           match uu____11718 with
           | FStar_Pervasives_Native.Some (l,r) -> _trefl l r
           | FStar_Pervasives_Native.None  ->
               let uu____11740 =
                 let uu____11742 = FStar_Tactics_Types.goal_env g  in
                 let uu____11743 = FStar_Tactics_Types.goal_type g  in
                 tts uu____11742 uu____11743  in
               fail1 "not an equality (%s)" uu____11740)
       in
    FStar_All.pipe_left (wrap_err "trefl") uu____11707
  
let (dup : unit -> unit tac) =
  fun uu____11757  ->
    let uu____11760 = cur_goal ()  in
    bind uu____11760
      (fun g  ->
         let uu____11766 =
           let uu____11773 = FStar_Tactics_Types.goal_env g  in
           let uu____11774 = FStar_Tactics_Types.goal_type g  in
           new_uvar "dup" uu____11773 uu____11774  in
         bind uu____11766
           (fun uu____11784  ->
              match uu____11784 with
              | (u,u_uvar) ->
                  let g' =
                    let uu___1630_11794 = g  in
                    {
                      FStar_Tactics_Types.goal_main_env =
                        (uu___1630_11794.FStar_Tactics_Types.goal_main_env);
                      FStar_Tactics_Types.goal_ctx_uvar = u_uvar;
                      FStar_Tactics_Types.opts =
                        (uu___1630_11794.FStar_Tactics_Types.opts);
                      FStar_Tactics_Types.is_guard =
                        (uu___1630_11794.FStar_Tactics_Types.is_guard);
                      FStar_Tactics_Types.label =
                        (uu___1630_11794.FStar_Tactics_Types.label)
                    }  in
                  bind __dismiss
                    (fun uu____11797  ->
                       let uu____11798 =
                         let uu____11801 = FStar_Tactics_Types.goal_env g  in
                         let uu____11802 =
                           let uu____11803 =
                             let uu____11804 = FStar_Tactics_Types.goal_env g
                                in
                             let uu____11805 =
                               FStar_Tactics_Types.goal_type g  in
                             FStar_TypeChecker_TcTerm.universe_of uu____11804
                               uu____11805
                              in
                           let uu____11806 = FStar_Tactics_Types.goal_type g
                              in
                           let uu____11807 =
                             FStar_Tactics_Types.goal_witness g  in
                           FStar_Syntax_Util.mk_eq2 uu____11803 uu____11806 u
                             uu____11807
                            in
                         add_irrelevant_goal "dup equation" uu____11801
                           uu____11802 g.FStar_Tactics_Types.opts
                           g.FStar_Tactics_Types.label
                          in
                       bind uu____11798
                         (fun uu____11811  ->
                            let uu____11812 = add_goals [g']  in
                            bind uu____11812 (fun uu____11816  -> ret ())))))
  
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
              let uu____11942 = f x y  in
              if uu____11942 then aux (x :: acc) xs ys else (acc, xs, ys)
          | uu____11965 -> (acc, l11, l21)  in
        let uu____11980 = aux [] l1 l2  in
        match uu____11980 with | (pr,t1,t2) -> ((FStar_List.rev pr), t1, t2)
  
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
      let uu____12086 = get_phi g1  in
      match uu____12086 with
      | FStar_Pervasives_Native.None  -> fail "goal 1 is not irrelevant"
      | FStar_Pervasives_Native.Some phi1 ->
          let uu____12093 = get_phi g2  in
          (match uu____12093 with
           | FStar_Pervasives_Native.None  -> fail "goal 2 is not irrelevant"
           | FStar_Pervasives_Native.Some phi2 ->
               let gamma1 =
                 (g1.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_gamma
                  in
               let gamma2 =
                 (g2.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_gamma
                  in
               let uu____12106 =
                 longest_prefix FStar_Syntax_Syntax.eq_binding
                   (FStar_List.rev gamma1) (FStar_List.rev gamma2)
                  in
               (match uu____12106 with
                | (gamma,r1,r2) ->
                    let t1 =
                      let uu____12137 =
                        FStar_TypeChecker_Env.binders_of_bindings
                          (FStar_List.rev r1)
                         in
                      close_forall_no_univs1 uu____12137 phi1  in
                    let t2 =
                      let uu____12147 =
                        FStar_TypeChecker_Env.binders_of_bindings
                          (FStar_List.rev r2)
                         in
                      close_forall_no_univs1 uu____12147 phi2  in
                    let uu____12156 =
                      set_solution g1 FStar_Syntax_Util.exp_unit  in
                    bind uu____12156
                      (fun uu____12161  ->
                         let uu____12162 =
                           set_solution g2 FStar_Syntax_Util.exp_unit  in
                         bind uu____12162
                           (fun uu____12169  ->
                              let ng = FStar_Syntax_Util.mk_conj t1 t2  in
                              let nenv =
                                let uu___1681_12174 =
                                  FStar_Tactics_Types.goal_env g1  in
                                let uu____12175 =
                                  FStar_Util.smap_create (Prims.of_int (100))
                                   in
                                {
                                  FStar_TypeChecker_Env.solver =
                                    (uu___1681_12174.FStar_TypeChecker_Env.solver);
                                  FStar_TypeChecker_Env.range =
                                    (uu___1681_12174.FStar_TypeChecker_Env.range);
                                  FStar_TypeChecker_Env.curmodule =
                                    (uu___1681_12174.FStar_TypeChecker_Env.curmodule);
                                  FStar_TypeChecker_Env.gamma =
                                    (FStar_List.rev gamma);
                                  FStar_TypeChecker_Env.gamma_sig =
                                    (uu___1681_12174.FStar_TypeChecker_Env.gamma_sig);
                                  FStar_TypeChecker_Env.gamma_cache =
                                    uu____12175;
                                  FStar_TypeChecker_Env.modules =
                                    (uu___1681_12174.FStar_TypeChecker_Env.modules);
                                  FStar_TypeChecker_Env.expected_typ =
                                    (uu___1681_12174.FStar_TypeChecker_Env.expected_typ);
                                  FStar_TypeChecker_Env.sigtab =
                                    (uu___1681_12174.FStar_TypeChecker_Env.sigtab);
                                  FStar_TypeChecker_Env.attrtab =
                                    (uu___1681_12174.FStar_TypeChecker_Env.attrtab);
                                  FStar_TypeChecker_Env.instantiate_imp =
                                    (uu___1681_12174.FStar_TypeChecker_Env.instantiate_imp);
                                  FStar_TypeChecker_Env.effects =
                                    (uu___1681_12174.FStar_TypeChecker_Env.effects);
                                  FStar_TypeChecker_Env.generalize =
                                    (uu___1681_12174.FStar_TypeChecker_Env.generalize);
                                  FStar_TypeChecker_Env.letrecs =
                                    (uu___1681_12174.FStar_TypeChecker_Env.letrecs);
                                  FStar_TypeChecker_Env.top_level =
                                    (uu___1681_12174.FStar_TypeChecker_Env.top_level);
                                  FStar_TypeChecker_Env.check_uvars =
                                    (uu___1681_12174.FStar_TypeChecker_Env.check_uvars);
                                  FStar_TypeChecker_Env.use_eq =
                                    (uu___1681_12174.FStar_TypeChecker_Env.use_eq);
                                  FStar_TypeChecker_Env.use_eq_strict =
                                    (uu___1681_12174.FStar_TypeChecker_Env.use_eq_strict);
                                  FStar_TypeChecker_Env.is_iface =
                                    (uu___1681_12174.FStar_TypeChecker_Env.is_iface);
                                  FStar_TypeChecker_Env.admit =
                                    (uu___1681_12174.FStar_TypeChecker_Env.admit);
                                  FStar_TypeChecker_Env.lax =
                                    (uu___1681_12174.FStar_TypeChecker_Env.lax);
                                  FStar_TypeChecker_Env.lax_universes =
                                    (uu___1681_12174.FStar_TypeChecker_Env.lax_universes);
                                  FStar_TypeChecker_Env.phase1 =
                                    (uu___1681_12174.FStar_TypeChecker_Env.phase1);
                                  FStar_TypeChecker_Env.failhard =
                                    (uu___1681_12174.FStar_TypeChecker_Env.failhard);
                                  FStar_TypeChecker_Env.nosynth =
                                    (uu___1681_12174.FStar_TypeChecker_Env.nosynth);
                                  FStar_TypeChecker_Env.uvar_subtyping =
                                    (uu___1681_12174.FStar_TypeChecker_Env.uvar_subtyping);
                                  FStar_TypeChecker_Env.tc_term =
                                    (uu___1681_12174.FStar_TypeChecker_Env.tc_term);
                                  FStar_TypeChecker_Env.type_of =
                                    (uu___1681_12174.FStar_TypeChecker_Env.type_of);
                                  FStar_TypeChecker_Env.universe_of =
                                    (uu___1681_12174.FStar_TypeChecker_Env.universe_of);
                                  FStar_TypeChecker_Env.check_type_of =
                                    (uu___1681_12174.FStar_TypeChecker_Env.check_type_of);
                                  FStar_TypeChecker_Env.use_bv_sorts =
                                    (uu___1681_12174.FStar_TypeChecker_Env.use_bv_sorts);
                                  FStar_TypeChecker_Env.qtbl_name_and_index =
                                    (uu___1681_12174.FStar_TypeChecker_Env.qtbl_name_and_index);
                                  FStar_TypeChecker_Env.normalized_eff_names
                                    =
                                    (uu___1681_12174.FStar_TypeChecker_Env.normalized_eff_names);
                                  FStar_TypeChecker_Env.fv_delta_depths =
                                    (uu___1681_12174.FStar_TypeChecker_Env.fv_delta_depths);
                                  FStar_TypeChecker_Env.proof_ns =
                                    (uu___1681_12174.FStar_TypeChecker_Env.proof_ns);
                                  FStar_TypeChecker_Env.synth_hook =
                                    (uu___1681_12174.FStar_TypeChecker_Env.synth_hook);
                                  FStar_TypeChecker_Env.try_solve_implicits_hook
                                    =
                                    (uu___1681_12174.FStar_TypeChecker_Env.try_solve_implicits_hook);
                                  FStar_TypeChecker_Env.splice =
                                    (uu___1681_12174.FStar_TypeChecker_Env.splice);
                                  FStar_TypeChecker_Env.mpreprocess =
                                    (uu___1681_12174.FStar_TypeChecker_Env.mpreprocess);
                                  FStar_TypeChecker_Env.postprocess =
                                    (uu___1681_12174.FStar_TypeChecker_Env.postprocess);
                                  FStar_TypeChecker_Env.is_native_tactic =
                                    (uu___1681_12174.FStar_TypeChecker_Env.is_native_tactic);
                                  FStar_TypeChecker_Env.identifier_info =
                                    (uu___1681_12174.FStar_TypeChecker_Env.identifier_info);
                                  FStar_TypeChecker_Env.tc_hooks =
                                    (uu___1681_12174.FStar_TypeChecker_Env.tc_hooks);
                                  FStar_TypeChecker_Env.dsenv =
                                    (uu___1681_12174.FStar_TypeChecker_Env.dsenv);
                                  FStar_TypeChecker_Env.nbe =
                                    (uu___1681_12174.FStar_TypeChecker_Env.nbe);
                                  FStar_TypeChecker_Env.strict_args_tab =
                                    (uu___1681_12174.FStar_TypeChecker_Env.strict_args_tab);
                                  FStar_TypeChecker_Env.erasable_types_tab =
                                    (uu___1681_12174.FStar_TypeChecker_Env.erasable_types_tab)
                                }  in
                              let uu____12179 =
                                mk_irrelevant_goal "joined" nenv ng
                                  g1.FStar_Tactics_Types.opts
                                  g1.FStar_Tactics_Types.label
                                 in
                              bind uu____12179
                                (fun goal  ->
                                   mlog
                                     (fun uu____12189  ->
                                        let uu____12190 =
                                          goal_to_string_verbose g1  in
                                        let uu____12192 =
                                          goal_to_string_verbose g2  in
                                        let uu____12194 =
                                          goal_to_string_verbose goal  in
                                        FStar_Util.print3
                                          "join_goals of\n(%s)\nand\n(%s)\n= (%s)\n"
                                          uu____12190 uu____12192 uu____12194)
                                     (fun uu____12198  -> ret goal))))))
  
let (join : unit -> unit tac) =
  fun uu____12206  ->
    bind get
      (fun ps  ->
         match ps.FStar_Tactics_Types.goals with
         | g1::g2::gs ->
             let uu____12222 =
               set
                 (let uu___1696_12227 = ps  in
                  {
                    FStar_Tactics_Types.main_context =
                      (uu___1696_12227.FStar_Tactics_Types.main_context);
                    FStar_Tactics_Types.all_implicits =
                      (uu___1696_12227.FStar_Tactics_Types.all_implicits);
                    FStar_Tactics_Types.goals = gs;
                    FStar_Tactics_Types.smt_goals =
                      (uu___1696_12227.FStar_Tactics_Types.smt_goals);
                    FStar_Tactics_Types.depth =
                      (uu___1696_12227.FStar_Tactics_Types.depth);
                    FStar_Tactics_Types.__dump =
                      (uu___1696_12227.FStar_Tactics_Types.__dump);
                    FStar_Tactics_Types.psc =
                      (uu___1696_12227.FStar_Tactics_Types.psc);
                    FStar_Tactics_Types.entry_range =
                      (uu___1696_12227.FStar_Tactics_Types.entry_range);
                    FStar_Tactics_Types.guard_policy =
                      (uu___1696_12227.FStar_Tactics_Types.guard_policy);
                    FStar_Tactics_Types.freshness =
                      (uu___1696_12227.FStar_Tactics_Types.freshness);
                    FStar_Tactics_Types.tac_verb_dbg =
                      (uu___1696_12227.FStar_Tactics_Types.tac_verb_dbg);
                    FStar_Tactics_Types.local_state =
                      (uu___1696_12227.FStar_Tactics_Types.local_state)
                  })
                in
             bind uu____12222
               (fun uu____12230  ->
                  let uu____12231 = join_goals g1 g2  in
                  bind uu____12231 (fun g12  -> add_goals [g12]))
         | uu____12236 -> fail "join: less than 2 goals")
  
let (set_options : Prims.string -> unit tac) =
  fun s  ->
    let uu____12252 =
      let uu____12255 = cur_goal ()  in
      bind uu____12255
        (fun g  ->
           FStar_Options.push ();
           (let uu____12268 = FStar_Util.smap_copy g.FStar_Tactics_Types.opts
               in
            FStar_Options.set uu____12268);
           (let res = FStar_Options.set_options s  in
            let opts' = FStar_Options.peek ()  in
            FStar_Options.pop ();
            (match res with
             | FStar_Getopt.Success  ->
                 let g' =
                   let uu___1707_12275 = g  in
                   {
                     FStar_Tactics_Types.goal_main_env =
                       (uu___1707_12275.FStar_Tactics_Types.goal_main_env);
                     FStar_Tactics_Types.goal_ctx_uvar =
                       (uu___1707_12275.FStar_Tactics_Types.goal_ctx_uvar);
                     FStar_Tactics_Types.opts = opts';
                     FStar_Tactics_Types.is_guard =
                       (uu___1707_12275.FStar_Tactics_Types.is_guard);
                     FStar_Tactics_Types.label =
                       (uu___1707_12275.FStar_Tactics_Types.label)
                   }  in
                 replace_cur g'
             | FStar_Getopt.Error err ->
                 fail2 "Setting options `%s` failed: %s" s err
             | FStar_Getopt.Help  ->
                 fail1 "Setting options `%s` failed (got `Help`?)" s)))
       in
    FStar_All.pipe_left (wrap_err "set_options") uu____12252
  
let (top_env : unit -> env tac) =
  fun uu____12292  ->
    bind get
      (fun ps  -> FStar_All.pipe_left ret ps.FStar_Tactics_Types.main_context)
  
let (lax_on : unit -> Prims.bool tac) =
  fun uu____12307  ->
    let uu____12311 = cur_goal ()  in
    bind uu____12311
      (fun g  ->
         let uu____12318 =
           (FStar_Options.lax ()) ||
             (let uu____12321 = FStar_Tactics_Types.goal_env g  in
              uu____12321.FStar_TypeChecker_Env.lax)
            in
         ret uu____12318)
  
let (unquote :
  FStar_Reflection_Data.typ ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term tac)
  =
  fun ty  ->
    fun tm  ->
      let uu____12338 =
        mlog
          (fun uu____12343  ->
             let uu____12344 = FStar_Syntax_Print.term_to_string tm  in
             FStar_Util.print1 "unquote: tm = %s\n" uu____12344)
          (fun uu____12349  ->
             let uu____12350 = cur_goal ()  in
             bind uu____12350
               (fun goal  ->
                  let env =
                    let uu____12358 = FStar_Tactics_Types.goal_env goal  in
                    FStar_TypeChecker_Env.set_expected_typ uu____12358 ty  in
                  let uu____12359 = __tc_ghost env tm  in
                  bind uu____12359
                    (fun uu____12378  ->
                       match uu____12378 with
                       | (tm1,typ,guard) ->
                           mlog
                             (fun uu____12392  ->
                                let uu____12393 =
                                  FStar_Syntax_Print.term_to_string tm1  in
                                FStar_Util.print1 "unquote: tm' = %s\n"
                                  uu____12393)
                             (fun uu____12397  ->
                                mlog
                                  (fun uu____12400  ->
                                     let uu____12401 =
                                       FStar_Syntax_Print.term_to_string typ
                                        in
                                     FStar_Util.print1 "unquote: typ = %s\n"
                                       uu____12401)
                                  (fun uu____12406  ->
                                     let uu____12407 =
                                       proc_guard "unquote" env guard  in
                                     bind uu____12407
                                       (fun uu____12412  -> ret tm1))))))
         in
      FStar_All.pipe_left (wrap_err "unquote") uu____12338
  
let (uvar_env :
  env ->
    FStar_Reflection_Data.typ FStar_Pervasives_Native.option ->
      FStar_Syntax_Syntax.term tac)
  =
  fun env  ->
    fun ty  ->
      let uu____12437 =
        match ty with
        | FStar_Pervasives_Native.Some ty1 -> ret ty1
        | FStar_Pervasives_Native.None  ->
            let uu____12443 =
              let uu____12450 =
                let uu____12451 = FStar_Syntax_Util.type_u ()  in
                FStar_All.pipe_left FStar_Pervasives_Native.fst uu____12451
                 in
              new_uvar "uvar_env.2" env uu____12450  in
            bind uu____12443
              (fun uu____12468  ->
                 match uu____12468 with | (typ,uvar_typ) -> ret typ)
         in
      bind uu____12437
        (fun typ  ->
           let uu____12480 = new_uvar "uvar_env" env typ  in
           bind uu____12480
             (fun uu____12495  ->
                match uu____12495 with | (t,uvar_t) -> ret t))
  
let (unshelve : FStar_Syntax_Syntax.term -> unit tac) =
  fun t  ->
    let uu____12514 =
      bind get
        (fun ps  ->
           let env = ps.FStar_Tactics_Types.main_context  in
           let opts =
             match ps.FStar_Tactics_Types.goals with
             | g::uu____12533 -> g.FStar_Tactics_Types.opts
             | uu____12536 -> FStar_Options.peek ()  in
           let uu____12539 = FStar_Syntax_Util.head_and_args t  in
           match uu____12539 with
           | ({
                FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                  (ctx_uvar,uu____12559);
                FStar_Syntax_Syntax.pos = uu____12560;
                FStar_Syntax_Syntax.vars = uu____12561;_},uu____12562)
               ->
               let env1 =
                 let uu___1761_12604 = env  in
                 {
                   FStar_TypeChecker_Env.solver =
                     (uu___1761_12604.FStar_TypeChecker_Env.solver);
                   FStar_TypeChecker_Env.range =
                     (uu___1761_12604.FStar_TypeChecker_Env.range);
                   FStar_TypeChecker_Env.curmodule =
                     (uu___1761_12604.FStar_TypeChecker_Env.curmodule);
                   FStar_TypeChecker_Env.gamma =
                     (ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_gamma);
                   FStar_TypeChecker_Env.gamma_sig =
                     (uu___1761_12604.FStar_TypeChecker_Env.gamma_sig);
                   FStar_TypeChecker_Env.gamma_cache =
                     (uu___1761_12604.FStar_TypeChecker_Env.gamma_cache);
                   FStar_TypeChecker_Env.modules =
                     (uu___1761_12604.FStar_TypeChecker_Env.modules);
                   FStar_TypeChecker_Env.expected_typ =
                     (uu___1761_12604.FStar_TypeChecker_Env.expected_typ);
                   FStar_TypeChecker_Env.sigtab =
                     (uu___1761_12604.FStar_TypeChecker_Env.sigtab);
                   FStar_TypeChecker_Env.attrtab =
                     (uu___1761_12604.FStar_TypeChecker_Env.attrtab);
                   FStar_TypeChecker_Env.instantiate_imp =
                     (uu___1761_12604.FStar_TypeChecker_Env.instantiate_imp);
                   FStar_TypeChecker_Env.effects =
                     (uu___1761_12604.FStar_TypeChecker_Env.effects);
                   FStar_TypeChecker_Env.generalize =
                     (uu___1761_12604.FStar_TypeChecker_Env.generalize);
                   FStar_TypeChecker_Env.letrecs =
                     (uu___1761_12604.FStar_TypeChecker_Env.letrecs);
                   FStar_TypeChecker_Env.top_level =
                     (uu___1761_12604.FStar_TypeChecker_Env.top_level);
                   FStar_TypeChecker_Env.check_uvars =
                     (uu___1761_12604.FStar_TypeChecker_Env.check_uvars);
                   FStar_TypeChecker_Env.use_eq =
                     (uu___1761_12604.FStar_TypeChecker_Env.use_eq);
                   FStar_TypeChecker_Env.use_eq_strict =
                     (uu___1761_12604.FStar_TypeChecker_Env.use_eq_strict);
                   FStar_TypeChecker_Env.is_iface =
                     (uu___1761_12604.FStar_TypeChecker_Env.is_iface);
                   FStar_TypeChecker_Env.admit =
                     (uu___1761_12604.FStar_TypeChecker_Env.admit);
                   FStar_TypeChecker_Env.lax =
                     (uu___1761_12604.FStar_TypeChecker_Env.lax);
                   FStar_TypeChecker_Env.lax_universes =
                     (uu___1761_12604.FStar_TypeChecker_Env.lax_universes);
                   FStar_TypeChecker_Env.phase1 =
                     (uu___1761_12604.FStar_TypeChecker_Env.phase1);
                   FStar_TypeChecker_Env.failhard =
                     (uu___1761_12604.FStar_TypeChecker_Env.failhard);
                   FStar_TypeChecker_Env.nosynth =
                     (uu___1761_12604.FStar_TypeChecker_Env.nosynth);
                   FStar_TypeChecker_Env.uvar_subtyping =
                     (uu___1761_12604.FStar_TypeChecker_Env.uvar_subtyping);
                   FStar_TypeChecker_Env.tc_term =
                     (uu___1761_12604.FStar_TypeChecker_Env.tc_term);
                   FStar_TypeChecker_Env.type_of =
                     (uu___1761_12604.FStar_TypeChecker_Env.type_of);
                   FStar_TypeChecker_Env.universe_of =
                     (uu___1761_12604.FStar_TypeChecker_Env.universe_of);
                   FStar_TypeChecker_Env.check_type_of =
                     (uu___1761_12604.FStar_TypeChecker_Env.check_type_of);
                   FStar_TypeChecker_Env.use_bv_sorts =
                     (uu___1761_12604.FStar_TypeChecker_Env.use_bv_sorts);
                   FStar_TypeChecker_Env.qtbl_name_and_index =
                     (uu___1761_12604.FStar_TypeChecker_Env.qtbl_name_and_index);
                   FStar_TypeChecker_Env.normalized_eff_names =
                     (uu___1761_12604.FStar_TypeChecker_Env.normalized_eff_names);
                   FStar_TypeChecker_Env.fv_delta_depths =
                     (uu___1761_12604.FStar_TypeChecker_Env.fv_delta_depths);
                   FStar_TypeChecker_Env.proof_ns =
                     (uu___1761_12604.FStar_TypeChecker_Env.proof_ns);
                   FStar_TypeChecker_Env.synth_hook =
                     (uu___1761_12604.FStar_TypeChecker_Env.synth_hook);
                   FStar_TypeChecker_Env.try_solve_implicits_hook =
                     (uu___1761_12604.FStar_TypeChecker_Env.try_solve_implicits_hook);
                   FStar_TypeChecker_Env.splice =
                     (uu___1761_12604.FStar_TypeChecker_Env.splice);
                   FStar_TypeChecker_Env.mpreprocess =
                     (uu___1761_12604.FStar_TypeChecker_Env.mpreprocess);
                   FStar_TypeChecker_Env.postprocess =
                     (uu___1761_12604.FStar_TypeChecker_Env.postprocess);
                   FStar_TypeChecker_Env.is_native_tactic =
                     (uu___1761_12604.FStar_TypeChecker_Env.is_native_tactic);
                   FStar_TypeChecker_Env.identifier_info =
                     (uu___1761_12604.FStar_TypeChecker_Env.identifier_info);
                   FStar_TypeChecker_Env.tc_hooks =
                     (uu___1761_12604.FStar_TypeChecker_Env.tc_hooks);
                   FStar_TypeChecker_Env.dsenv =
                     (uu___1761_12604.FStar_TypeChecker_Env.dsenv);
                   FStar_TypeChecker_Env.nbe =
                     (uu___1761_12604.FStar_TypeChecker_Env.nbe);
                   FStar_TypeChecker_Env.strict_args_tab =
                     (uu___1761_12604.FStar_TypeChecker_Env.strict_args_tab);
                   FStar_TypeChecker_Env.erasable_types_tab =
                     (uu___1761_12604.FStar_TypeChecker_Env.erasable_types_tab)
                 }  in
               let g =
                 FStar_Tactics_Types.mk_goal env1 ctx_uvar opts false ""  in
               let uu____12608 =
                 let uu____12611 = bnorm_goal g  in [uu____12611]  in
               add_goals uu____12608
           | uu____12612 -> fail "not a uvar")
       in
    FStar_All.pipe_left (wrap_err "unshelve") uu____12514
  
let (tac_and : Prims.bool tac -> Prims.bool tac -> Prims.bool tac) =
  fun t1  ->
    fun t2  ->
      let comp =
        bind t1
          (fun b  ->
             let uu____12674 = if b then t2 else ret false  in
             bind uu____12674 (fun b'  -> if b' then ret b' else fail ""))
         in
      let uu____12700 = trytac comp  in
      bind uu____12700
        (fun uu___6_12712  ->
           match uu___6_12712 with
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
        let uu____12754 =
          bind get
            (fun ps  ->
               let uu____12762 = __tc e t1  in
               bind uu____12762
                 (fun uu____12783  ->
                    match uu____12783 with
                    | (t11,ty1,g1) ->
                        let uu____12796 = __tc e t2  in
                        bind uu____12796
                          (fun uu____12817  ->
                             match uu____12817 with
                             | (t21,ty2,g2) ->
                                 let uu____12830 =
                                   proc_guard "unify_env g1" e g1  in
                                 bind uu____12830
                                   (fun uu____12837  ->
                                      let uu____12838 =
                                        proc_guard "unify_env g2" e g2  in
                                      bind uu____12838
                                        (fun uu____12846  ->
                                           let uu____12847 =
                                             do_unify e ty1 ty2  in
                                           let uu____12851 =
                                             do_unify e t11 t21  in
                                           tac_and uu____12847 uu____12851)))))
           in
        FStar_All.pipe_left (wrap_err "unify_env") uu____12754
  
let (launch_process :
  Prims.string -> Prims.string Prims.list -> Prims.string -> Prims.string tac)
  =
  fun prog  ->
    fun args  ->
      fun input  ->
        bind idtac
          (fun uu____12899  ->
             let uu____12900 = FStar_Options.unsafe_tactic_exec ()  in
             if uu____12900
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
        (fun uu____12934  ->
           let uu____12935 =
             FStar_Syntax_Syntax.gen_bv nm FStar_Pervasives_Native.None t  in
           ret uu____12935)
  
let (change : FStar_Reflection_Data.typ -> unit tac) =
  fun ty  ->
    let uu____12946 =
      mlog
        (fun uu____12951  ->
           let uu____12952 = FStar_Syntax_Print.term_to_string ty  in
           FStar_Util.print1 "change: ty = %s\n" uu____12952)
        (fun uu____12957  ->
           let uu____12958 = cur_goal ()  in
           bind uu____12958
             (fun g  ->
                let uu____12964 =
                  let uu____12973 = FStar_Tactics_Types.goal_env g  in
                  __tc uu____12973 ty  in
                bind uu____12964
                  (fun uu____12985  ->
                     match uu____12985 with
                     | (ty1,uu____12995,guard) ->
                         let uu____12997 =
                           let uu____13000 = FStar_Tactics_Types.goal_env g
                              in
                           proc_guard "change" uu____13000 guard  in
                         bind uu____12997
                           (fun uu____13004  ->
                              let uu____13005 =
                                let uu____13009 =
                                  FStar_Tactics_Types.goal_env g  in
                                let uu____13010 =
                                  FStar_Tactics_Types.goal_type g  in
                                do_unify uu____13009 uu____13010 ty1  in
                              bind uu____13005
                                (fun bb  ->
                                   if bb
                                   then
                                     let uu____13019 =
                                       FStar_Tactics_Types.goal_with_type g
                                         ty1
                                        in
                                     replace_cur uu____13019
                                   else
                                     (let steps =
                                        [FStar_TypeChecker_Env.AllowUnboundUniverses;
                                        FStar_TypeChecker_Env.UnfoldUntil
                                          FStar_Syntax_Syntax.delta_constant;
                                        FStar_TypeChecker_Env.Primops]  in
                                      let ng =
                                        let uu____13026 =
                                          FStar_Tactics_Types.goal_env g  in
                                        let uu____13027 =
                                          FStar_Tactics_Types.goal_type g  in
                                        normalize steps uu____13026
                                          uu____13027
                                         in
                                      let nty =
                                        let uu____13029 =
                                          FStar_Tactics_Types.goal_env g  in
                                        normalize steps uu____13029 ty1  in
                                      let uu____13030 =
                                        let uu____13034 =
                                          FStar_Tactics_Types.goal_env g  in
                                        do_unify uu____13034 ng nty  in
                                      bind uu____13030
                                        (fun b  ->
                                           if b
                                           then
                                             let uu____13043 =
                                               FStar_Tactics_Types.goal_with_type
                                                 g ty1
                                                in
                                             replace_cur uu____13043
                                           else fail "not convertible")))))))
       in
    FStar_All.pipe_left (wrap_err "change") uu____12946
  
let failwhen : 'a . Prims.bool -> Prims.string -> (unit -> 'a tac) -> 'a tac
  = fun b  -> fun msg  -> fun k  -> if b then fail msg else k () 
let (t_destruct :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.fv * FStar_BigInt.t) Prims.list tac)
  =
  fun s_tm  ->
    let uu____13117 =
      let uu____13126 = cur_goal ()  in
      bind uu____13126
        (fun g  ->
           let uu____13138 =
             let uu____13147 = FStar_Tactics_Types.goal_env g  in
             __tc uu____13147 s_tm  in
           bind uu____13138
             (fun uu____13165  ->
                match uu____13165 with
                | (s_tm1,s_ty,guard) ->
                    let uu____13183 =
                      let uu____13186 = FStar_Tactics_Types.goal_env g  in
                      proc_guard "destruct" uu____13186 guard  in
                    bind uu____13183
                      (fun uu____13200  ->
                         let s_ty1 =
                           let uu____13202 = FStar_Tactics_Types.goal_env g
                              in
                           FStar_TypeChecker_Normalize.normalize
                             [FStar_TypeChecker_Env.UnfoldTac;
                             FStar_TypeChecker_Env.Weak;
                             FStar_TypeChecker_Env.HNF;
                             FStar_TypeChecker_Env.UnfoldUntil
                               FStar_Syntax_Syntax.delta_constant]
                             uu____13202 s_ty
                            in
                         let uu____13203 =
                           FStar_Syntax_Util.head_and_args' s_ty1  in
                         match uu____13203 with
                         | (h,args) ->
                             let uu____13248 =
                               let uu____13255 =
                                 let uu____13256 =
                                   FStar_Syntax_Subst.compress h  in
                                 uu____13256.FStar_Syntax_Syntax.n  in
                               match uu____13255 with
                               | FStar_Syntax_Syntax.Tm_fvar fv ->
                                   ret (fv, [])
                               | FStar_Syntax_Syntax.Tm_uinst
                                   ({
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.Tm_fvar fv;
                                      FStar_Syntax_Syntax.pos = uu____13271;
                                      FStar_Syntax_Syntax.vars = uu____13272;_},us)
                                   -> ret (fv, us)
                               | uu____13282 -> fail "type is not an fv"  in
                             bind uu____13248
                               (fun uu____13303  ->
                                  match uu____13303 with
                                  | (fv,a_us) ->
                                      let t_lid =
                                        FStar_Syntax_Syntax.lid_of_fv fv  in
                                      let uu____13319 =
                                        let uu____13322 =
                                          FStar_Tactics_Types.goal_env g  in
                                        FStar_TypeChecker_Env.lookup_sigelt
                                          uu____13322 t_lid
                                         in
                                      (match uu____13319 with
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
                                                let uu____13363 =
                                                  erasable &&
                                                    (let uu____13366 =
                                                       is_irrelevant g  in
                                                     Prims.op_Negation
                                                       uu____13366)
                                                   in
                                                failwhen uu____13363
                                                  "cannot destruct erasable type to solve proof-relevant goal"
                                                  (fun uu____13376  ->
                                                     failwhen
                                                       ((FStar_List.length
                                                           a_us)
                                                          <>
                                                          (FStar_List.length
                                                             t_us))
                                                       "t_us don't match?"
                                                       (fun uu____13389  ->
                                                          let uu____13390 =
                                                            FStar_Syntax_Subst.open_term
                                                              t_ps t_ty
                                                             in
                                                          match uu____13390
                                                          with
                                                          | (t_ps1,t_ty1) ->
                                                              let uu____13405
                                                                =
                                                                mapM
                                                                  (fun c_lid 
                                                                    ->
                                                                    let uu____13433
                                                                    =
                                                                    let uu____13436
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    g  in
                                                                    FStar_TypeChecker_Env.lookup_sigelt
                                                                    uu____13436
                                                                    c_lid  in
                                                                    match uu____13433
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
                                                                    uu____13513
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
                                                                    let uu____13518
                                                                    =
                                                                    FStar_TypeChecker_Env.inst_tscheme
                                                                    (c_us,
                                                                    c_ty1)
                                                                     in
                                                                    match uu____13518
                                                                    with
                                                                    | 
                                                                    (c_us1,c_ty2)
                                                                    ->
                                                                    let uu____13541
                                                                    =
                                                                    FStar_Syntax_Util.arrow_formals_comp
                                                                    c_ty2  in
                                                                    (match uu____13541
                                                                    with
                                                                    | 
                                                                    (bs,comp)
                                                                    ->
                                                                    let uu____13560
                                                                    =
                                                                    let rename_bv
                                                                    bv =
                                                                    let ppname
                                                                    =
                                                                    bv.FStar_Syntax_Syntax.ppname
                                                                     in
                                                                    let ppname1
                                                                    =
                                                                    let uu___1888_13583
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
                                                                    (uu___1888_13583.FStar_Ident.idRange)
                                                                    }  in
                                                                    FStar_Syntax_Syntax.freshen_bv
                                                                    (let uu___1891_13587
                                                                    = bv  in
                                                                    {
                                                                    FStar_Syntax_Syntax.ppname
                                                                    = ppname1;
                                                                    FStar_Syntax_Syntax.index
                                                                    =
                                                                    (uu___1891_13587.FStar_Syntax_Syntax.index);
                                                                    FStar_Syntax_Syntax.sort
                                                                    =
                                                                    (uu___1891_13587.FStar_Syntax_Syntax.sort)
                                                                    })  in
                                                                    let bs' =
                                                                    FStar_List.map
                                                                    (fun
                                                                    uu____13613
                                                                     ->
                                                                    match uu____13613
                                                                    with
                                                                    | 
                                                                    (bv,aq)
                                                                    ->
                                                                    let uu____13632
                                                                    =
                                                                    rename_bv
                                                                    bv  in
                                                                    (uu____13632,
                                                                    aq)) bs
                                                                     in
                                                                    let subst1
                                                                    =
                                                                    FStar_List.map2
                                                                    (fun
                                                                    uu____13657
                                                                     ->
                                                                    fun
                                                                    uu____13658
                                                                     ->
                                                                    match 
                                                                    (uu____13657,
                                                                    uu____13658)
                                                                    with
                                                                    | 
                                                                    ((bv,uu____13684),
                                                                    (bv',uu____13686))
                                                                    ->
                                                                    let uu____13707
                                                                    =
                                                                    let uu____13714
                                                                    =
                                                                    FStar_Syntax_Syntax.bv_to_name
                                                                    bv'  in
                                                                    (bv,
                                                                    uu____13714)
                                                                     in
                                                                    FStar_Syntax_Syntax.NT
                                                                    uu____13707)
                                                                    bs bs'
                                                                     in
                                                                    let uu____13719
                                                                    =
                                                                    FStar_Syntax_Subst.subst_binders
                                                                    subst1
                                                                    bs'  in
                                                                    let uu____13728
                                                                    =
                                                                    FStar_Syntax_Subst.subst_comp
                                                                    subst1
                                                                    comp  in
                                                                    (uu____13719,
                                                                    uu____13728)
                                                                     in
                                                                    (match uu____13560
                                                                    with
                                                                    | 
                                                                    (bs1,comp1)
                                                                    ->
                                                                    let uu____13775
                                                                    =
                                                                    FStar_List.splitAt
                                                                    nparam
                                                                    bs1  in
                                                                    (match uu____13775
                                                                    with
                                                                    | 
                                                                    (d_ps,bs2)
                                                                    ->
                                                                    let uu____13848
                                                                    =
                                                                    let uu____13850
                                                                    =
                                                                    FStar_Syntax_Util.is_total_comp
                                                                    comp1  in
                                                                    Prims.op_Negation
                                                                    uu____13850
                                                                     in
                                                                    failwhen
                                                                    uu____13848
                                                                    "not total?"
                                                                    (fun
                                                                    uu____13869
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
                                                                    uu___7_13886
                                                                    =
                                                                    match uu___7_13886
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    (FStar_Syntax_Syntax.Implicit
                                                                    uu____13890)
                                                                    -> true
                                                                    | 
                                                                    uu____13893
                                                                    -> false
                                                                     in
                                                                    let uu____13897
                                                                    =
                                                                    FStar_List.splitAt
                                                                    nparam
                                                                    args  in
                                                                    match uu____13897
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
                                                                    uu____14033
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
                                                                    uu____14095
                                                                     ->
                                                                    match uu____14095
                                                                    with
                                                                    | 
                                                                    ((bv,uu____14115),
                                                                    (t,uu____14117))
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
                                                                    uu____14187
                                                                     ->
                                                                    match uu____14187
                                                                    with
                                                                    | 
                                                                    ((bv,uu____14214),
                                                                    (t,uu____14216))
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
                                                                    uu____14275
                                                                     ->
                                                                    match uu____14275
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
                                                                    let uu____14330
                                                                    =
                                                                    FStar_TypeChecker_TcTerm.tc_pat
                                                                    (let uu___1950_14354
                                                                    = env  in
                                                                    {
                                                                    FStar_TypeChecker_Env.solver
                                                                    =
                                                                    (uu___1950_14354.FStar_TypeChecker_Env.solver);
                                                                    FStar_TypeChecker_Env.range
                                                                    =
                                                                    (uu___1950_14354.FStar_TypeChecker_Env.range);
                                                                    FStar_TypeChecker_Env.curmodule
                                                                    =
                                                                    (uu___1950_14354.FStar_TypeChecker_Env.curmodule);
                                                                    FStar_TypeChecker_Env.gamma
                                                                    =
                                                                    (uu___1950_14354.FStar_TypeChecker_Env.gamma);
                                                                    FStar_TypeChecker_Env.gamma_sig
                                                                    =
                                                                    (uu___1950_14354.FStar_TypeChecker_Env.gamma_sig);
                                                                    FStar_TypeChecker_Env.gamma_cache
                                                                    =
                                                                    (uu___1950_14354.FStar_TypeChecker_Env.gamma_cache);
                                                                    FStar_TypeChecker_Env.modules
                                                                    =
                                                                    (uu___1950_14354.FStar_TypeChecker_Env.modules);
                                                                    FStar_TypeChecker_Env.expected_typ
                                                                    =
                                                                    (uu___1950_14354.FStar_TypeChecker_Env.expected_typ);
                                                                    FStar_TypeChecker_Env.sigtab
                                                                    =
                                                                    (uu___1950_14354.FStar_TypeChecker_Env.sigtab);
                                                                    FStar_TypeChecker_Env.attrtab
                                                                    =
                                                                    (uu___1950_14354.FStar_TypeChecker_Env.attrtab);
                                                                    FStar_TypeChecker_Env.instantiate_imp
                                                                    =
                                                                    (uu___1950_14354.FStar_TypeChecker_Env.instantiate_imp);
                                                                    FStar_TypeChecker_Env.effects
                                                                    =
                                                                    (uu___1950_14354.FStar_TypeChecker_Env.effects);
                                                                    FStar_TypeChecker_Env.generalize
                                                                    =
                                                                    (uu___1950_14354.FStar_TypeChecker_Env.generalize);
                                                                    FStar_TypeChecker_Env.letrecs
                                                                    =
                                                                    (uu___1950_14354.FStar_TypeChecker_Env.letrecs);
                                                                    FStar_TypeChecker_Env.top_level
                                                                    =
                                                                    (uu___1950_14354.FStar_TypeChecker_Env.top_level);
                                                                    FStar_TypeChecker_Env.check_uvars
                                                                    =
                                                                    (uu___1950_14354.FStar_TypeChecker_Env.check_uvars);
                                                                    FStar_TypeChecker_Env.use_eq
                                                                    =
                                                                    (uu___1950_14354.FStar_TypeChecker_Env.use_eq);
                                                                    FStar_TypeChecker_Env.use_eq_strict
                                                                    =
                                                                    (uu___1950_14354.FStar_TypeChecker_Env.use_eq_strict);
                                                                    FStar_TypeChecker_Env.is_iface
                                                                    =
                                                                    (uu___1950_14354.FStar_TypeChecker_Env.is_iface);
                                                                    FStar_TypeChecker_Env.admit
                                                                    =
                                                                    (uu___1950_14354.FStar_TypeChecker_Env.admit);
                                                                    FStar_TypeChecker_Env.lax
                                                                    = true;
                                                                    FStar_TypeChecker_Env.lax_universes
                                                                    =
                                                                    (uu___1950_14354.FStar_TypeChecker_Env.lax_universes);
                                                                    FStar_TypeChecker_Env.phase1
                                                                    =
                                                                    (uu___1950_14354.FStar_TypeChecker_Env.phase1);
                                                                    FStar_TypeChecker_Env.failhard
                                                                    =
                                                                    (uu___1950_14354.FStar_TypeChecker_Env.failhard);
                                                                    FStar_TypeChecker_Env.nosynth
                                                                    =
                                                                    (uu___1950_14354.FStar_TypeChecker_Env.nosynth);
                                                                    FStar_TypeChecker_Env.uvar_subtyping
                                                                    =
                                                                    (uu___1950_14354.FStar_TypeChecker_Env.uvar_subtyping);
                                                                    FStar_TypeChecker_Env.tc_term
                                                                    =
                                                                    (uu___1950_14354.FStar_TypeChecker_Env.tc_term);
                                                                    FStar_TypeChecker_Env.type_of
                                                                    =
                                                                    (uu___1950_14354.FStar_TypeChecker_Env.type_of);
                                                                    FStar_TypeChecker_Env.universe_of
                                                                    =
                                                                    (uu___1950_14354.FStar_TypeChecker_Env.universe_of);
                                                                    FStar_TypeChecker_Env.check_type_of
                                                                    =
                                                                    (uu___1950_14354.FStar_TypeChecker_Env.check_type_of);
                                                                    FStar_TypeChecker_Env.use_bv_sorts
                                                                    =
                                                                    (uu___1950_14354.FStar_TypeChecker_Env.use_bv_sorts);
                                                                    FStar_TypeChecker_Env.qtbl_name_and_index
                                                                    =
                                                                    (uu___1950_14354.FStar_TypeChecker_Env.qtbl_name_and_index);
                                                                    FStar_TypeChecker_Env.normalized_eff_names
                                                                    =
                                                                    (uu___1950_14354.FStar_TypeChecker_Env.normalized_eff_names);
                                                                    FStar_TypeChecker_Env.fv_delta_depths
                                                                    =
                                                                    (uu___1950_14354.FStar_TypeChecker_Env.fv_delta_depths);
                                                                    FStar_TypeChecker_Env.proof_ns
                                                                    =
                                                                    (uu___1950_14354.FStar_TypeChecker_Env.proof_ns);
                                                                    FStar_TypeChecker_Env.synth_hook
                                                                    =
                                                                    (uu___1950_14354.FStar_TypeChecker_Env.synth_hook);
                                                                    FStar_TypeChecker_Env.try_solve_implicits_hook
                                                                    =
                                                                    (uu___1950_14354.FStar_TypeChecker_Env.try_solve_implicits_hook);
                                                                    FStar_TypeChecker_Env.splice
                                                                    =
                                                                    (uu___1950_14354.FStar_TypeChecker_Env.splice);
                                                                    FStar_TypeChecker_Env.mpreprocess
                                                                    =
                                                                    (uu___1950_14354.FStar_TypeChecker_Env.mpreprocess);
                                                                    FStar_TypeChecker_Env.postprocess
                                                                    =
                                                                    (uu___1950_14354.FStar_TypeChecker_Env.postprocess);
                                                                    FStar_TypeChecker_Env.is_native_tactic
                                                                    =
                                                                    (uu___1950_14354.FStar_TypeChecker_Env.is_native_tactic);
                                                                    FStar_TypeChecker_Env.identifier_info
                                                                    =
                                                                    (uu___1950_14354.FStar_TypeChecker_Env.identifier_info);
                                                                    FStar_TypeChecker_Env.tc_hooks
                                                                    =
                                                                    (uu___1950_14354.FStar_TypeChecker_Env.tc_hooks);
                                                                    FStar_TypeChecker_Env.dsenv
                                                                    =
                                                                    (uu___1950_14354.FStar_TypeChecker_Env.dsenv);
                                                                    FStar_TypeChecker_Env.nbe
                                                                    =
                                                                    (uu___1950_14354.FStar_TypeChecker_Env.nbe);
                                                                    FStar_TypeChecker_Env.strict_args_tab
                                                                    =
                                                                    (uu___1950_14354.FStar_TypeChecker_Env.strict_args_tab);
                                                                    FStar_TypeChecker_Env.erasable_types_tab
                                                                    =
                                                                    (uu___1950_14354.FStar_TypeChecker_Env.erasable_types_tab)
                                                                    }) s_ty1
                                                                    pat  in
                                                                    match uu____14330
                                                                    with
                                                                    | 
                                                                    (uu____14368,uu____14369,uu____14370,uu____14371,pat_t,uu____14373,_guard_pat,_erasable)
                                                                    ->
                                                                    let eq_b
                                                                    =
                                                                    let uu____14387
                                                                    =
                                                                    let uu____14388
                                                                    =
                                                                    FStar_Syntax_Util.mk_eq2
                                                                    equ s_ty1
                                                                    s_tm1
                                                                    pat_t  in
                                                                    FStar_Syntax_Util.mk_squash
                                                                    equ
                                                                    uu____14388
                                                                     in
                                                                    FStar_Syntax_Syntax.gen_bv
                                                                    "breq"
                                                                    FStar_Pervasives_Native.None
                                                                    uu____14387
                                                                     in
                                                                    let cod1
                                                                    =
                                                                    let uu____14393
                                                                    =
                                                                    let uu____14402
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_binder
                                                                    eq_b  in
                                                                    [uu____14402]
                                                                     in
                                                                    let uu____14421
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Total
                                                                    cod  in
                                                                    FStar_Syntax_Util.arrow
                                                                    uu____14393
                                                                    uu____14421
                                                                     in
                                                                    let nty =
                                                                    let uu____14427
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Total
                                                                    cod1  in
                                                                    FStar_Syntax_Util.arrow
                                                                    bs3
                                                                    uu____14427
                                                                     in
                                                                    let uu____14430
                                                                    =
                                                                    new_uvar
                                                                    "destruct branch"
                                                                    env nty
                                                                     in
                                                                    bind
                                                                    uu____14430
                                                                    (fun
                                                                    uu____14460
                                                                     ->
                                                                    match uu____14460
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
                                                                    let uu____14487
                                                                    =
                                                                    let uu____14498
                                                                    =
                                                                    FStar_Syntax_Syntax.as_arg
                                                                    FStar_Syntax_Util.exp_unit
                                                                     in
                                                                    [uu____14498]
                                                                     in
                                                                    FStar_Syntax_Util.mk_app
                                                                    brt
                                                                    uu____14487
                                                                     in
                                                                    let br =
                                                                    FStar_Syntax_Subst.close_branch
                                                                    (pat,
                                                                    FStar_Pervasives_Native.None,
                                                                    brt1)  in
                                                                    let uu____14534
                                                                    =
                                                                    let uu____14545
                                                                    =
                                                                    let uu____14550
                                                                    =
                                                                    FStar_BigInt.of_int_fs
                                                                    (FStar_List.length
                                                                    bs3)  in
                                                                    (fv1,
                                                                    uu____14550)
                                                                     in
                                                                    (g', br,
                                                                    uu____14545)
                                                                     in
                                                                    ret
                                                                    uu____14534)))))))
                                                                    | 
                                                                    uu____14571
                                                                    ->
                                                                    fail
                                                                    "impossible: not a ctor"))
                                                                  c_lids
                                                                 in
                                                              bind
                                                                uu____13405
                                                                (fun goal_brs
                                                                    ->
                                                                   let uu____14621
                                                                    =
                                                                    FStar_List.unzip3
                                                                    goal_brs
                                                                     in
                                                                   match uu____14621
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
                                                                    let uu____14694
                                                                    =
                                                                    solve' g
                                                                    w  in
                                                                    bind
                                                                    uu____14694
                                                                    (fun
                                                                    uu____14705
                                                                     ->
                                                                    let uu____14706
                                                                    =
                                                                    add_goals
                                                                    goals  in
                                                                    bind
                                                                    uu____14706
                                                                    (fun
                                                                    uu____14716
                                                                     ->
                                                                    ret infos)))))
                                            | uu____14723 ->
                                                fail "not an inductive type"))))))
       in
    FStar_All.pipe_left (wrap_err "destruct") uu____13117
  
let rec last : 'a . 'a Prims.list -> 'a =
  fun l  ->
    match l with
    | [] -> failwith "last: empty list"
    | x::[] -> x
    | uu____14772::xs -> last xs
  
let rec init : 'a . 'a Prims.list -> 'a Prims.list =
  fun l  ->
    match l with
    | [] -> failwith "init: empty list"
    | x::[] -> []
    | x::xs -> let uu____14802 = init xs  in x :: uu____14802
  
let rec (inspect :
  FStar_Syntax_Syntax.term -> FStar_Reflection_Data.term_view tac) =
  fun t  ->
    let uu____14815 =
      let t1 = FStar_Syntax_Util.unascribe t  in
      let t2 = FStar_Syntax_Util.un_uinst t1  in
      let t3 = FStar_Syntax_Util.unlazy_emb t2  in
      match t3.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_meta (t4,uu____14824) -> inspect t4
      | FStar_Syntax_Syntax.Tm_name bv ->
          FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_Var bv)
      | FStar_Syntax_Syntax.Tm_bvar bv ->
          FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_BVar bv)
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_FVar fv)
      | FStar_Syntax_Syntax.Tm_app (hd1,[]) ->
          failwith "empty arguments on Tm_app"
      | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
          let uu____14890 = last args  in
          (match uu____14890 with
           | (a,q) ->
               let q' = FStar_Reflection_Basic.inspect_aqual q  in
               let uu____14920 =
                 let uu____14921 =
                   let uu____14926 =
                     let uu____14927 =
                       let uu____14932 = init args  in
                       FStar_Syntax_Syntax.mk_Tm_app hd1 uu____14932  in
                     uu____14927 FStar_Pervasives_Native.None
                       t3.FStar_Syntax_Syntax.pos
                      in
                   (uu____14926, (a, q'))  in
                 FStar_Reflection_Data.Tv_App uu____14921  in
               FStar_All.pipe_left ret uu____14920)
      | FStar_Syntax_Syntax.Tm_abs ([],uu____14943,uu____14944) ->
          failwith "empty arguments on Tm_abs"
      | FStar_Syntax_Syntax.Tm_abs (bs,t4,k) ->
          let uu____14997 = FStar_Syntax_Subst.open_term bs t4  in
          (match uu____14997 with
           | (bs1,t5) ->
               (match bs1 with
                | [] -> failwith "impossible"
                | b::bs2 ->
                    let uu____15039 =
                      let uu____15040 =
                        let uu____15045 = FStar_Syntax_Util.abs bs2 t5 k  in
                        (b, uu____15045)  in
                      FStar_Reflection_Data.Tv_Abs uu____15040  in
                    FStar_All.pipe_left ret uu____15039))
      | FStar_Syntax_Syntax.Tm_type uu____15048 ->
          FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_Type ())
      | FStar_Syntax_Syntax.Tm_arrow ([],k) ->
          failwith "empty binders on arrow"
      | FStar_Syntax_Syntax.Tm_arrow uu____15073 ->
          let uu____15088 = FStar_Syntax_Util.arrow_one t3  in
          (match uu____15088 with
           | FStar_Pervasives_Native.Some (b,c) ->
               FStar_All.pipe_left ret
                 (FStar_Reflection_Data.Tv_Arrow (b, c))
           | FStar_Pervasives_Native.None  -> failwith "impossible")
      | FStar_Syntax_Syntax.Tm_refine (bv,t4) ->
          let b = FStar_Syntax_Syntax.mk_binder bv  in
          let uu____15119 = FStar_Syntax_Subst.open_term [b] t4  in
          (match uu____15119 with
           | (b',t5) ->
               let b1 =
                 match b' with
                 | b'1::[] -> b'1
                 | uu____15172 -> failwith "impossible"  in
               FStar_All.pipe_left ret
                 (FStar_Reflection_Data.Tv_Refine
                    ((FStar_Pervasives_Native.fst b1), t5)))
      | FStar_Syntax_Syntax.Tm_constant c ->
          let uu____15185 =
            let uu____15186 = FStar_Reflection_Basic.inspect_const c  in
            FStar_Reflection_Data.Tv_Const uu____15186  in
          FStar_All.pipe_left ret uu____15185
      | FStar_Syntax_Syntax.Tm_uvar (ctx_u,s) ->
          let uu____15207 =
            let uu____15208 =
              let uu____15213 =
                let uu____15214 =
                  FStar_Syntax_Unionfind.uvar_id
                    ctx_u.FStar_Syntax_Syntax.ctx_uvar_head
                   in
                FStar_BigInt.of_int_fs uu____15214  in
              (uu____15213, (ctx_u, s))  in
            FStar_Reflection_Data.Tv_Uvar uu____15208  in
          FStar_All.pipe_left ret uu____15207
      | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),t21) ->
          if lb.FStar_Syntax_Syntax.lbunivs <> []
          then FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown
          else
            (match lb.FStar_Syntax_Syntax.lbname with
             | FStar_Util.Inr uu____15254 ->
                 FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown
             | FStar_Util.Inl bv ->
                 let b = FStar_Syntax_Syntax.mk_binder bv  in
                 let uu____15259 = FStar_Syntax_Subst.open_term [b] t21  in
                 (match uu____15259 with
                  | (bs,t22) ->
                      let b1 =
                        match bs with
                        | b1::[] -> b1
                        | uu____15312 ->
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
             | FStar_Util.Inr uu____15356 ->
                 FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown
             | FStar_Util.Inl bv ->
                 let uu____15360 = FStar_Syntax_Subst.open_let_rec [lb] t21
                    in
                 (match uu____15360 with
                  | (lbs,t22) ->
                      (match lbs with
                       | lb1::[] ->
                           (match lb1.FStar_Syntax_Syntax.lbname with
                            | FStar_Util.Inr uu____15380 ->
                                ret FStar_Reflection_Data.Tv_Unknown
                            | FStar_Util.Inl bv1 ->
                                FStar_All.pipe_left ret
                                  (FStar_Reflection_Data.Tv_Let
                                     (true,
                                       (lb1.FStar_Syntax_Syntax.lbattrs),
                                       bv1, (lb1.FStar_Syntax_Syntax.lbdef),
                                       t22)))
                       | uu____15388 ->
                           failwith
                             "impossible: open_term returned different amount of binders")))
      | FStar_Syntax_Syntax.Tm_match (t4,brs) ->
          let rec inspect_pat p =
            match p.FStar_Syntax_Syntax.v with
            | FStar_Syntax_Syntax.Pat_constant c ->
                let uu____15443 = FStar_Reflection_Basic.inspect_const c  in
                FStar_Reflection_Data.Pat_Constant uu____15443
            | FStar_Syntax_Syntax.Pat_cons (fv,ps) ->
                let uu____15464 =
                  let uu____15476 =
                    FStar_List.map
                      (fun uu____15500  ->
                         match uu____15500 with
                         | (p1,b) ->
                             let uu____15521 = inspect_pat p1  in
                             (uu____15521, b)) ps
                     in
                  (fv, uu____15476)  in
                FStar_Reflection_Data.Pat_Cons uu____15464
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
              (fun uu___8_15617  ->
                 match uu___8_15617 with
                 | (pat,uu____15639,t5) ->
                     let uu____15657 = inspect_pat pat  in (uu____15657, t5))
              brs1
             in
          FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_Match (t4, brs2))
      | FStar_Syntax_Syntax.Tm_unknown  ->
          FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown
      | uu____15666 ->
          ((let uu____15668 =
              let uu____15674 =
                let uu____15676 = FStar_Syntax_Print.tag_of_term t3  in
                let uu____15678 = FStar_Syntax_Print.term_to_string t3  in
                FStar_Util.format2
                  "inspect: outside of expected syntax (%s, %s)\n"
                  uu____15676 uu____15678
                 in
              (FStar_Errors.Warning_CantInspect, uu____15674)  in
            FStar_Errors.log_issue t3.FStar_Syntax_Syntax.pos uu____15668);
           FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown)
       in
    wrap_err "inspect" uu____14815
  
let (pack : FStar_Reflection_Data.term_view -> FStar_Syntax_Syntax.term tac)
  =
  fun tv  ->
    match tv with
    | FStar_Reflection_Data.Tv_Var bv ->
        let uu____15696 = FStar_Syntax_Syntax.bv_to_name bv  in
        FStar_All.pipe_left ret uu____15696
    | FStar_Reflection_Data.Tv_BVar bv ->
        let uu____15700 = FStar_Syntax_Syntax.bv_to_tm bv  in
        FStar_All.pipe_left ret uu____15700
    | FStar_Reflection_Data.Tv_FVar fv ->
        let uu____15704 = FStar_Syntax_Syntax.fv_to_tm fv  in
        FStar_All.pipe_left ret uu____15704
    | FStar_Reflection_Data.Tv_App (l,(r,q)) ->
        let q' = FStar_Reflection_Basic.pack_aqual q  in
        let uu____15711 = FStar_Syntax_Util.mk_app l [(r, q')]  in
        FStar_All.pipe_left ret uu____15711
    | FStar_Reflection_Data.Tv_Abs (b,t) ->
        let uu____15736 =
          FStar_Syntax_Util.abs [b] t FStar_Pervasives_Native.None  in
        FStar_All.pipe_left ret uu____15736
    | FStar_Reflection_Data.Tv_Arrow (b,c) ->
        let uu____15753 = FStar_Syntax_Util.arrow [b] c  in
        FStar_All.pipe_left ret uu____15753
    | FStar_Reflection_Data.Tv_Type () ->
        FStar_All.pipe_left ret FStar_Syntax_Util.ktype
    | FStar_Reflection_Data.Tv_Refine (bv,t) ->
        let uu____15772 = FStar_Syntax_Util.refine bv t  in
        FStar_All.pipe_left ret uu____15772
    | FStar_Reflection_Data.Tv_Const c ->
        let uu____15776 =
          let uu____15777 =
            let uu____15784 =
              let uu____15785 = FStar_Reflection_Basic.pack_const c  in
              FStar_Syntax_Syntax.Tm_constant uu____15785  in
            FStar_Syntax_Syntax.mk uu____15784  in
          uu____15777 FStar_Pervasives_Native.None FStar_Range.dummyRange  in
        FStar_All.pipe_left ret uu____15776
    | FStar_Reflection_Data.Tv_Uvar (_u,ctx_u_s) ->
        let uu____15790 =
          FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_uvar ctx_u_s)
            FStar_Pervasives_Native.None FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____15790
    | FStar_Reflection_Data.Tv_Let (false ,attrs,bv,t1,t2) ->
        let lb =
          FStar_Syntax_Util.mk_letbinding (FStar_Util.Inl bv) []
            bv.FStar_Syntax_Syntax.sort FStar_Parser_Const.effect_Tot_lid t1
            attrs FStar_Range.dummyRange
           in
        let uu____15804 =
          let uu____15805 =
            let uu____15812 =
              let uu____15813 =
                let uu____15827 =
                  let uu____15830 =
                    let uu____15831 = FStar_Syntax_Syntax.mk_binder bv  in
                    [uu____15831]  in
                  FStar_Syntax_Subst.close uu____15830 t2  in
                ((false, [lb]), uu____15827)  in
              FStar_Syntax_Syntax.Tm_let uu____15813  in
            FStar_Syntax_Syntax.mk uu____15812  in
          uu____15805 FStar_Pervasives_Native.None FStar_Range.dummyRange  in
        FStar_All.pipe_left ret uu____15804
    | FStar_Reflection_Data.Tv_Let (true ,attrs,bv,t1,t2) ->
        let lb =
          FStar_Syntax_Util.mk_letbinding (FStar_Util.Inl bv) []
            bv.FStar_Syntax_Syntax.sort FStar_Parser_Const.effect_Tot_lid t1
            attrs FStar_Range.dummyRange
           in
        let uu____15876 = FStar_Syntax_Subst.close_let_rec [lb] t2  in
        (match uu____15876 with
         | (lbs,body) ->
             let uu____15891 =
               FStar_Syntax_Syntax.mk
                 (FStar_Syntax_Syntax.Tm_let ((true, lbs), body))
                 FStar_Pervasives_Native.None FStar_Range.dummyRange
                in
             FStar_All.pipe_left ret uu____15891)
    | FStar_Reflection_Data.Tv_Match (t,brs) ->
        let wrap v1 =
          {
            FStar_Syntax_Syntax.v = v1;
            FStar_Syntax_Syntax.p = FStar_Range.dummyRange
          }  in
        let rec pack_pat p =
          match p with
          | FStar_Reflection_Data.Pat_Constant c ->
              let uu____15928 =
                let uu____15929 = FStar_Reflection_Basic.pack_const c  in
                FStar_Syntax_Syntax.Pat_constant uu____15929  in
              FStar_All.pipe_left wrap uu____15928
          | FStar_Reflection_Data.Pat_Cons (fv,ps) ->
              let uu____15946 =
                let uu____15947 =
                  let uu____15961 =
                    FStar_List.map
                      (fun uu____15985  ->
                         match uu____15985 with
                         | (p1,b) ->
                             let uu____16000 = pack_pat p1  in
                             (uu____16000, b)) ps
                     in
                  (fv, uu____15961)  in
                FStar_Syntax_Syntax.Pat_cons uu____15947  in
              FStar_All.pipe_left wrap uu____15946
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
            (fun uu___9_16048  ->
               match uu___9_16048 with
               | (pat,t1) ->
                   let uu____16065 = pack_pat pat  in
                   (uu____16065, FStar_Pervasives_Native.None, t1)) brs
           in
        let brs2 = FStar_List.map FStar_Syntax_Subst.close_branch brs1  in
        let uu____16113 =
          FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_match (t, brs2))
            FStar_Pervasives_Native.None FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____16113
    | FStar_Reflection_Data.Tv_AscribedT (e,t,tacopt) ->
        let uu____16141 =
          FStar_Syntax_Syntax.mk
            (FStar_Syntax_Syntax.Tm_ascribed
               (e, ((FStar_Util.Inl t), tacopt),
                 FStar_Pervasives_Native.None)) FStar_Pervasives_Native.None
            FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____16141
    | FStar_Reflection_Data.Tv_AscribedC (e,c,tacopt) ->
        let uu____16187 =
          FStar_Syntax_Syntax.mk
            (FStar_Syntax_Syntax.Tm_ascribed
               (e, ((FStar_Util.Inr c), tacopt),
                 FStar_Pervasives_Native.None)) FStar_Pervasives_Native.None
            FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____16187
    | FStar_Reflection_Data.Tv_Unknown  ->
        let uu____16226 =
          FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown
            FStar_Pervasives_Native.None FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____16226
  
let (lget :
  FStar_Reflection_Data.typ -> Prims.string -> FStar_Syntax_Syntax.term tac)
  =
  fun ty  ->
    fun k  ->
      let uu____16246 =
        bind get
          (fun ps  ->
             let uu____16252 =
               FStar_Util.psmap_try_find ps.FStar_Tactics_Types.local_state k
                in
             match uu____16252 with
             | FStar_Pervasives_Native.None  -> fail "not found"
             | FStar_Pervasives_Native.Some t -> unquote ty t)
         in
      FStar_All.pipe_left (wrap_err "lget") uu____16246
  
let (lset :
  FStar_Reflection_Data.typ ->
    Prims.string -> FStar_Syntax_Syntax.term -> unit tac)
  =
  fun _ty  ->
    fun k  ->
      fun t  ->
        let uu____16286 =
          bind get
            (fun ps  ->
               let ps1 =
                 let uu___2254_16293 = ps  in
                 let uu____16294 =
                   FStar_Util.psmap_add ps.FStar_Tactics_Types.local_state k
                     t
                    in
                 {
                   FStar_Tactics_Types.main_context =
                     (uu___2254_16293.FStar_Tactics_Types.main_context);
                   FStar_Tactics_Types.all_implicits =
                     (uu___2254_16293.FStar_Tactics_Types.all_implicits);
                   FStar_Tactics_Types.goals =
                     (uu___2254_16293.FStar_Tactics_Types.goals);
                   FStar_Tactics_Types.smt_goals =
                     (uu___2254_16293.FStar_Tactics_Types.smt_goals);
                   FStar_Tactics_Types.depth =
                     (uu___2254_16293.FStar_Tactics_Types.depth);
                   FStar_Tactics_Types.__dump =
                     (uu___2254_16293.FStar_Tactics_Types.__dump);
                   FStar_Tactics_Types.psc =
                     (uu___2254_16293.FStar_Tactics_Types.psc);
                   FStar_Tactics_Types.entry_range =
                     (uu___2254_16293.FStar_Tactics_Types.entry_range);
                   FStar_Tactics_Types.guard_policy =
                     (uu___2254_16293.FStar_Tactics_Types.guard_policy);
                   FStar_Tactics_Types.freshness =
                     (uu___2254_16293.FStar_Tactics_Types.freshness);
                   FStar_Tactics_Types.tac_verb_dbg =
                     (uu___2254_16293.FStar_Tactics_Types.tac_verb_dbg);
                   FStar_Tactics_Types.local_state = uu____16294
                 }  in
               set ps1)
           in
        FStar_All.pipe_left (wrap_err "lset") uu____16286
  
let (goal_of_goal_ty :
  env ->
    FStar_Reflection_Data.typ ->
      (FStar_Tactics_Types.goal * FStar_TypeChecker_Common.guard_t))
  =
  fun env  ->
    fun typ  ->
      let uu____16321 =
        FStar_TypeChecker_Util.new_implicit_var "proofstate_of_goal_ty"
          typ.FStar_Syntax_Syntax.pos env typ
         in
      match uu____16321 with
      | (u,ctx_uvars,g_u) ->
          let uu____16354 = FStar_List.hd ctx_uvars  in
          (match uu____16354 with
           | (ctx_uvar,uu____16368) ->
               let g =
                 let uu____16370 = FStar_Options.peek ()  in
                 FStar_Tactics_Types.mk_goal env ctx_uvar uu____16370 false
                   ""
                  in
               (g, g_u))
  
let (tac_env : FStar_TypeChecker_Env.env -> FStar_TypeChecker_Env.env) =
  fun env  ->
    let uu____16379 = FStar_TypeChecker_Env.clear_expected_typ env  in
    match uu____16379 with
    | (env1,uu____16387) ->
        let env2 =
          let uu___2271_16393 = env1  in
          {
            FStar_TypeChecker_Env.solver =
              (uu___2271_16393.FStar_TypeChecker_Env.solver);
            FStar_TypeChecker_Env.range =
              (uu___2271_16393.FStar_TypeChecker_Env.range);
            FStar_TypeChecker_Env.curmodule =
              (uu___2271_16393.FStar_TypeChecker_Env.curmodule);
            FStar_TypeChecker_Env.gamma =
              (uu___2271_16393.FStar_TypeChecker_Env.gamma);
            FStar_TypeChecker_Env.gamma_sig =
              (uu___2271_16393.FStar_TypeChecker_Env.gamma_sig);
            FStar_TypeChecker_Env.gamma_cache =
              (uu___2271_16393.FStar_TypeChecker_Env.gamma_cache);
            FStar_TypeChecker_Env.modules =
              (uu___2271_16393.FStar_TypeChecker_Env.modules);
            FStar_TypeChecker_Env.expected_typ =
              (uu___2271_16393.FStar_TypeChecker_Env.expected_typ);
            FStar_TypeChecker_Env.sigtab =
              (uu___2271_16393.FStar_TypeChecker_Env.sigtab);
            FStar_TypeChecker_Env.attrtab =
              (uu___2271_16393.FStar_TypeChecker_Env.attrtab);
            FStar_TypeChecker_Env.instantiate_imp = false;
            FStar_TypeChecker_Env.effects =
              (uu___2271_16393.FStar_TypeChecker_Env.effects);
            FStar_TypeChecker_Env.generalize =
              (uu___2271_16393.FStar_TypeChecker_Env.generalize);
            FStar_TypeChecker_Env.letrecs =
              (uu___2271_16393.FStar_TypeChecker_Env.letrecs);
            FStar_TypeChecker_Env.top_level =
              (uu___2271_16393.FStar_TypeChecker_Env.top_level);
            FStar_TypeChecker_Env.check_uvars =
              (uu___2271_16393.FStar_TypeChecker_Env.check_uvars);
            FStar_TypeChecker_Env.use_eq =
              (uu___2271_16393.FStar_TypeChecker_Env.use_eq);
            FStar_TypeChecker_Env.use_eq_strict =
              (uu___2271_16393.FStar_TypeChecker_Env.use_eq_strict);
            FStar_TypeChecker_Env.is_iface =
              (uu___2271_16393.FStar_TypeChecker_Env.is_iface);
            FStar_TypeChecker_Env.admit =
              (uu___2271_16393.FStar_TypeChecker_Env.admit);
            FStar_TypeChecker_Env.lax =
              (uu___2271_16393.FStar_TypeChecker_Env.lax);
            FStar_TypeChecker_Env.lax_universes =
              (uu___2271_16393.FStar_TypeChecker_Env.lax_universes);
            FStar_TypeChecker_Env.phase1 =
              (uu___2271_16393.FStar_TypeChecker_Env.phase1);
            FStar_TypeChecker_Env.failhard =
              (uu___2271_16393.FStar_TypeChecker_Env.failhard);
            FStar_TypeChecker_Env.nosynth =
              (uu___2271_16393.FStar_TypeChecker_Env.nosynth);
            FStar_TypeChecker_Env.uvar_subtyping =
              (uu___2271_16393.FStar_TypeChecker_Env.uvar_subtyping);
            FStar_TypeChecker_Env.tc_term =
              (uu___2271_16393.FStar_TypeChecker_Env.tc_term);
            FStar_TypeChecker_Env.type_of =
              (uu___2271_16393.FStar_TypeChecker_Env.type_of);
            FStar_TypeChecker_Env.universe_of =
              (uu___2271_16393.FStar_TypeChecker_Env.universe_of);
            FStar_TypeChecker_Env.check_type_of =
              (uu___2271_16393.FStar_TypeChecker_Env.check_type_of);
            FStar_TypeChecker_Env.use_bv_sorts =
              (uu___2271_16393.FStar_TypeChecker_Env.use_bv_sorts);
            FStar_TypeChecker_Env.qtbl_name_and_index =
              (uu___2271_16393.FStar_TypeChecker_Env.qtbl_name_and_index);
            FStar_TypeChecker_Env.normalized_eff_names =
              (uu___2271_16393.FStar_TypeChecker_Env.normalized_eff_names);
            FStar_TypeChecker_Env.fv_delta_depths =
              (uu___2271_16393.FStar_TypeChecker_Env.fv_delta_depths);
            FStar_TypeChecker_Env.proof_ns =
              (uu___2271_16393.FStar_TypeChecker_Env.proof_ns);
            FStar_TypeChecker_Env.synth_hook =
              (uu___2271_16393.FStar_TypeChecker_Env.synth_hook);
            FStar_TypeChecker_Env.try_solve_implicits_hook =
              (uu___2271_16393.FStar_TypeChecker_Env.try_solve_implicits_hook);
            FStar_TypeChecker_Env.splice =
              (uu___2271_16393.FStar_TypeChecker_Env.splice);
            FStar_TypeChecker_Env.mpreprocess =
              (uu___2271_16393.FStar_TypeChecker_Env.mpreprocess);
            FStar_TypeChecker_Env.postprocess =
              (uu___2271_16393.FStar_TypeChecker_Env.postprocess);
            FStar_TypeChecker_Env.is_native_tactic =
              (uu___2271_16393.FStar_TypeChecker_Env.is_native_tactic);
            FStar_TypeChecker_Env.identifier_info =
              (uu___2271_16393.FStar_TypeChecker_Env.identifier_info);
            FStar_TypeChecker_Env.tc_hooks =
              (uu___2271_16393.FStar_TypeChecker_Env.tc_hooks);
            FStar_TypeChecker_Env.dsenv =
              (uu___2271_16393.FStar_TypeChecker_Env.dsenv);
            FStar_TypeChecker_Env.nbe =
              (uu___2271_16393.FStar_TypeChecker_Env.nbe);
            FStar_TypeChecker_Env.strict_args_tab =
              (uu___2271_16393.FStar_TypeChecker_Env.strict_args_tab);
            FStar_TypeChecker_Env.erasable_types_tab =
              (uu___2271_16393.FStar_TypeChecker_Env.erasable_types_tab)
          }  in
        let env3 =
          let uu___2274_16396 = env2  in
          {
            FStar_TypeChecker_Env.solver =
              (uu___2274_16396.FStar_TypeChecker_Env.solver);
            FStar_TypeChecker_Env.range =
              (uu___2274_16396.FStar_TypeChecker_Env.range);
            FStar_TypeChecker_Env.curmodule =
              (uu___2274_16396.FStar_TypeChecker_Env.curmodule);
            FStar_TypeChecker_Env.gamma =
              (uu___2274_16396.FStar_TypeChecker_Env.gamma);
            FStar_TypeChecker_Env.gamma_sig =
              (uu___2274_16396.FStar_TypeChecker_Env.gamma_sig);
            FStar_TypeChecker_Env.gamma_cache =
              (uu___2274_16396.FStar_TypeChecker_Env.gamma_cache);
            FStar_TypeChecker_Env.modules =
              (uu___2274_16396.FStar_TypeChecker_Env.modules);
            FStar_TypeChecker_Env.expected_typ =
              (uu___2274_16396.FStar_TypeChecker_Env.expected_typ);
            FStar_TypeChecker_Env.sigtab =
              (uu___2274_16396.FStar_TypeChecker_Env.sigtab);
            FStar_TypeChecker_Env.attrtab =
              (uu___2274_16396.FStar_TypeChecker_Env.attrtab);
            FStar_TypeChecker_Env.instantiate_imp =
              (uu___2274_16396.FStar_TypeChecker_Env.instantiate_imp);
            FStar_TypeChecker_Env.effects =
              (uu___2274_16396.FStar_TypeChecker_Env.effects);
            FStar_TypeChecker_Env.generalize =
              (uu___2274_16396.FStar_TypeChecker_Env.generalize);
            FStar_TypeChecker_Env.letrecs =
              (uu___2274_16396.FStar_TypeChecker_Env.letrecs);
            FStar_TypeChecker_Env.top_level =
              (uu___2274_16396.FStar_TypeChecker_Env.top_level);
            FStar_TypeChecker_Env.check_uvars =
              (uu___2274_16396.FStar_TypeChecker_Env.check_uvars);
            FStar_TypeChecker_Env.use_eq =
              (uu___2274_16396.FStar_TypeChecker_Env.use_eq);
            FStar_TypeChecker_Env.use_eq_strict =
              (uu___2274_16396.FStar_TypeChecker_Env.use_eq_strict);
            FStar_TypeChecker_Env.is_iface =
              (uu___2274_16396.FStar_TypeChecker_Env.is_iface);
            FStar_TypeChecker_Env.admit =
              (uu___2274_16396.FStar_TypeChecker_Env.admit);
            FStar_TypeChecker_Env.lax =
              (uu___2274_16396.FStar_TypeChecker_Env.lax);
            FStar_TypeChecker_Env.lax_universes =
              (uu___2274_16396.FStar_TypeChecker_Env.lax_universes);
            FStar_TypeChecker_Env.phase1 =
              (uu___2274_16396.FStar_TypeChecker_Env.phase1);
            FStar_TypeChecker_Env.failhard = true;
            FStar_TypeChecker_Env.nosynth =
              (uu___2274_16396.FStar_TypeChecker_Env.nosynth);
            FStar_TypeChecker_Env.uvar_subtyping =
              (uu___2274_16396.FStar_TypeChecker_Env.uvar_subtyping);
            FStar_TypeChecker_Env.tc_term =
              (uu___2274_16396.FStar_TypeChecker_Env.tc_term);
            FStar_TypeChecker_Env.type_of =
              (uu___2274_16396.FStar_TypeChecker_Env.type_of);
            FStar_TypeChecker_Env.universe_of =
              (uu___2274_16396.FStar_TypeChecker_Env.universe_of);
            FStar_TypeChecker_Env.check_type_of =
              (uu___2274_16396.FStar_TypeChecker_Env.check_type_of);
            FStar_TypeChecker_Env.use_bv_sorts =
              (uu___2274_16396.FStar_TypeChecker_Env.use_bv_sorts);
            FStar_TypeChecker_Env.qtbl_name_and_index =
              (uu___2274_16396.FStar_TypeChecker_Env.qtbl_name_and_index);
            FStar_TypeChecker_Env.normalized_eff_names =
              (uu___2274_16396.FStar_TypeChecker_Env.normalized_eff_names);
            FStar_TypeChecker_Env.fv_delta_depths =
              (uu___2274_16396.FStar_TypeChecker_Env.fv_delta_depths);
            FStar_TypeChecker_Env.proof_ns =
              (uu___2274_16396.FStar_TypeChecker_Env.proof_ns);
            FStar_TypeChecker_Env.synth_hook =
              (uu___2274_16396.FStar_TypeChecker_Env.synth_hook);
            FStar_TypeChecker_Env.try_solve_implicits_hook =
              (uu___2274_16396.FStar_TypeChecker_Env.try_solve_implicits_hook);
            FStar_TypeChecker_Env.splice =
              (uu___2274_16396.FStar_TypeChecker_Env.splice);
            FStar_TypeChecker_Env.mpreprocess =
              (uu___2274_16396.FStar_TypeChecker_Env.mpreprocess);
            FStar_TypeChecker_Env.postprocess =
              (uu___2274_16396.FStar_TypeChecker_Env.postprocess);
            FStar_TypeChecker_Env.is_native_tactic =
              (uu___2274_16396.FStar_TypeChecker_Env.is_native_tactic);
            FStar_TypeChecker_Env.identifier_info =
              (uu___2274_16396.FStar_TypeChecker_Env.identifier_info);
            FStar_TypeChecker_Env.tc_hooks =
              (uu___2274_16396.FStar_TypeChecker_Env.tc_hooks);
            FStar_TypeChecker_Env.dsenv =
              (uu___2274_16396.FStar_TypeChecker_Env.dsenv);
            FStar_TypeChecker_Env.nbe =
              (uu___2274_16396.FStar_TypeChecker_Env.nbe);
            FStar_TypeChecker_Env.strict_args_tab =
              (uu___2274_16396.FStar_TypeChecker_Env.strict_args_tab);
            FStar_TypeChecker_Env.erasable_types_tab =
              (uu___2274_16396.FStar_TypeChecker_Env.erasable_types_tab)
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
            let uu____16429 =
              FStar_TypeChecker_Env.debug env1
                (FStar_Options.Other "TacVerbose")
               in
            let uu____16432 = FStar_Util.psmap_empty ()  in
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
              FStar_Tactics_Types.tac_verb_dbg = uu____16429;
              FStar_Tactics_Types.local_state = uu____16432
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
        let uu____16458 = goal_of_goal_ty env1 typ  in
        match uu____16458 with
        | (g,g_u) ->
            let ps =
              proofstate_of_goals rng env1 [g]
                g_u.FStar_TypeChecker_Common.implicits
               in
            let uu____16470 = FStar_Tactics_Types.goal_witness g  in
            (ps, uu____16470)
  
let (goal_of_implicit :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Env.implicit -> FStar_Tactics_Types.goal)
  =
  fun env  ->
    fun i  ->
      let uu____16482 = FStar_Options.peek ()  in
      FStar_Tactics_Types.mk_goal env i.FStar_TypeChecker_Common.imp_uvar
        uu____16482 false ""
  
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
          let uu____16509 = FStar_List.hd goals  in
          FStar_Tactics_Types.goal_witness uu____16509  in
        let ps =
          let uu____16511 =
            FStar_TypeChecker_Env.debug env
              (FStar_Options.Other "TacVerbose")
             in
          let uu____16514 = FStar_Util.psmap_empty ()  in
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
            FStar_Tactics_Types.tac_verb_dbg = uu____16511;
            FStar_Tactics_Types.local_state = uu____16514
          }  in
        (ps, w)
  