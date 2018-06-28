open Prims
type goal = FStar_Tactics_Types.goal
type name = FStar_Syntax_Syntax.bv
type env = FStar_TypeChecker_Env.env
type implicits = FStar_TypeChecker_Env.implicits
let (normalize :
  FStar_TypeChecker_Normalize.step Prims.list ->
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
    let uu____43 =
      let uu____44 = FStar_Tactics_Types.goal_env g  in
      let uu____45 = FStar_Tactics_Types.goal_type g  in
      bnorm uu____44 uu____45  in
    FStar_Tactics_Types.goal_with_type g uu____43
  
type 'a tac =
  {
  tac_f: FStar_Tactics_Types.proofstate -> 'a FStar_Tactics_Result.__result }
let __proj__Mktac__item__tac_f :
  'a .
    'a tac ->
      FStar_Tactics_Types.proofstate -> 'a FStar_Tactics_Result.__result
  =
  fun projectee  ->
    match projectee with | { tac_f = __fname__tac_f;_} -> __fname__tac_f
  
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
      try t.tac_f p
      with
      | FStar_Errors.Err (uu____167,msg) ->
          FStar_Tactics_Result.Failed (msg, p)
      | FStar_Errors.Error (uu____169,msg,uu____171) ->
          FStar_Tactics_Result.Failed (msg, p)
      | e ->
          let uu____173 =
            let uu____178 = FStar_Util.message_of_exn e  in (uu____178, p)
             in
          FStar_Tactics_Result.Failed uu____173
  
let rec (log : FStar_Tactics_Types.proofstate -> (unit -> unit) -> unit) =
  fun ps  ->
    fun f  -> if ps.FStar_Tactics_Types.tac_verb_dbg then f () else ()
  
let ret : 'a . 'a -> 'a tac =
  fun x  -> mk_tac (fun p  -> FStar_Tactics_Result.Success (x, p)) 
let bind : 'a 'b . 'a tac -> ('a -> 'b tac) -> 'b tac =
  fun t1  ->
    fun t2  ->
      mk_tac
        (fun p  ->
           let uu____250 = run t1 p  in
           match uu____250 with
           | FStar_Tactics_Result.Success (a,q) ->
               let uu____257 = t2 a  in run uu____257 q
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
    let uu____277 =
      FStar_Syntax_Unionfind.find uv.FStar_Syntax_Syntax.ctx_uvar_head  in
    match uu____277 with
    | FStar_Pervasives_Native.Some t -> FStar_Pervasives_Native.Some t
    | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
  
let (check_goal_solved :
  FStar_Tactics_Types.goal ->
    FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  = fun goal  -> get_uvar_solved goal.FStar_Tactics_Types.goal_ctx_uvar 
let (goal_to_string_verbose : FStar_Tactics_Types.goal -> Prims.string) =
  fun g  ->
    let uu____295 =
      FStar_Syntax_Print.ctx_uvar_to_string
        g.FStar_Tactics_Types.goal_ctx_uvar
       in
    let uu____296 =
      let uu____297 = check_goal_solved g  in
      match uu____297 with
      | FStar_Pervasives_Native.None  -> ""
      | FStar_Pervasives_Native.Some t ->
          let uu____301 = FStar_Syntax_Print.term_to_string t  in
          FStar_Util.format1 "\tGOAL ALREADY SOLVED!: %s" uu____301
       in
    FStar_Util.format2 "%s%s" uu____295 uu____296
  
let (goal_to_string :
  FStar_Tactics_Types.proofstate -> FStar_Tactics_Types.goal -> Prims.string)
  =
  fun ps  ->
    fun g  ->
      let uu____312 =
        (FStar_Options.print_implicits ()) ||
          ps.FStar_Tactics_Types.tac_verb_dbg
         in
      if uu____312
      then goal_to_string_verbose g
      else
        (let w =
           let uu____315 =
             get_uvar_solved g.FStar_Tactics_Types.goal_ctx_uvar  in
           match uu____315 with
           | FStar_Pervasives_Native.None  -> "_"
           | FStar_Pervasives_Native.Some t ->
               let uu____319 = FStar_Tactics_Types.goal_env g  in
               tts uu____319 t
            in
         let uu____320 =
           FStar_Syntax_Print.binders_to_string ", "
             (g.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_binders
            in
         let uu____321 =
           let uu____322 = FStar_Tactics_Types.goal_env g  in
           tts uu____322
             (g.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_typ
            in
         FStar_Util.format3 "%s |- %s : %s" uu____320 w uu____321)
  
let (tacprint : Prims.string -> unit) =
  fun s  -> FStar_Util.print1 "TAC>> %s\n" s 
let (tacprint1 : Prims.string -> Prims.string -> unit) =
  fun s  ->
    fun x  ->
      let uu____338 = FStar_Util.format1 s x  in
      FStar_Util.print1 "TAC>> %s\n" uu____338
  
let (tacprint2 : Prims.string -> Prims.string -> Prims.string -> unit) =
  fun s  ->
    fun x  ->
      fun y  ->
        let uu____354 = FStar_Util.format2 s x y  in
        FStar_Util.print1 "TAC>> %s\n" uu____354
  
let (tacprint3 :
  Prims.string -> Prims.string -> Prims.string -> Prims.string -> unit) =
  fun s  ->
    fun x  ->
      fun y  ->
        fun z  ->
          let uu____375 = FStar_Util.format3 s x y z  in
          FStar_Util.print1 "TAC>> %s\n" uu____375
  
let (comp_to_typ : FStar_Syntax_Syntax.comp -> FStar_Reflection_Data.typ) =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Total (t,uu____382) -> t
    | FStar_Syntax_Syntax.GTotal (t,uu____392) -> t
    | FStar_Syntax_Syntax.Comp ct -> ct.FStar_Syntax_Syntax.result_typ
  
let (is_irrelevant : FStar_Tactics_Types.goal -> Prims.bool) =
  fun g  ->
    let uu____407 =
      let uu____412 =
        let uu____413 = FStar_Tactics_Types.goal_env g  in
        let uu____414 = FStar_Tactics_Types.goal_type g  in
        FStar_TypeChecker_Normalize.unfold_whnf uu____413 uu____414  in
      FStar_Syntax_Util.un_squash uu____412  in
    match uu____407 with
    | FStar_Pervasives_Native.Some t -> true
    | uu____420 -> false
  
let (print : Prims.string -> unit tac) = fun msg  -> tacprint msg; ret () 
let (debug : Prims.string -> unit tac) =
  fun msg  ->
    bind get
      (fun ps  ->
         (let uu____448 =
            let uu____449 =
              FStar_Ident.string_of_lid
                (ps.FStar_Tactics_Types.main_context).FStar_TypeChecker_Env.curmodule
               in
            FStar_Options.debug_module uu____449  in
          if uu____448 then tacprint msg else ());
         ret ())
  
let (dump_goal :
  FStar_Tactics_Types.proofstate -> FStar_Tactics_Types.goal -> unit) =
  fun ps  ->
    fun goal  ->
      let uu____462 = goal_to_string ps goal  in tacprint uu____462
  
let (dump_cur : FStar_Tactics_Types.proofstate -> Prims.string -> unit) =
  fun ps  ->
    fun msg  ->
      match ps.FStar_Tactics_Types.goals with
      | [] -> tacprint1 "No more goals (%s)" msg
      | h::uu____474 ->
          (tacprint1 "Current goal (%s):" msg;
           (let uu____478 = FStar_List.hd ps.FStar_Tactics_Types.goals  in
            dump_goal ps uu____478))
  
let (ps_to_string :
  (Prims.string,FStar_Tactics_Types.proofstate)
    FStar_Pervasives_Native.tuple2 -> Prims.string)
  =
  fun uu____487  ->
    match uu____487 with
    | (msg,ps) ->
        let p_imp imp =
          FStar_Syntax_Print.uvar_to_string
            (imp.FStar_TypeChecker_Env.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_head
           in
        let uu____500 =
          let uu____503 =
            let uu____504 =
              FStar_Util.string_of_int ps.FStar_Tactics_Types.depth  in
            FStar_Util.format2 "State dump @ depth %s (%s):\n" uu____504 msg
             in
          let uu____505 =
            let uu____508 =
              if ps.FStar_Tactics_Types.entry_range <> FStar_Range.dummyRange
              then
                let uu____509 =
                  FStar_Range.string_of_def_range
                    ps.FStar_Tactics_Types.entry_range
                   in
                FStar_Util.format1 "Location: %s\n" uu____509
              else ""  in
            let uu____511 =
              let uu____514 =
                let uu____515 =
                  FStar_TypeChecker_Env.debug
                    ps.FStar_Tactics_Types.main_context
                    (FStar_Options.Other "Imp")
                   in
                if uu____515
                then
                  let uu____516 =
                    FStar_Common.string_of_list p_imp
                      ps.FStar_Tactics_Types.all_implicits
                     in
                  FStar_Util.format1 "Imps: %s\n" uu____516
                else ""  in
              let uu____518 =
                let uu____521 =
                  let uu____522 =
                    FStar_Util.string_of_int
                      (FStar_List.length ps.FStar_Tactics_Types.goals)
                     in
                  let uu____523 =
                    let uu____524 =
                      FStar_List.map (goal_to_string ps)
                        ps.FStar_Tactics_Types.goals
                       in
                    FStar_String.concat "\n" uu____524  in
                  FStar_Util.format2 "ACTIVE goals (%s):\n%s\n" uu____522
                    uu____523
                   in
                let uu____527 =
                  let uu____530 =
                    let uu____531 =
                      FStar_Util.string_of_int
                        (FStar_List.length ps.FStar_Tactics_Types.smt_goals)
                       in
                    let uu____532 =
                      let uu____533 =
                        FStar_List.map (goal_to_string ps)
                          ps.FStar_Tactics_Types.smt_goals
                         in
                      FStar_String.concat "\n" uu____533  in
                    FStar_Util.format2 "SMT goals (%s):\n%s\n" uu____531
                      uu____532
                     in
                  [uu____530]  in
                uu____521 :: uu____527  in
              uu____514 :: uu____518  in
            uu____508 :: uu____511  in
          uu____503 :: uu____505  in
        FStar_String.concat "" uu____500
  
let (goal_to_json : FStar_Tactics_Types.goal -> FStar_Util.json) =
  fun g  ->
    let g_binders =
      let uu____542 =
        let uu____543 = FStar_Tactics_Types.goal_env g  in
        FStar_TypeChecker_Env.all_binders uu____543  in
      let uu____544 =
        let uu____549 =
          let uu____550 = FStar_Tactics_Types.goal_env g  in
          FStar_TypeChecker_Env.dsenv uu____550  in
        FStar_Syntax_Print.binders_to_json uu____549  in
      FStar_All.pipe_right uu____542 uu____544  in
    let uu____551 =
      let uu____558 =
        let uu____565 =
          let uu____570 =
            let uu____571 =
              let uu____578 =
                let uu____583 =
                  let uu____584 =
                    let uu____585 = FStar_Tactics_Types.goal_env g  in
                    let uu____586 = FStar_Tactics_Types.goal_witness g  in
                    tts uu____585 uu____586  in
                  FStar_Util.JsonStr uu____584  in
                ("witness", uu____583)  in
              let uu____587 =
                let uu____594 =
                  let uu____599 =
                    let uu____600 =
                      let uu____601 = FStar_Tactics_Types.goal_env g  in
                      let uu____602 = FStar_Tactics_Types.goal_type g  in
                      tts uu____601 uu____602  in
                    FStar_Util.JsonStr uu____600  in
                  ("type", uu____599)  in
                [uu____594]  in
              uu____578 :: uu____587  in
            FStar_Util.JsonAssoc uu____571  in
          ("goal", uu____570)  in
        [uu____565]  in
      ("hyps", g_binders) :: uu____558  in
    FStar_Util.JsonAssoc uu____551
  
let (ps_to_json :
  (Prims.string,FStar_Tactics_Types.proofstate)
    FStar_Pervasives_Native.tuple2 -> FStar_Util.json)
  =
  fun uu____635  ->
    match uu____635 with
    | (msg,ps) ->
        let uu____642 =
          let uu____649 =
            let uu____656 =
              let uu____663 =
                let uu____670 =
                  let uu____675 =
                    let uu____676 =
                      FStar_List.map goal_to_json
                        ps.FStar_Tactics_Types.goals
                       in
                    FStar_Util.JsonList uu____676  in
                  ("goals", uu____675)  in
                let uu____679 =
                  let uu____686 =
                    let uu____691 =
                      let uu____692 =
                        FStar_List.map goal_to_json
                          ps.FStar_Tactics_Types.smt_goals
                         in
                      FStar_Util.JsonList uu____692  in
                    ("smt-goals", uu____691)  in
                  [uu____686]  in
                uu____670 :: uu____679  in
              ("depth", (FStar_Util.JsonInt (ps.FStar_Tactics_Types.depth)))
                :: uu____663
               in
            ("label", (FStar_Util.JsonStr msg)) :: uu____656  in
          let uu____715 =
            if ps.FStar_Tactics_Types.entry_range <> FStar_Range.dummyRange
            then
              let uu____728 =
                let uu____733 =
                  FStar_Range.json_of_def_range
                    ps.FStar_Tactics_Types.entry_range
                   in
                ("location", uu____733)  in
              [uu____728]
            else []  in
          FStar_List.append uu____649 uu____715  in
        FStar_Util.JsonAssoc uu____642
  
let (dump_proofstate :
  FStar_Tactics_Types.proofstate -> Prims.string -> unit) =
  fun ps  ->
    fun msg  ->
      FStar_Options.with_saved_options
        (fun uu____763  ->
           FStar_Options.set_option "print_effect_args"
             (FStar_Options.Bool true);
           FStar_Util.print_generic "proof-state" ps_to_string ps_to_json
             (msg, ps))
  
let (print_proof_state1 : Prims.string -> unit tac) =
  fun msg  ->
    mk_tac
      (fun ps  ->
         let psc = ps.FStar_Tactics_Types.psc  in
         let subst1 = FStar_TypeChecker_Normalize.psc_subst psc  in
         (let uu____786 = FStar_Tactics_Types.subst_proof_state subst1 ps  in
          dump_cur uu____786 msg);
         FStar_Tactics_Result.Success ((), ps))
  
let (print_proof_state : Prims.string -> unit tac) =
  fun msg  ->
    mk_tac
      (fun ps  ->
         let psc = ps.FStar_Tactics_Types.psc  in
         let subst1 = FStar_TypeChecker_Normalize.psc_subst psc  in
         (let uu____804 = FStar_Tactics_Types.subst_proof_state subst1 ps  in
          dump_proofstate uu____804 msg);
         FStar_Tactics_Result.Success ((), ps))
  
let mlog : 'a . (unit -> unit) -> (unit -> 'a tac) -> 'a tac =
  fun f  -> fun cont  -> bind get (fun ps  -> log ps f; cont ()) 
let fail : 'a . Prims.string -> 'a tac =
  fun msg  ->
    mk_tac
      (fun ps  ->
         (let uu____858 =
            FStar_TypeChecker_Env.debug ps.FStar_Tactics_Types.main_context
              (FStar_Options.Other "TacFail")
             in
          if uu____858
          then dump_proofstate ps (Prims.strcat "TACTIC FAILING: " msg)
          else ());
         FStar_Tactics_Result.Failed (msg, ps))
  
let fail1 : 'Auu____866 . Prims.string -> Prims.string -> 'Auu____866 tac =
  fun msg  ->
    fun x  -> let uu____879 = FStar_Util.format1 msg x  in fail uu____879
  
let fail2 :
  'Auu____888 .
    Prims.string -> Prims.string -> Prims.string -> 'Auu____888 tac
  =
  fun msg  ->
    fun x  ->
      fun y  -> let uu____906 = FStar_Util.format2 msg x y  in fail uu____906
  
let fail3 :
  'Auu____917 .
    Prims.string ->
      Prims.string -> Prims.string -> Prims.string -> 'Auu____917 tac
  =
  fun msg  ->
    fun x  ->
      fun y  ->
        fun z  ->
          let uu____940 = FStar_Util.format3 msg x y z  in fail uu____940
  
let fail4 :
  'Auu____953 .
    Prims.string ->
      Prims.string ->
        Prims.string -> Prims.string -> Prims.string -> 'Auu____953 tac
  =
  fun msg  ->
    fun x  ->
      fun y  ->
        fun z  ->
          fun w  ->
            let uu____981 = FStar_Util.format4 msg x y z w  in fail uu____981
  
let trytac' : 'a . 'a tac -> (Prims.string,'a) FStar_Util.either tac =
  fun t  ->
    mk_tac
      (fun ps  ->
         let tx = FStar_Syntax_Unionfind.new_transaction ()  in
         let uu____1014 = run t ps  in
         match uu____1014 with
         | FStar_Tactics_Result.Success (a,q) ->
             (FStar_Syntax_Unionfind.commit tx;
              FStar_Tactics_Result.Success ((FStar_Util.Inr a), q))
         | FStar_Tactics_Result.Failed (m,q) ->
             (FStar_Syntax_Unionfind.rollback tx;
              (let ps1 =
                 let uu___348_1038 = ps  in
                 {
                   FStar_Tactics_Types.main_context =
                     (uu___348_1038.FStar_Tactics_Types.main_context);
                   FStar_Tactics_Types.main_goal =
                     (uu___348_1038.FStar_Tactics_Types.main_goal);
                   FStar_Tactics_Types.all_implicits =
                     (uu___348_1038.FStar_Tactics_Types.all_implicits);
                   FStar_Tactics_Types.goals =
                     (uu___348_1038.FStar_Tactics_Types.goals);
                   FStar_Tactics_Types.smt_goals =
                     (uu___348_1038.FStar_Tactics_Types.smt_goals);
                   FStar_Tactics_Types.depth =
                     (uu___348_1038.FStar_Tactics_Types.depth);
                   FStar_Tactics_Types.__dump =
                     (uu___348_1038.FStar_Tactics_Types.__dump);
                   FStar_Tactics_Types.psc =
                     (uu___348_1038.FStar_Tactics_Types.psc);
                   FStar_Tactics_Types.entry_range =
                     (uu___348_1038.FStar_Tactics_Types.entry_range);
                   FStar_Tactics_Types.guard_policy =
                     (uu___348_1038.FStar_Tactics_Types.guard_policy);
                   FStar_Tactics_Types.freshness =
                     (q.FStar_Tactics_Types.freshness);
                   FStar_Tactics_Types.tac_verb_dbg =
                     (uu___348_1038.FStar_Tactics_Types.tac_verb_dbg)
                 }  in
               FStar_Tactics_Result.Success ((FStar_Util.Inl m), ps1))))
  
let trytac : 'a . 'a tac -> 'a FStar_Pervasives_Native.option tac =
  fun t  ->
    let uu____1065 = trytac' t  in
    bind uu____1065
      (fun r  ->
         match r with
         | FStar_Util.Inr v1 -> ret (FStar_Pervasives_Native.Some v1)
         | FStar_Util.Inl uu____1092 -> ret FStar_Pervasives_Native.None)
  
let trytac_exn : 'a . 'a tac -> 'a FStar_Pervasives_Native.option tac =
  fun t  ->
    mk_tac
      (fun ps  ->
         try let uu____1128 = trytac t  in run uu____1128 ps
         with
         | FStar_Errors.Err (uu____1144,msg) ->
             (log ps
                (fun uu____1148  ->
                   FStar_Util.print1 "trytac_exn error: (%s)" msg);
              FStar_Tactics_Result.Success (FStar_Pervasives_Native.None, ps))
         | FStar_Errors.Error (uu____1153,msg,uu____1155) ->
             (log ps
                (fun uu____1158  ->
                   FStar_Util.print1 "trytac_exn error: (%s)" msg);
              FStar_Tactics_Result.Success (FStar_Pervasives_Native.None, ps)))
  
let wrap_err : 'a . Prims.string -> 'a tac -> 'a tac =
  fun pref  ->
    fun t  ->
      mk_tac
        (fun ps  ->
           let uu____1191 = run t ps  in
           match uu____1191 with
           | FStar_Tactics_Result.Success (a,q) ->
               FStar_Tactics_Result.Success (a, q)
           | FStar_Tactics_Result.Failed (msg,q) ->
               FStar_Tactics_Result.Failed
                 ((Prims.strcat pref (Prims.strcat ": " msg)), q))
  
let (set : FStar_Tactics_Types.proofstate -> unit tac) =
  fun p  -> mk_tac (fun uu____1210  -> FStar_Tactics_Result.Success ((), p)) 
let (__do_unify :
  env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.bool tac)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        (let uu____1231 =
           FStar_TypeChecker_Env.debug env (FStar_Options.Other "1346")  in
         if uu____1231
         then
           let uu____1232 = FStar_Syntax_Print.term_to_string t1  in
           let uu____1233 = FStar_Syntax_Print.term_to_string t2  in
           FStar_Util.print2 "%%%%%%%%do_unify %s =? %s\n" uu____1232
             uu____1233
         else ());
        (try
           let res = FStar_TypeChecker_Rel.teq_nosmt env t1 t2  in
           (let uu____1245 =
              FStar_TypeChecker_Env.debug env (FStar_Options.Other "1346")
               in
            if uu____1245
            then
              let uu____1246 = FStar_Util.string_of_bool res  in
              let uu____1247 = FStar_Syntax_Print.term_to_string t1  in
              let uu____1248 = FStar_Syntax_Print.term_to_string t2  in
              FStar_Util.print3 "%%%%%%%%do_unify (RESULT %s) %s =? %s\n"
                uu____1246 uu____1247 uu____1248
            else ());
           ret res
         with
         | FStar_Errors.Err (uu____1256,msg) ->
             mlog
               (fun uu____1259  ->
                  FStar_Util.print1 ">> do_unify error, (%s)\n" msg)
               (fun uu____1261  -> ret false)
         | FStar_Errors.Error (uu____1262,msg,r) ->
             mlog
               (fun uu____1267  ->
                  let uu____1268 = FStar_Range.string_of_range r  in
                  FStar_Util.print2 ">> do_unify error, (%s) at (%s)\n" msg
                    uu____1268) (fun uu____1270  -> ret false))
  
let (do_unify :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.bool tac)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        bind idtac
          (fun uu____1293  ->
             (let uu____1295 =
                FStar_TypeChecker_Env.debug env (FStar_Options.Other "1346")
                 in
              if uu____1295
              then
                (FStar_Options.push ();
                 (let uu____1297 =
                    FStar_Options.set_options FStar_Options.Set
                      "--debug_level Rel --debug_level RelCheck"
                     in
                  ()))
              else ());
             (let uu____1299 = __do_unify env t1 t2  in
              bind uu____1299
                (fun r  ->
                   (let uu____1306 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "1346")
                       in
                    if uu____1306 then FStar_Options.pop () else ());
                   ret r)))
  
let (remove_solved_goals : unit tac) =
  bind get
    (fun ps  ->
       let ps' =
         let uu___353_1314 = ps  in
         let uu____1315 =
           FStar_List.filter
             (fun g  ->
                let uu____1321 = check_goal_solved g  in
                FStar_Option.isNone uu____1321) ps.FStar_Tactics_Types.goals
            in
         {
           FStar_Tactics_Types.main_context =
             (uu___353_1314.FStar_Tactics_Types.main_context);
           FStar_Tactics_Types.main_goal =
             (uu___353_1314.FStar_Tactics_Types.main_goal);
           FStar_Tactics_Types.all_implicits =
             (uu___353_1314.FStar_Tactics_Types.all_implicits);
           FStar_Tactics_Types.goals = uu____1315;
           FStar_Tactics_Types.smt_goals =
             (uu___353_1314.FStar_Tactics_Types.smt_goals);
           FStar_Tactics_Types.depth =
             (uu___353_1314.FStar_Tactics_Types.depth);
           FStar_Tactics_Types.__dump =
             (uu___353_1314.FStar_Tactics_Types.__dump);
           FStar_Tactics_Types.psc = (uu___353_1314.FStar_Tactics_Types.psc);
           FStar_Tactics_Types.entry_range =
             (uu___353_1314.FStar_Tactics_Types.entry_range);
           FStar_Tactics_Types.guard_policy =
             (uu___353_1314.FStar_Tactics_Types.guard_policy);
           FStar_Tactics_Types.freshness =
             (uu___353_1314.FStar_Tactics_Types.freshness);
           FStar_Tactics_Types.tac_verb_dbg =
             (uu___353_1314.FStar_Tactics_Types.tac_verb_dbg)
         }  in
       set ps')
  
let (set_solution :
  FStar_Tactics_Types.goal -> FStar_Syntax_Syntax.term -> unit tac) =
  fun goal  ->
    fun solution  ->
      let uu____1338 =
        FStar_Syntax_Unionfind.find
          (goal.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_head
         in
      match uu____1338 with
      | FStar_Pervasives_Native.Some uu____1343 ->
          let uu____1344 =
            let uu____1345 = goal_to_string_verbose goal  in
            FStar_Util.format1 "Goal %s is already solved" uu____1345  in
          fail uu____1344
      | FStar_Pervasives_Native.None  ->
          (FStar_Syntax_Unionfind.change
             (goal.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_head
             solution;
           ret ())
  
let (trysolve :
  FStar_Tactics_Types.goal -> FStar_Syntax_Syntax.term -> Prims.bool tac) =
  fun goal  ->
    fun solution  ->
      let uu____1361 = FStar_Tactics_Types.goal_env goal  in
      let uu____1362 = FStar_Tactics_Types.goal_witness goal  in
      do_unify uu____1361 solution uu____1362
  
let (__dismiss : unit tac) =
  bind get
    (fun p  ->
       let uu____1368 =
         let uu___354_1369 = p  in
         let uu____1370 = FStar_List.tl p.FStar_Tactics_Types.goals  in
         {
           FStar_Tactics_Types.main_context =
             (uu___354_1369.FStar_Tactics_Types.main_context);
           FStar_Tactics_Types.main_goal =
             (uu___354_1369.FStar_Tactics_Types.main_goal);
           FStar_Tactics_Types.all_implicits =
             (uu___354_1369.FStar_Tactics_Types.all_implicits);
           FStar_Tactics_Types.goals = uu____1370;
           FStar_Tactics_Types.smt_goals =
             (uu___354_1369.FStar_Tactics_Types.smt_goals);
           FStar_Tactics_Types.depth =
             (uu___354_1369.FStar_Tactics_Types.depth);
           FStar_Tactics_Types.__dump =
             (uu___354_1369.FStar_Tactics_Types.__dump);
           FStar_Tactics_Types.psc = (uu___354_1369.FStar_Tactics_Types.psc);
           FStar_Tactics_Types.entry_range =
             (uu___354_1369.FStar_Tactics_Types.entry_range);
           FStar_Tactics_Types.guard_policy =
             (uu___354_1369.FStar_Tactics_Types.guard_policy);
           FStar_Tactics_Types.freshness =
             (uu___354_1369.FStar_Tactics_Types.freshness);
           FStar_Tactics_Types.tac_verb_dbg =
             (uu___354_1369.FStar_Tactics_Types.tac_verb_dbg)
         }  in
       set uu____1368)
  
let (dismiss : unit -> unit tac) =
  fun uu____1379  ->
    bind get
      (fun p  ->
         match p.FStar_Tactics_Types.goals with
         | [] -> fail "dismiss: no more goals"
         | uu____1386 -> __dismiss)
  
let (solve :
  FStar_Tactics_Types.goal -> FStar_Syntax_Syntax.term -> unit tac) =
  fun goal  ->
    fun solution  ->
      let e = FStar_Tactics_Types.goal_env goal  in
      mlog
        (fun uu____1407  ->
           let uu____1408 =
             let uu____1409 = FStar_Tactics_Types.goal_witness goal  in
             FStar_Syntax_Print.term_to_string uu____1409  in
           let uu____1410 = FStar_Syntax_Print.term_to_string solution  in
           FStar_Util.print2 "solve %s := %s\n" uu____1408 uu____1410)
        (fun uu____1413  ->
           let uu____1414 = trysolve goal solution  in
           bind uu____1414
             (fun b  ->
                if b
                then bind __dismiss (fun uu____1422  -> remove_solved_goals)
                else
                  (let uu____1424 =
                     let uu____1425 =
                       let uu____1426 = FStar_Tactics_Types.goal_env goal  in
                       tts uu____1426 solution  in
                     let uu____1427 =
                       let uu____1428 = FStar_Tactics_Types.goal_env goal  in
                       let uu____1429 = FStar_Tactics_Types.goal_witness goal
                          in
                       tts uu____1428 uu____1429  in
                     let uu____1430 =
                       let uu____1431 = FStar_Tactics_Types.goal_env goal  in
                       let uu____1432 = FStar_Tactics_Types.goal_type goal
                          in
                       tts uu____1431 uu____1432  in
                     FStar_Util.format3 "%s does not solve %s : %s"
                       uu____1425 uu____1427 uu____1430
                      in
                   fail uu____1424)))
  
let (solve' :
  FStar_Tactics_Types.goal -> FStar_Syntax_Syntax.term -> unit tac) =
  fun goal  ->
    fun solution  ->
      let uu____1447 = set_solution goal solution  in
      bind uu____1447
        (fun uu____1451  ->
           bind __dismiss (fun uu____1453  -> remove_solved_goals))
  
let (dismiss_all : unit tac) =
  bind get
    (fun p  ->
       set
         (let uu___355_1460 = p  in
          {
            FStar_Tactics_Types.main_context =
              (uu___355_1460.FStar_Tactics_Types.main_context);
            FStar_Tactics_Types.main_goal =
              (uu___355_1460.FStar_Tactics_Types.main_goal);
            FStar_Tactics_Types.all_implicits =
              (uu___355_1460.FStar_Tactics_Types.all_implicits);
            FStar_Tactics_Types.goals = [];
            FStar_Tactics_Types.smt_goals =
              (uu___355_1460.FStar_Tactics_Types.smt_goals);
            FStar_Tactics_Types.depth =
              (uu___355_1460.FStar_Tactics_Types.depth);
            FStar_Tactics_Types.__dump =
              (uu___355_1460.FStar_Tactics_Types.__dump);
            FStar_Tactics_Types.psc = (uu___355_1460.FStar_Tactics_Types.psc);
            FStar_Tactics_Types.entry_range =
              (uu___355_1460.FStar_Tactics_Types.entry_range);
            FStar_Tactics_Types.guard_policy =
              (uu___355_1460.FStar_Tactics_Types.guard_policy);
            FStar_Tactics_Types.freshness =
              (uu___355_1460.FStar_Tactics_Types.freshness);
            FStar_Tactics_Types.tac_verb_dbg =
              (uu___355_1460.FStar_Tactics_Types.tac_verb_dbg)
          }))
  
let (nwarn : Prims.int FStar_ST.ref) =
  FStar_Util.mk_ref (Prims.parse_int "0") 
let (check_valid_goal : FStar_Tactics_Types.goal -> unit) =
  fun g  ->
    let uu____1479 = FStar_Options.defensive ()  in
    if uu____1479
    then
      let b = true  in
      let env = FStar_Tactics_Types.goal_env g  in
      let b1 =
        b &&
          (let uu____1484 = FStar_Tactics_Types.goal_witness g  in
           FStar_TypeChecker_Env.closed env uu____1484)
         in
      let b2 =
        b1 &&
          (let uu____1487 = FStar_Tactics_Types.goal_type g  in
           FStar_TypeChecker_Env.closed env uu____1487)
         in
      let rec aux b3 e =
        let uu____1499 = FStar_TypeChecker_Env.pop_bv e  in
        match uu____1499 with
        | FStar_Pervasives_Native.None  -> b3
        | FStar_Pervasives_Native.Some (bv,e1) ->
            let b4 =
              b3 &&
                (FStar_TypeChecker_Env.closed e1 bv.FStar_Syntax_Syntax.sort)
               in
            aux b4 e1
         in
      let uu____1517 =
        (let uu____1520 = aux b2 env  in Prims.op_Negation uu____1520) &&
          (let uu____1522 = FStar_ST.op_Bang nwarn  in
           uu____1522 < (Prims.parse_int "5"))
         in
      (if uu____1517
       then
         ((let uu____1543 =
             let uu____1544 = FStar_Tactics_Types.goal_type g  in
             uu____1544.FStar_Syntax_Syntax.pos  in
           let uu____1547 =
             let uu____1552 =
               let uu____1553 = goal_to_string_verbose g  in
               FStar_Util.format1
                 "The following goal is ill-formed. Keeping calm and carrying on...\n<%s>\n\n"
                 uu____1553
                in
             (FStar_Errors.Warning_IllFormedGoal, uu____1552)  in
           FStar_Errors.log_issue uu____1543 uu____1547);
          (let uu____1554 =
             let uu____1555 = FStar_ST.op_Bang nwarn  in
             uu____1555 + (Prims.parse_int "1")  in
           FStar_ST.op_Colon_Equals nwarn uu____1554))
       else ())
    else ()
  
let (add_goals : FStar_Tactics_Types.goal Prims.list -> unit tac) =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___356_1615 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___356_1615.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___356_1615.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___356_1615.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (FStar_List.append gs p.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (uu___356_1615.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___356_1615.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___356_1615.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___356_1615.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___356_1615.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___356_1615.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___356_1615.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___356_1615.FStar_Tactics_Types.tac_verb_dbg)
            }))
  
let (add_smt_goals : FStar_Tactics_Types.goal Prims.list -> unit tac) =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___357_1635 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___357_1635.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___357_1635.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___357_1635.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___357_1635.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (FStar_List.append gs p.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___357_1635.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___357_1635.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___357_1635.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___357_1635.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___357_1635.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___357_1635.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___357_1635.FStar_Tactics_Types.tac_verb_dbg)
            }))
  
let (push_goals : FStar_Tactics_Types.goal Prims.list -> unit tac) =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___358_1655 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___358_1655.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___358_1655.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___358_1655.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (FStar_List.append p.FStar_Tactics_Types.goals gs);
              FStar_Tactics_Types.smt_goals =
                (uu___358_1655.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___358_1655.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___358_1655.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___358_1655.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___358_1655.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___358_1655.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___358_1655.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___358_1655.FStar_Tactics_Types.tac_verb_dbg)
            }))
  
let (push_smt_goals : FStar_Tactics_Types.goal Prims.list -> unit tac) =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___359_1675 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___359_1675.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___359_1675.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___359_1675.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___359_1675.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (FStar_List.append p.FStar_Tactics_Types.smt_goals gs);
              FStar_Tactics_Types.depth =
                (uu___359_1675.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___359_1675.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___359_1675.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___359_1675.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___359_1675.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___359_1675.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___359_1675.FStar_Tactics_Types.tac_verb_dbg)
            }))
  
let (replace_cur : FStar_Tactics_Types.goal -> unit tac) =
  fun g  -> bind __dismiss (fun uu____1686  -> add_goals [g]) 
let (add_implicits : implicits -> unit tac) =
  fun i  ->
    bind get
      (fun p  ->
         set
           (let uu___360_1700 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___360_1700.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___360_1700.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (FStar_List.append i p.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___360_1700.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (uu___360_1700.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___360_1700.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___360_1700.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___360_1700.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___360_1700.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___360_1700.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___360_1700.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___360_1700.FStar_Tactics_Types.tac_verb_dbg)
            }))
  
let (new_uvar :
  Prims.string ->
    env ->
      FStar_Reflection_Data.typ ->
        (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.ctx_uvar)
          FStar_Pervasives_Native.tuple2 tac)
  =
  fun reason  ->
    fun env  ->
      fun typ  ->
        let uu____1728 =
          FStar_TypeChecker_Util.new_implicit_var reason
            typ.FStar_Syntax_Syntax.pos env typ
           in
        match uu____1728 with
        | (u,ctx_uvar,g_u) ->
            let uu____1762 =
              add_implicits g_u.FStar_TypeChecker_Env.implicits  in
            bind uu____1762
              (fun uu____1771  ->
                 let uu____1772 =
                   let uu____1777 =
                     let uu____1778 = FStar_List.hd ctx_uvar  in
                     FStar_Pervasives_Native.fst uu____1778  in
                   (u, uu____1777)  in
                 ret uu____1772)
  
let (is_true : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____1796 = FStar_Syntax_Util.un_squash t  in
    match uu____1796 with
    | FStar_Pervasives_Native.Some t' ->
        let uu____1806 =
          let uu____1807 = FStar_Syntax_Subst.compress t'  in
          uu____1807.FStar_Syntax_Syntax.n  in
        (match uu____1806 with
         | FStar_Syntax_Syntax.Tm_fvar fv ->
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.true_lid
         | uu____1811 -> false)
    | uu____1812 -> false
  
let (is_false : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____1822 = FStar_Syntax_Util.un_squash t  in
    match uu____1822 with
    | FStar_Pervasives_Native.Some t' ->
        let uu____1832 =
          let uu____1833 = FStar_Syntax_Subst.compress t'  in
          uu____1833.FStar_Syntax_Syntax.n  in
        (match uu____1832 with
         | FStar_Syntax_Syntax.Tm_fvar fv ->
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.false_lid
         | uu____1837 -> false)
    | uu____1838 -> false
  
let (cur_goal : unit -> FStar_Tactics_Types.goal tac) =
  fun uu____1849  ->
    bind get
      (fun p  ->
         match p.FStar_Tactics_Types.goals with
         | [] -> fail "No more goals (1)"
         | hd1::tl1 ->
             let uu____1860 =
               FStar_Syntax_Unionfind.find
                 (hd1.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_head
                in
             (match uu____1860 with
              | FStar_Pervasives_Native.None  -> ret hd1
              | FStar_Pervasives_Native.Some t ->
                  ((let uu____1867 = goal_to_string_verbose hd1  in
                    let uu____1868 = FStar_Syntax_Print.term_to_string t  in
                    FStar_Util.print2
                      "!!!!!!!!!!!! GOAL IS ALREADY SOLVED! %s\nsol is %s\n"
                      uu____1867 uu____1868);
                   ret hd1)))
  
let (tadmit : unit -> unit tac) =
  fun uu____1875  ->
    let uu____1878 =
      bind get
        (fun ps  ->
           let uu____1884 = cur_goal ()  in
           bind uu____1884
             (fun g  ->
                (let uu____1891 =
                   let uu____1892 = FStar_Tactics_Types.goal_type g  in
                   uu____1892.FStar_Syntax_Syntax.pos  in
                 let uu____1895 =
                   let uu____1900 =
                     let uu____1901 = goal_to_string ps g  in
                     FStar_Util.format1 "Tactics admitted goal <%s>\n\n"
                       uu____1901
                      in
                   (FStar_Errors.Warning_TacAdmit, uu____1900)  in
                 FStar_Errors.log_issue uu____1891 uu____1895);
                solve' g FStar_Syntax_Util.exp_unit))
       in
    FStar_All.pipe_left (wrap_err "tadmit") uu____1878
  
let (fresh : unit -> FStar_BigInt.t tac) =
  fun uu____1912  ->
    bind get
      (fun ps  ->
         let n1 = ps.FStar_Tactics_Types.freshness  in
         let ps1 =
           let uu___361_1922 = ps  in
           {
             FStar_Tactics_Types.main_context =
               (uu___361_1922.FStar_Tactics_Types.main_context);
             FStar_Tactics_Types.main_goal =
               (uu___361_1922.FStar_Tactics_Types.main_goal);
             FStar_Tactics_Types.all_implicits =
               (uu___361_1922.FStar_Tactics_Types.all_implicits);
             FStar_Tactics_Types.goals =
               (uu___361_1922.FStar_Tactics_Types.goals);
             FStar_Tactics_Types.smt_goals =
               (uu___361_1922.FStar_Tactics_Types.smt_goals);
             FStar_Tactics_Types.depth =
               (uu___361_1922.FStar_Tactics_Types.depth);
             FStar_Tactics_Types.__dump =
               (uu___361_1922.FStar_Tactics_Types.__dump);
             FStar_Tactics_Types.psc =
               (uu___361_1922.FStar_Tactics_Types.psc);
             FStar_Tactics_Types.entry_range =
               (uu___361_1922.FStar_Tactics_Types.entry_range);
             FStar_Tactics_Types.guard_policy =
               (uu___361_1922.FStar_Tactics_Types.guard_policy);
             FStar_Tactics_Types.freshness = (n1 + (Prims.parse_int "1"));
             FStar_Tactics_Types.tac_verb_dbg =
               (uu___361_1922.FStar_Tactics_Types.tac_verb_dbg)
           }  in
         let uu____1923 = set ps1  in
         bind uu____1923
           (fun uu____1928  ->
              let uu____1929 = FStar_BigInt.of_int_fs n1  in ret uu____1929))
  
let (ngoals : unit -> FStar_BigInt.t tac) =
  fun uu____1936  ->
    bind get
      (fun ps  ->
         let n1 = FStar_List.length ps.FStar_Tactics_Types.goals  in
         let uu____1944 = FStar_BigInt.of_int_fs n1  in ret uu____1944)
  
let (ngoals_smt : unit -> FStar_BigInt.t tac) =
  fun uu____1957  ->
    bind get
      (fun ps  ->
         let n1 = FStar_List.length ps.FStar_Tactics_Types.smt_goals  in
         let uu____1965 = FStar_BigInt.of_int_fs n1  in ret uu____1965)
  
let (is_guard : unit -> Prims.bool tac) =
  fun uu____1978  ->
    let uu____1981 = cur_goal ()  in
    bind uu____1981 (fun g  -> ret g.FStar_Tactics_Types.is_guard)
  
let (mk_irrelevant_goal :
  Prims.string ->
    env ->
      FStar_Reflection_Data.typ ->
        FStar_Options.optionstate -> FStar_Tactics_Types.goal tac)
  =
  fun reason  ->
    fun env  ->
      fun phi  ->
        fun opts  ->
          let typ =
            let uu____2013 = env.FStar_TypeChecker_Env.universe_of env phi
               in
            FStar_Syntax_Util.mk_squash uu____2013 phi  in
          let uu____2014 = new_uvar reason env typ  in
          bind uu____2014
            (fun uu____2029  ->
               match uu____2029 with
               | (uu____2036,ctx_uvar) ->
                   let goal =
                     FStar_Tactics_Types.mk_goal env ctx_uvar opts false  in
                   ret goal)
  
let (__tc :
  env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term,FStar_Reflection_Data.typ,FStar_TypeChecker_Env.guard_t)
        FStar_Pervasives_Native.tuple3 tac)
  =
  fun e  ->
    fun t  ->
      bind get
        (fun ps  ->
           mlog
             (fun uu____2081  ->
                let uu____2082 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.print1 "Tac> __tc(%s)\n" uu____2082)
             (fun uu____2085  ->
                let e1 =
                  let uu___362_2087 = e  in
                  {
                    FStar_TypeChecker_Env.solver =
                      (uu___362_2087.FStar_TypeChecker_Env.solver);
                    FStar_TypeChecker_Env.range =
                      (uu___362_2087.FStar_TypeChecker_Env.range);
                    FStar_TypeChecker_Env.curmodule =
                      (uu___362_2087.FStar_TypeChecker_Env.curmodule);
                    FStar_TypeChecker_Env.gamma =
                      (uu___362_2087.FStar_TypeChecker_Env.gamma);
                    FStar_TypeChecker_Env.gamma_sig =
                      (uu___362_2087.FStar_TypeChecker_Env.gamma_sig);
                    FStar_TypeChecker_Env.gamma_cache =
                      (uu___362_2087.FStar_TypeChecker_Env.gamma_cache);
                    FStar_TypeChecker_Env.modules =
                      (uu___362_2087.FStar_TypeChecker_Env.modules);
                    FStar_TypeChecker_Env.expected_typ =
                      (uu___362_2087.FStar_TypeChecker_Env.expected_typ);
                    FStar_TypeChecker_Env.sigtab =
                      (uu___362_2087.FStar_TypeChecker_Env.sigtab);
                    FStar_TypeChecker_Env.attrtab =
                      (uu___362_2087.FStar_TypeChecker_Env.attrtab);
                    FStar_TypeChecker_Env.is_pattern =
                      (uu___362_2087.FStar_TypeChecker_Env.is_pattern);
                    FStar_TypeChecker_Env.instantiate_imp =
                      (uu___362_2087.FStar_TypeChecker_Env.instantiate_imp);
                    FStar_TypeChecker_Env.effects =
                      (uu___362_2087.FStar_TypeChecker_Env.effects);
                    FStar_TypeChecker_Env.generalize =
                      (uu___362_2087.FStar_TypeChecker_Env.generalize);
                    FStar_TypeChecker_Env.letrecs =
                      (uu___362_2087.FStar_TypeChecker_Env.letrecs);
                    FStar_TypeChecker_Env.top_level =
                      (uu___362_2087.FStar_TypeChecker_Env.top_level);
                    FStar_TypeChecker_Env.check_uvars =
                      (uu___362_2087.FStar_TypeChecker_Env.check_uvars);
                    FStar_TypeChecker_Env.use_eq =
                      (uu___362_2087.FStar_TypeChecker_Env.use_eq);
                    FStar_TypeChecker_Env.is_iface =
                      (uu___362_2087.FStar_TypeChecker_Env.is_iface);
                    FStar_TypeChecker_Env.admit =
                      (uu___362_2087.FStar_TypeChecker_Env.admit);
                    FStar_TypeChecker_Env.lax =
                      (uu___362_2087.FStar_TypeChecker_Env.lax);
                    FStar_TypeChecker_Env.lax_universes =
                      (uu___362_2087.FStar_TypeChecker_Env.lax_universes);
                    FStar_TypeChecker_Env.phase1 =
                      (uu___362_2087.FStar_TypeChecker_Env.phase1);
                    FStar_TypeChecker_Env.failhard =
                      (uu___362_2087.FStar_TypeChecker_Env.failhard);
                    FStar_TypeChecker_Env.nosynth =
                      (uu___362_2087.FStar_TypeChecker_Env.nosynth);
                    FStar_TypeChecker_Env.uvar_subtyping = false;
                    FStar_TypeChecker_Env.tc_term =
                      (uu___362_2087.FStar_TypeChecker_Env.tc_term);
                    FStar_TypeChecker_Env.type_of =
                      (uu___362_2087.FStar_TypeChecker_Env.type_of);
                    FStar_TypeChecker_Env.universe_of =
                      (uu___362_2087.FStar_TypeChecker_Env.universe_of);
                    FStar_TypeChecker_Env.check_type_of =
                      (uu___362_2087.FStar_TypeChecker_Env.check_type_of);
                    FStar_TypeChecker_Env.use_bv_sorts =
                      (uu___362_2087.FStar_TypeChecker_Env.use_bv_sorts);
                    FStar_TypeChecker_Env.qtbl_name_and_index =
                      (uu___362_2087.FStar_TypeChecker_Env.qtbl_name_and_index);
                    FStar_TypeChecker_Env.normalized_eff_names =
                      (uu___362_2087.FStar_TypeChecker_Env.normalized_eff_names);
                    FStar_TypeChecker_Env.proof_ns =
                      (uu___362_2087.FStar_TypeChecker_Env.proof_ns);
                    FStar_TypeChecker_Env.synth_hook =
                      (uu___362_2087.FStar_TypeChecker_Env.synth_hook);
                    FStar_TypeChecker_Env.splice =
                      (uu___362_2087.FStar_TypeChecker_Env.splice);
                    FStar_TypeChecker_Env.is_native_tactic =
                      (uu___362_2087.FStar_TypeChecker_Env.is_native_tactic);
                    FStar_TypeChecker_Env.identifier_info =
                      (uu___362_2087.FStar_TypeChecker_Env.identifier_info);
                    FStar_TypeChecker_Env.tc_hooks =
                      (uu___362_2087.FStar_TypeChecker_Env.tc_hooks);
                    FStar_TypeChecker_Env.dsenv =
                      (uu___362_2087.FStar_TypeChecker_Env.dsenv);
                    FStar_TypeChecker_Env.dep_graph =
                      (uu___362_2087.FStar_TypeChecker_Env.dep_graph)
                  }  in
                try
                  let uu____2107 =
                    (ps.FStar_Tactics_Types.main_context).FStar_TypeChecker_Env.type_of
                      e1 t
                     in
                  ret uu____2107
                with
                | FStar_Errors.Err (uu____2134,msg) ->
                    let uu____2136 = tts e1 t  in
                    let uu____2137 =
                      let uu____2138 = FStar_TypeChecker_Env.all_binders e1
                         in
                      FStar_All.pipe_right uu____2138
                        (FStar_Syntax_Print.binders_to_string ", ")
                       in
                    fail3 "Cannot type %s in context (%s). Error = (%s)"
                      uu____2136 uu____2137 msg
                | FStar_Errors.Error (uu____2145,msg,uu____2147) ->
                    let uu____2148 = tts e1 t  in
                    let uu____2149 =
                      let uu____2150 = FStar_TypeChecker_Env.all_binders e1
                         in
                      FStar_All.pipe_right uu____2150
                        (FStar_Syntax_Print.binders_to_string ", ")
                       in
                    fail3 "Cannot type %s in context (%s). Error = (%s)"
                      uu____2148 uu____2149 msg))
  
let (istrivial : env -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun e  ->
    fun t  ->
      let steps =
        [FStar_TypeChecker_Normalize.Reify;
        FStar_TypeChecker_Normalize.UnfoldUntil
          FStar_Syntax_Syntax.delta_constant;
        FStar_TypeChecker_Normalize.Primops;
        FStar_TypeChecker_Normalize.Simplify;
        FStar_TypeChecker_Normalize.UnfoldTac;
        FStar_TypeChecker_Normalize.Unmeta]  in
      let t1 = normalize steps e t  in is_true t1
  
let (get_guard_policy : unit -> FStar_Tactics_Types.guard_policy tac) =
  fun uu____2177  ->
    bind get (fun ps  -> ret ps.FStar_Tactics_Types.guard_policy)
  
let (set_guard_policy : FStar_Tactics_Types.guard_policy -> unit tac) =
  fun pol  ->
    bind get
      (fun ps  ->
         set
           (let uu___365_2195 = ps  in
            {
              FStar_Tactics_Types.main_context =
                (uu___365_2195.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___365_2195.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___365_2195.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___365_2195.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (uu___365_2195.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___365_2195.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___365_2195.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___365_2195.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___365_2195.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy = pol;
              FStar_Tactics_Types.freshness =
                (uu___365_2195.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___365_2195.FStar_Tactics_Types.tac_verb_dbg)
            }))
  
let with_policy : 'a . FStar_Tactics_Types.guard_policy -> 'a tac -> 'a tac =
  fun pol  ->
    fun t  ->
      let uu____2219 = get_guard_policy ()  in
      bind uu____2219
        (fun old_pol  ->
           let uu____2225 = set_guard_policy pol  in
           bind uu____2225
             (fun uu____2229  ->
                bind t
                  (fun r  ->
                     let uu____2233 = set_guard_policy old_pol  in
                     bind uu____2233 (fun uu____2237  -> ret r))))
  
let (getopts : FStar_Options.optionstate tac) =
  let uu____2240 = let uu____2245 = cur_goal ()  in trytac uu____2245  in
  bind uu____2240
    (fun uu___338_2252  ->
       match uu___338_2252 with
       | FStar_Pervasives_Native.Some g -> ret g.FStar_Tactics_Types.opts
       | FStar_Pervasives_Native.None  ->
           let uu____2258 = FStar_Options.peek ()  in ret uu____2258)
  
let (proc_guard :
  Prims.string -> env -> FStar_TypeChecker_Env.guard_t -> unit tac) =
  fun reason  ->
    fun e  ->
      fun g  ->
        bind getopts
          (fun opts  ->
             let uu____2281 =
               let uu____2282 = FStar_TypeChecker_Rel.simplify_guard e g  in
               uu____2282.FStar_TypeChecker_Env.guard_f  in
             match uu____2281 with
             | FStar_TypeChecker_Common.Trivial  -> ret ()
             | FStar_TypeChecker_Common.NonTrivial f ->
                 let uu____2286 = istrivial e f  in
                 if uu____2286
                 then ret ()
                 else
                   bind get
                     (fun ps  ->
                        match ps.FStar_Tactics_Types.guard_policy with
                        | FStar_Tactics_Types.Drop  -> ret ()
                        | FStar_Tactics_Types.Goal  ->
                            let uu____2294 =
                              mk_irrelevant_goal reason e f opts  in
                            bind uu____2294
                              (fun goal  ->
                                 let goal1 =
                                   let uu___366_2301 = goal  in
                                   {
                                     FStar_Tactics_Types.goal_main_env =
                                       (uu___366_2301.FStar_Tactics_Types.goal_main_env);
                                     FStar_Tactics_Types.goal_ctx_uvar =
                                       (uu___366_2301.FStar_Tactics_Types.goal_ctx_uvar);
                                     FStar_Tactics_Types.opts =
                                       (uu___366_2301.FStar_Tactics_Types.opts);
                                     FStar_Tactics_Types.is_guard = true
                                   }  in
                                 push_goals [goal1])
                        | FStar_Tactics_Types.SMT  ->
                            let uu____2302 =
                              mk_irrelevant_goal reason e f opts  in
                            bind uu____2302
                              (fun goal  ->
                                 let goal1 =
                                   let uu___367_2309 = goal  in
                                   {
                                     FStar_Tactics_Types.goal_main_env =
                                       (uu___367_2309.FStar_Tactics_Types.goal_main_env);
                                     FStar_Tactics_Types.goal_ctx_uvar =
                                       (uu___367_2309.FStar_Tactics_Types.goal_ctx_uvar);
                                     FStar_Tactics_Types.opts =
                                       (uu___367_2309.FStar_Tactics_Types.opts);
                                     FStar_Tactics_Types.is_guard = true
                                   }  in
                                 push_smt_goals [goal1])
                        | FStar_Tactics_Types.Force  ->
                            (try
                               let uu____2317 =
                                 let uu____2318 =
                                   let uu____2319 =
                                     FStar_TypeChecker_Rel.discharge_guard_no_smt
                                       e g
                                      in
                                   FStar_All.pipe_left
                                     FStar_TypeChecker_Env.is_trivial
                                     uu____2319
                                    in
                                 Prims.op_Negation uu____2318  in
                               if uu____2317
                               then
                                 mlog
                                   (fun uu____2324  ->
                                      let uu____2325 =
                                        FStar_TypeChecker_Rel.guard_to_string
                                          e g
                                         in
                                      FStar_Util.print1 "guard = %s\n"
                                        uu____2325)
                                   (fun uu____2327  ->
                                      fail1 "Forcing the guard failed %s)"
                                        reason)
                               else ret ()
                             with
                             | uu____2334 ->
                                 mlog
                                   (fun uu____2337  ->
                                      let uu____2338 =
                                        FStar_TypeChecker_Rel.guard_to_string
                                          e g
                                         in
                                      FStar_Util.print1 "guard = %s\n"
                                        uu____2338)
                                   (fun uu____2340  ->
                                      fail1 "Forcing the guard failed (%s)"
                                        reason))))
  
let (tc : FStar_Syntax_Syntax.term -> FStar_Reflection_Data.typ tac) =
  fun t  ->
    let uu____2350 =
      let uu____2353 = cur_goal ()  in
      bind uu____2353
        (fun goal  ->
           let uu____2359 =
             let uu____2368 = FStar_Tactics_Types.goal_env goal  in
             __tc uu____2368 t  in
           bind uu____2359
             (fun uu____2380  ->
                match uu____2380 with
                | (t1,typ,guard) ->
                    let uu____2392 =
                      let uu____2395 = FStar_Tactics_Types.goal_env goal  in
                      proc_guard "tc" uu____2395 guard  in
                    bind uu____2392 (fun uu____2397  -> ret typ)))
       in
    FStar_All.pipe_left (wrap_err "tc") uu____2350
  
let (add_irrelevant_goal :
  Prims.string ->
    env -> FStar_Reflection_Data.typ -> FStar_Options.optionstate -> unit tac)
  =
  fun reason  ->
    fun env  ->
      fun phi  ->
        fun opts  ->
          let uu____2426 = mk_irrelevant_goal reason env phi opts  in
          bind uu____2426 (fun goal  -> add_goals [goal])
  
let (trivial : unit -> unit tac) =
  fun uu____2437  ->
    let uu____2440 = cur_goal ()  in
    bind uu____2440
      (fun goal  ->
         let uu____2446 =
           let uu____2447 = FStar_Tactics_Types.goal_env goal  in
           let uu____2448 = FStar_Tactics_Types.goal_type goal  in
           istrivial uu____2447 uu____2448  in
         if uu____2446
         then solve' goal FStar_Syntax_Util.exp_unit
         else
           (let uu____2452 =
              let uu____2453 = FStar_Tactics_Types.goal_env goal  in
              let uu____2454 = FStar_Tactics_Types.goal_type goal  in
              tts uu____2453 uu____2454  in
            fail1 "Not a trivial goal: %s" uu____2452))
  
let (goal_from_guard :
  Prims.string ->
    env ->
      FStar_TypeChecker_Env.guard_t ->
        FStar_Options.optionstate ->
          FStar_Tactics_Types.goal FStar_Pervasives_Native.option tac)
  =
  fun reason  ->
    fun e  ->
      fun g  ->
        fun opts  ->
          let uu____2483 =
            let uu____2484 = FStar_TypeChecker_Rel.simplify_guard e g  in
            uu____2484.FStar_TypeChecker_Env.guard_f  in
          match uu____2483 with
          | FStar_TypeChecker_Common.Trivial  ->
              ret FStar_Pervasives_Native.None
          | FStar_TypeChecker_Common.NonTrivial f ->
              let uu____2492 = istrivial e f  in
              if uu____2492
              then ret FStar_Pervasives_Native.None
              else
                (let uu____2500 = mk_irrelevant_goal reason e f opts  in
                 bind uu____2500
                   (fun goal  ->
                      ret
                        (FStar_Pervasives_Native.Some
                           (let uu___370_2510 = goal  in
                            {
                              FStar_Tactics_Types.goal_main_env =
                                (uu___370_2510.FStar_Tactics_Types.goal_main_env);
                              FStar_Tactics_Types.goal_ctx_uvar =
                                (uu___370_2510.FStar_Tactics_Types.goal_ctx_uvar);
                              FStar_Tactics_Types.opts =
                                (uu___370_2510.FStar_Tactics_Types.opts);
                              FStar_Tactics_Types.is_guard = true
                            }))))
  
let (smt : unit -> unit tac) =
  fun uu____2517  ->
    let uu____2520 = cur_goal ()  in
    bind uu____2520
      (fun g  ->
         let uu____2526 = is_irrelevant g  in
         if uu____2526
         then bind __dismiss (fun uu____2530  -> add_smt_goals [g])
         else
           (let uu____2532 =
              let uu____2533 = FStar_Tactics_Types.goal_env g  in
              let uu____2534 = FStar_Tactics_Types.goal_type g  in
              tts uu____2533 uu____2534  in
            fail1 "goal is not irrelevant: cannot dispatch to smt (%s)"
              uu____2532))
  
let divide :
  'a 'b .
    FStar_BigInt.t ->
      'a tac -> 'b tac -> ('a,'b) FStar_Pervasives_Native.tuple2 tac
  =
  fun n1  ->
    fun l  ->
      fun r  ->
        bind get
          (fun p  ->
             let uu____2583 =
               try
                 let uu____2617 =
                   let uu____2626 = FStar_BigInt.to_int_fs n1  in
                   FStar_List.splitAt uu____2626 p.FStar_Tactics_Types.goals
                    in
                 ret uu____2617
               with | uu____2648 -> fail "divide: not enough goals"  in
             bind uu____2583
               (fun uu____2674  ->
                  match uu____2674 with
                  | (lgs,rgs) ->
                      let lp =
                        let uu___371_2700 = p  in
                        {
                          FStar_Tactics_Types.main_context =
                            (uu___371_2700.FStar_Tactics_Types.main_context);
                          FStar_Tactics_Types.main_goal =
                            (uu___371_2700.FStar_Tactics_Types.main_goal);
                          FStar_Tactics_Types.all_implicits =
                            (uu___371_2700.FStar_Tactics_Types.all_implicits);
                          FStar_Tactics_Types.goals = lgs;
                          FStar_Tactics_Types.smt_goals = [];
                          FStar_Tactics_Types.depth =
                            (uu___371_2700.FStar_Tactics_Types.depth);
                          FStar_Tactics_Types.__dump =
                            (uu___371_2700.FStar_Tactics_Types.__dump);
                          FStar_Tactics_Types.psc =
                            (uu___371_2700.FStar_Tactics_Types.psc);
                          FStar_Tactics_Types.entry_range =
                            (uu___371_2700.FStar_Tactics_Types.entry_range);
                          FStar_Tactics_Types.guard_policy =
                            (uu___371_2700.FStar_Tactics_Types.guard_policy);
                          FStar_Tactics_Types.freshness =
                            (uu___371_2700.FStar_Tactics_Types.freshness);
                          FStar_Tactics_Types.tac_verb_dbg =
                            (uu___371_2700.FStar_Tactics_Types.tac_verb_dbg)
                        }  in
                      let uu____2701 = set lp  in
                      bind uu____2701
                        (fun uu____2709  ->
                           bind l
                             (fun a  ->
                                bind get
                                  (fun lp'  ->
                                     let rp =
                                       let uu___372_2725 = lp'  in
                                       {
                                         FStar_Tactics_Types.main_context =
                                           (uu___372_2725.FStar_Tactics_Types.main_context);
                                         FStar_Tactics_Types.main_goal =
                                           (uu___372_2725.FStar_Tactics_Types.main_goal);
                                         FStar_Tactics_Types.all_implicits =
                                           (uu___372_2725.FStar_Tactics_Types.all_implicits);
                                         FStar_Tactics_Types.goals = rgs;
                                         FStar_Tactics_Types.smt_goals = [];
                                         FStar_Tactics_Types.depth =
                                           (uu___372_2725.FStar_Tactics_Types.depth);
                                         FStar_Tactics_Types.__dump =
                                           (uu___372_2725.FStar_Tactics_Types.__dump);
                                         FStar_Tactics_Types.psc =
                                           (uu___372_2725.FStar_Tactics_Types.psc);
                                         FStar_Tactics_Types.entry_range =
                                           (uu___372_2725.FStar_Tactics_Types.entry_range);
                                         FStar_Tactics_Types.guard_policy =
                                           (uu___372_2725.FStar_Tactics_Types.guard_policy);
                                         FStar_Tactics_Types.freshness =
                                           (uu___372_2725.FStar_Tactics_Types.freshness);
                                         FStar_Tactics_Types.tac_verb_dbg =
                                           (uu___372_2725.FStar_Tactics_Types.tac_verb_dbg)
                                       }  in
                                     let uu____2726 = set rp  in
                                     bind uu____2726
                                       (fun uu____2734  ->
                                          bind r
                                            (fun b  ->
                                               bind get
                                                 (fun rp'  ->
                                                    let p' =
                                                      let uu___373_2750 = rp'
                                                         in
                                                      {
                                                        FStar_Tactics_Types.main_context
                                                          =
                                                          (uu___373_2750.FStar_Tactics_Types.main_context);
                                                        FStar_Tactics_Types.main_goal
                                                          =
                                                          (uu___373_2750.FStar_Tactics_Types.main_goal);
                                                        FStar_Tactics_Types.all_implicits
                                                          =
                                                          (uu___373_2750.FStar_Tactics_Types.all_implicits);
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
                                                          (uu___373_2750.FStar_Tactics_Types.depth);
                                                        FStar_Tactics_Types.__dump
                                                          =
                                                          (uu___373_2750.FStar_Tactics_Types.__dump);
                                                        FStar_Tactics_Types.psc
                                                          =
                                                          (uu___373_2750.FStar_Tactics_Types.psc);
                                                        FStar_Tactics_Types.entry_range
                                                          =
                                                          (uu___373_2750.FStar_Tactics_Types.entry_range);
                                                        FStar_Tactics_Types.guard_policy
                                                          =
                                                          (uu___373_2750.FStar_Tactics_Types.guard_policy);
                                                        FStar_Tactics_Types.freshness
                                                          =
                                                          (uu___373_2750.FStar_Tactics_Types.freshness);
                                                        FStar_Tactics_Types.tac_verb_dbg
                                                          =
                                                          (uu___373_2750.FStar_Tactics_Types.tac_verb_dbg)
                                                      }  in
                                                    let uu____2751 = set p'
                                                       in
                                                    bind uu____2751
                                                      (fun uu____2759  ->
                                                         bind
                                                           remove_solved_goals
                                                           (fun uu____2765 
                                                              -> ret (a, b)))))))))))
  
let focus : 'a . 'a tac -> 'a tac =
  fun f  ->
    let uu____2786 = divide FStar_BigInt.one f idtac  in
    bind uu____2786
      (fun uu____2799  -> match uu____2799 with | (a,()) -> ret a)
  
let rec map : 'a . 'a tac -> 'a Prims.list tac =
  fun tau  ->
    bind get
      (fun p  ->
         match p.FStar_Tactics_Types.goals with
         | [] -> ret []
         | uu____2836::uu____2837 ->
             let uu____2840 =
               let uu____2849 = map tau  in
               divide FStar_BigInt.one tau uu____2849  in
             bind uu____2840
               (fun uu____2867  ->
                  match uu____2867 with | (h,t) -> ret (h :: t)))
  
let (seq : unit tac -> unit tac -> unit tac) =
  fun t1  ->
    fun t2  ->
      let uu____2908 =
        bind t1
          (fun uu____2913  ->
             let uu____2914 = map t2  in
             bind uu____2914 (fun uu____2922  -> ret ()))
         in
      focus uu____2908
  
let (intro : unit -> FStar_Syntax_Syntax.binder tac) =
  fun uu____2931  ->
    let uu____2934 =
      let uu____2937 = cur_goal ()  in
      bind uu____2937
        (fun goal  ->
           let uu____2946 =
             let uu____2953 = FStar_Tactics_Types.goal_type goal  in
             FStar_Syntax_Util.arrow_one uu____2953  in
           match uu____2946 with
           | FStar_Pervasives_Native.Some (b,c) ->
               let uu____2962 =
                 let uu____2963 = FStar_Syntax_Util.is_total_comp c  in
                 Prims.op_Negation uu____2963  in
               if uu____2962
               then fail "Codomain is effectful"
               else
                 (let env' =
                    let uu____2968 = FStar_Tactics_Types.goal_env goal  in
                    FStar_TypeChecker_Env.push_binders uu____2968 [b]  in
                  let typ' = comp_to_typ c  in
                  let uu____2982 = new_uvar "intro" env' typ'  in
                  bind uu____2982
                    (fun uu____2998  ->
                       match uu____2998 with
                       | (body,ctx_uvar) ->
                           let sol =
                             FStar_Syntax_Util.abs [b] body
                               FStar_Pervasives_Native.None
                              in
                           let uu____3022 = set_solution goal sol  in
                           bind uu____3022
                             (fun uu____3028  ->
                                let g =
                                  FStar_Tactics_Types.mk_goal env' ctx_uvar
                                    goal.FStar_Tactics_Types.opts
                                    goal.FStar_Tactics_Types.is_guard
                                   in
                                let uu____3030 =
                                  let uu____3033 = bnorm_goal g  in
                                  replace_cur uu____3033  in
                                bind uu____3030 (fun uu____3035  -> ret b))))
           | FStar_Pervasives_Native.None  ->
               let uu____3040 =
                 let uu____3041 = FStar_Tactics_Types.goal_env goal  in
                 let uu____3042 = FStar_Tactics_Types.goal_type goal  in
                 tts uu____3041 uu____3042  in
               fail1 "goal is not an arrow (%s)" uu____3040)
       in
    FStar_All.pipe_left (wrap_err "intro") uu____2934
  
let (intro_rec :
  unit ->
    (FStar_Syntax_Syntax.binder,FStar_Syntax_Syntax.binder)
      FStar_Pervasives_Native.tuple2 tac)
  =
  fun uu____3057  ->
    let uu____3064 = cur_goal ()  in
    bind uu____3064
      (fun goal  ->
         FStar_Util.print_string
           "WARNING (intro_rec): calling this is known to cause normalizer loops\n";
         FStar_Util.print_string
           "WARNING (intro_rec): proceed at your own risk...\n";
         (let uu____3081 =
            let uu____3088 = FStar_Tactics_Types.goal_type goal  in
            FStar_Syntax_Util.arrow_one uu____3088  in
          match uu____3081 with
          | FStar_Pervasives_Native.Some (b,c) ->
              let uu____3101 =
                let uu____3102 = FStar_Syntax_Util.is_total_comp c  in
                Prims.op_Negation uu____3102  in
              if uu____3101
              then fail "Codomain is effectful"
              else
                (let bv =
                   let uu____3115 = FStar_Tactics_Types.goal_type goal  in
                   FStar_Syntax_Syntax.gen_bv "__recf"
                     FStar_Pervasives_Native.None uu____3115
                    in
                 let bs =
                   let uu____3125 = FStar_Syntax_Syntax.mk_binder bv  in
                   [uu____3125; b]  in
                 let env' =
                   let uu____3151 = FStar_Tactics_Types.goal_env goal  in
                   FStar_TypeChecker_Env.push_binders uu____3151 bs  in
                 let uu____3152 =
                   let uu____3159 = comp_to_typ c  in
                   new_uvar "intro_rec" env' uu____3159  in
                 bind uu____3152
                   (fun uu____3178  ->
                      match uu____3178 with
                      | (u,ctx_uvar_u) ->
                          let lb =
                            let uu____3192 =
                              FStar_Tactics_Types.goal_type goal  in
                            let uu____3195 =
                              FStar_Syntax_Util.abs [b] u
                                FStar_Pervasives_Native.None
                               in
                            FStar_Syntax_Util.mk_letbinding
                              (FStar_Util.Inl bv) [] uu____3192
                              FStar_Parser_Const.effect_Tot_lid uu____3195 []
                              FStar_Range.dummyRange
                             in
                          let body = FStar_Syntax_Syntax.bv_to_name bv  in
                          let uu____3213 =
                            FStar_Syntax_Subst.close_let_rec [lb] body  in
                          (match uu____3213 with
                           | (lbs,body1) ->
                               let tm =
                                 let uu____3235 =
                                   let uu____3236 =
                                     FStar_Tactics_Types.goal_witness goal
                                      in
                                   uu____3236.FStar_Syntax_Syntax.pos  in
                                 FStar_Syntax_Syntax.mk
                                   (FStar_Syntax_Syntax.Tm_let
                                      ((true, lbs), body1))
                                   FStar_Pervasives_Native.None uu____3235
                                  in
                               let uu____3249 = set_solution goal tm  in
                               bind uu____3249
                                 (fun uu____3258  ->
                                    let uu____3259 =
                                      let uu____3262 =
                                        bnorm_goal
                                          (let uu___376_3265 = goal  in
                                           {
                                             FStar_Tactics_Types.goal_main_env
                                               =
                                               (uu___376_3265.FStar_Tactics_Types.goal_main_env);
                                             FStar_Tactics_Types.goal_ctx_uvar
                                               = ctx_uvar_u;
                                             FStar_Tactics_Types.opts =
                                               (uu___376_3265.FStar_Tactics_Types.opts);
                                             FStar_Tactics_Types.is_guard =
                                               (uu___376_3265.FStar_Tactics_Types.is_guard)
                                           })
                                         in
                                      replace_cur uu____3262  in
                                    bind uu____3259
                                      (fun uu____3272  ->
                                         let uu____3273 =
                                           let uu____3278 =
                                             FStar_Syntax_Syntax.mk_binder bv
                                              in
                                           (uu____3278, b)  in
                                         ret uu____3273)))))
          | FStar_Pervasives_Native.None  ->
              let uu____3287 =
                let uu____3288 = FStar_Tactics_Types.goal_env goal  in
                let uu____3289 = FStar_Tactics_Types.goal_type goal  in
                tts uu____3288 uu____3289  in
              fail1 "intro_rec: goal is not an arrow (%s)" uu____3287))
  
let (norm : FStar_Syntax_Embeddings.norm_step Prims.list -> unit tac) =
  fun s  ->
    let uu____3307 = cur_goal ()  in
    bind uu____3307
      (fun goal  ->
         mlog
           (fun uu____3314  ->
              let uu____3315 =
                let uu____3316 = FStar_Tactics_Types.goal_witness goal  in
                FStar_Syntax_Print.term_to_string uu____3316  in
              FStar_Util.print1 "norm: witness = %s\n" uu____3315)
           (fun uu____3321  ->
              let steps =
                let uu____3325 = FStar_TypeChecker_Normalize.tr_norm_steps s
                   in
                FStar_List.append
                  [FStar_TypeChecker_Normalize.Reify;
                  FStar_TypeChecker_Normalize.UnfoldTac] uu____3325
                 in
              let t =
                let uu____3329 = FStar_Tactics_Types.goal_env goal  in
                let uu____3330 = FStar_Tactics_Types.goal_type goal  in
                normalize steps uu____3329 uu____3330  in
              let uu____3331 = FStar_Tactics_Types.goal_with_type goal t  in
              replace_cur uu____3331))
  
let (norm_term_env :
  env ->
    FStar_Syntax_Embeddings.norm_step Prims.list ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term tac)
  =
  fun e  ->
    fun s  ->
      fun t  ->
        let uu____3355 =
          mlog
            (fun uu____3360  ->
               let uu____3361 = FStar_Syntax_Print.term_to_string t  in
               FStar_Util.print1 "norm_term: tm = %s\n" uu____3361)
            (fun uu____3363  ->
               bind get
                 (fun ps  ->
                    let opts =
                      match ps.FStar_Tactics_Types.goals with
                      | g::uu____3369 -> g.FStar_Tactics_Types.opts
                      | uu____3372 -> FStar_Options.peek ()  in
                    mlog
                      (fun uu____3377  ->
                         let uu____3378 = FStar_Syntax_Print.term_to_string t
                            in
                         FStar_Util.print1 "norm_term_env: t = %s\n"
                           uu____3378)
                      (fun uu____3381  ->
                         let uu____3382 = __tc e t  in
                         bind uu____3382
                           (fun uu____3403  ->
                              match uu____3403 with
                              | (t1,uu____3413,uu____3414) ->
                                  let steps =
                                    let uu____3418 =
                                      FStar_TypeChecker_Normalize.tr_norm_steps
                                        s
                                       in
                                    FStar_List.append
                                      [FStar_TypeChecker_Normalize.Reify;
                                      FStar_TypeChecker_Normalize.UnfoldTac]
                                      uu____3418
                                     in
                                  let t2 =
                                    normalize steps
                                      ps.FStar_Tactics_Types.main_context t1
                                     in
                                  ret t2))))
           in
        FStar_All.pipe_left (wrap_err "norm_term") uu____3355
  
let (refine_intro : unit -> unit tac) =
  fun uu____3432  ->
    let uu____3435 =
      let uu____3438 = cur_goal ()  in
      bind uu____3438
        (fun g  ->
           let uu____3445 =
             let uu____3456 = FStar_Tactics_Types.goal_env g  in
             let uu____3457 = FStar_Tactics_Types.goal_type g  in
             FStar_TypeChecker_Rel.base_and_refinement uu____3456 uu____3457
              in
           match uu____3445 with
           | (uu____3460,FStar_Pervasives_Native.None ) ->
               fail "not a refinement"
           | (t,FStar_Pervasives_Native.Some (bv,phi)) ->
               let g1 = FStar_Tactics_Types.goal_with_type g t  in
               let uu____3485 =
                 let uu____3490 =
                   let uu____3495 =
                     let uu____3496 = FStar_Syntax_Syntax.mk_binder bv  in
                     [uu____3496]  in
                   FStar_Syntax_Subst.open_term uu____3495 phi  in
                 match uu____3490 with
                 | (bvs,phi1) ->
                     let uu____3521 =
                       let uu____3522 = FStar_List.hd bvs  in
                       FStar_Pervasives_Native.fst uu____3522  in
                     (uu____3521, phi1)
                  in
               (match uu____3485 with
                | (bv1,phi1) ->
                    let uu____3541 =
                      let uu____3544 = FStar_Tactics_Types.goal_env g  in
                      let uu____3545 =
                        let uu____3546 =
                          let uu____3549 =
                            let uu____3550 =
                              let uu____3557 =
                                FStar_Tactics_Types.goal_witness g  in
                              (bv1, uu____3557)  in
                            FStar_Syntax_Syntax.NT uu____3550  in
                          [uu____3549]  in
                        FStar_Syntax_Subst.subst uu____3546 phi1  in
                      mk_irrelevant_goal "refine_intro refinement" uu____3544
                        uu____3545 g.FStar_Tactics_Types.opts
                       in
                    bind uu____3541
                      (fun g2  ->
                         bind __dismiss
                           (fun uu____3565  -> add_goals [g1; g2]))))
       in
    FStar_All.pipe_left (wrap_err "refine_intro") uu____3435
  
let (__exact_now : Prims.bool -> FStar_Syntax_Syntax.term -> unit tac) =
  fun set_expected_typ1  ->
    fun t  ->
      let uu____3584 = cur_goal ()  in
      bind uu____3584
        (fun goal  ->
           let env =
             if set_expected_typ1
             then
               let uu____3592 = FStar_Tactics_Types.goal_env goal  in
               let uu____3593 = FStar_Tactics_Types.goal_type goal  in
               FStar_TypeChecker_Env.set_expected_typ uu____3592 uu____3593
             else FStar_Tactics_Types.goal_env goal  in
           let uu____3595 = __tc env t  in
           bind uu____3595
             (fun uu____3614  ->
                match uu____3614 with
                | (t1,typ,guard) ->
                    mlog
                      (fun uu____3629  ->
                         let uu____3630 =
                           FStar_Syntax_Print.term_to_string typ  in
                         let uu____3631 =
                           let uu____3632 = FStar_Tactics_Types.goal_env goal
                              in
                           FStar_TypeChecker_Rel.guard_to_string uu____3632
                             guard
                            in
                         FStar_Util.print2
                           "__exact_now: got type %s\n__exact_now: and guard %s\n"
                           uu____3630 uu____3631)
                      (fun uu____3635  ->
                         let uu____3636 =
                           let uu____3639 = FStar_Tactics_Types.goal_env goal
                              in
                           proc_guard "__exact typing" uu____3639 guard  in
                         bind uu____3636
                           (fun uu____3641  ->
                              mlog
                                (fun uu____3645  ->
                                   let uu____3646 =
                                     FStar_Syntax_Print.term_to_string typ
                                      in
                                   let uu____3647 =
                                     let uu____3648 =
                                       FStar_Tactics_Types.goal_type goal  in
                                     FStar_Syntax_Print.term_to_string
                                       uu____3648
                                      in
                                   FStar_Util.print2
                                     "__exact_now: unifying %s and %s\n"
                                     uu____3646 uu____3647)
                                (fun uu____3651  ->
                                   let uu____3652 =
                                     let uu____3655 =
                                       FStar_Tactics_Types.goal_env goal  in
                                     let uu____3656 =
                                       FStar_Tactics_Types.goal_type goal  in
                                     do_unify uu____3655 typ uu____3656  in
                                   bind uu____3652
                                     (fun b  ->
                                        if b
                                        then solve goal t1
                                        else
                                          (let uu____3662 =
                                             let uu____3663 =
                                               FStar_Tactics_Types.goal_env
                                                 goal
                                                in
                                             tts uu____3663 t1  in
                                           let uu____3664 =
                                             let uu____3665 =
                                               FStar_Tactics_Types.goal_env
                                                 goal
                                                in
                                             tts uu____3665 typ  in
                                           let uu____3666 =
                                             let uu____3667 =
                                               FStar_Tactics_Types.goal_env
                                                 goal
                                                in
                                             let uu____3668 =
                                               FStar_Tactics_Types.goal_type
                                                 goal
                                                in
                                             tts uu____3667 uu____3668  in
                                           let uu____3669 =
                                             let uu____3670 =
                                               FStar_Tactics_Types.goal_env
                                                 goal
                                                in
                                             let uu____3671 =
                                               FStar_Tactics_Types.goal_witness
                                                 goal
                                                in
                                             tts uu____3670 uu____3671  in
                                           fail4
                                             "%s : %s does not exactly solve the goal %s (witness = %s)"
                                             uu____3662 uu____3664 uu____3666
                                             uu____3669)))))))
  
let (t_exact : Prims.bool -> FStar_Syntax_Syntax.term -> unit tac) =
  fun set_expected_typ1  ->
    fun tm  ->
      let uu____3686 =
        mlog
          (fun uu____3691  ->
             let uu____3692 = FStar_Syntax_Print.term_to_string tm  in
             FStar_Util.print1 "t_exact: tm = %s\n" uu____3692)
          (fun uu____3695  ->
             let uu____3696 =
               let uu____3703 = __exact_now set_expected_typ1 tm  in
               trytac' uu____3703  in
             bind uu____3696
               (fun uu___340_3712  ->
                  match uu___340_3712 with
                  | FStar_Util.Inr r -> ret ()
                  | FStar_Util.Inl e ->
                      mlog
                        (fun uu____3722  ->
                           FStar_Util.print_string
                             "__exact_now failed, trying refine...\n")
                        (fun uu____3725  ->
                           let uu____3726 =
                             let uu____3733 =
                               let uu____3736 =
                                 norm [FStar_Syntax_Embeddings.Delta]  in
                               bind uu____3736
                                 (fun uu____3741  ->
                                    let uu____3742 = refine_intro ()  in
                                    bind uu____3742
                                      (fun uu____3746  ->
                                         __exact_now set_expected_typ1 tm))
                                in
                             trytac' uu____3733  in
                           bind uu____3726
                             (fun uu___339_3753  ->
                                match uu___339_3753 with
                                | FStar_Util.Inr r -> ret ()
                                | FStar_Util.Inl uu____3761 -> fail e))))
         in
      FStar_All.pipe_left (wrap_err "exact") uu____3686
  
let rec mapM : 'a 'b . ('a -> 'b tac) -> 'a Prims.list -> 'b Prims.list tac =
  fun f  ->
    fun l  ->
      match l with
      | [] -> ret []
      | x::xs ->
          let uu____3811 = f x  in
          bind uu____3811
            (fun y  ->
               let uu____3819 = mapM f xs  in
               bind uu____3819 (fun ys  -> ret (y :: ys)))
  
let rec (__try_match_by_application :
  (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.aqual,FStar_Syntax_Syntax.ctx_uvar)
    FStar_Pervasives_Native.tuple3 Prims.list ->
    env ->
      FStar_Syntax_Syntax.term ->
        FStar_Syntax_Syntax.term ->
          (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.aqual,FStar_Syntax_Syntax.ctx_uvar)
            FStar_Pervasives_Native.tuple3 Prims.list tac)
  =
  fun acc  ->
    fun e  ->
      fun ty1  ->
        fun ty2  ->
          let uu____3890 = do_unify e ty1 ty2  in
          bind uu____3890
            (fun uu___341_3902  ->
               if uu___341_3902
               then ret acc
               else
                 (let uu____3921 = FStar_Syntax_Util.arrow_one ty1  in
                  match uu____3921 with
                  | FStar_Pervasives_Native.None  ->
                      let uu____3942 = FStar_Syntax_Print.term_to_string ty1
                         in
                      let uu____3943 = FStar_Syntax_Print.term_to_string ty2
                         in
                      fail2 "Could not instantiate, %s to %s" uu____3942
                        uu____3943
                  | FStar_Pervasives_Native.Some (b,c) ->
                      let uu____3958 =
                        let uu____3959 = FStar_Syntax_Util.is_total_comp c
                           in
                        Prims.op_Negation uu____3959  in
                      if uu____3958
                      then fail "Codomain is effectful"
                      else
                        (let uu____3979 =
                           new_uvar "apply arg" e
                             (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                            in
                         bind uu____3979
                           (fun uu____4005  ->
                              match uu____4005 with
                              | (uvt,uv) ->
                                  let typ = comp_to_typ c  in
                                  let typ' =
                                    FStar_Syntax_Subst.subst
                                      [FStar_Syntax_Syntax.NT
                                         ((FStar_Pervasives_Native.fst b),
                                           uvt)] typ
                                     in
                                  __try_match_by_application
                                    ((uvt, (FStar_Pervasives_Native.snd b),
                                       uv) :: acc) e typ' ty2))))
  
let (try_match_by_application :
  env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term ->
        (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.aqual,FStar_Syntax_Syntax.ctx_uvar)
          FStar_Pervasives_Native.tuple3 Prims.list tac)
  = fun e  -> fun ty1  -> fun ty2  -> __try_match_by_application [] e ty1 ty2 
let (apply : Prims.bool -> FStar_Syntax_Syntax.term -> unit tac) =
  fun uopt  ->
    fun tm  ->
      let uu____4091 =
        mlog
          (fun uu____4096  ->
             let uu____4097 = FStar_Syntax_Print.term_to_string tm  in
             FStar_Util.print1 "apply: tm = %s\n" uu____4097)
          (fun uu____4100  ->
             let uu____4101 = cur_goal ()  in
             bind uu____4101
               (fun goal  ->
                  let e = FStar_Tactics_Types.goal_env goal  in
                  let uu____4109 = __tc e tm  in
                  bind uu____4109
                    (fun uu____4130  ->
                       match uu____4130 with
                       | (tm1,typ,guard) ->
                           let typ1 = bnorm e typ  in
                           let uu____4143 =
                             let uu____4154 =
                               FStar_Tactics_Types.goal_type goal  in
                             try_match_by_application e typ1 uu____4154  in
                           bind uu____4143
                             (fun uvs  ->
                                let w =
                                  FStar_List.fold_right
                                    (fun uu____4197  ->
                                       fun w  ->
                                         match uu____4197 with
                                         | (uvt,q,uu____4215) ->
                                             FStar_Syntax_Util.mk_app w
                                               [(uvt, q)]) uvs tm1
                                   in
                                let uvset =
                                  let uu____4247 =
                                    FStar_Syntax_Free.new_uv_set ()  in
                                  FStar_List.fold_right
                                    (fun uu____4264  ->
                                       fun s  ->
                                         match uu____4264 with
                                         | (uu____4276,uu____4277,uv) ->
                                             let uu____4279 =
                                               FStar_Syntax_Free.uvars
                                                 uv.FStar_Syntax_Syntax.ctx_uvar_typ
                                                in
                                             FStar_Util.set_union s
                                               uu____4279) uvs uu____4247
                                   in
                                let free_in_some_goal uv =
                                  FStar_Util.set_mem uv uvset  in
                                let uu____4288 = solve' goal w  in
                                bind uu____4288
                                  (fun uu____4293  ->
                                     let uu____4294 =
                                       mapM
                                         (fun uu____4311  ->
                                            match uu____4311 with
                                            | (uvt,q,uv) ->
                                                let uu____4323 =
                                                  FStar_Syntax_Unionfind.find
                                                    uv.FStar_Syntax_Syntax.ctx_uvar_head
                                                   in
                                                (match uu____4323 with
                                                 | FStar_Pervasives_Native.Some
                                                     uu____4328 -> ret ()
                                                 | FStar_Pervasives_Native.None
                                                      ->
                                                     let uu____4329 =
                                                       uopt &&
                                                         (free_in_some_goal
                                                            uv)
                                                        in
                                                     if uu____4329
                                                     then ret ()
                                                     else
                                                       (let uu____4333 =
                                                          let uu____4336 =
                                                            bnorm_goal
                                                              (let uu___377_4339
                                                                 = goal  in
                                                               {
                                                                 FStar_Tactics_Types.goal_main_env
                                                                   =
                                                                   (uu___377_4339.FStar_Tactics_Types.goal_main_env);
                                                                 FStar_Tactics_Types.goal_ctx_uvar
                                                                   = uv;
                                                                 FStar_Tactics_Types.opts
                                                                   =
                                                                   (uu___377_4339.FStar_Tactics_Types.opts);
                                                                 FStar_Tactics_Types.is_guard
                                                                   = false
                                                               })
                                                             in
                                                          [uu____4336]  in
                                                        add_goals uu____4333)))
                                         uvs
                                        in
                                     bind uu____4294
                                       (fun uu____4343  ->
                                          proc_guard "apply guard" e guard))))))
         in
      FStar_All.pipe_left (wrap_err "apply") uu____4091
  
let (lemma_or_sq :
  FStar_Syntax_Syntax.comp ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun c  ->
    let ct = FStar_Syntax_Util.comp_to_comp_typ_nouniv c  in
    let uu____4368 =
      FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
        FStar_Parser_Const.effect_Lemma_lid
       in
    if uu____4368
    then
      let uu____4375 =
        match ct.FStar_Syntax_Syntax.effect_args with
        | pre::post::uu____4390 ->
            ((FStar_Pervasives_Native.fst pre),
              (FStar_Pervasives_Native.fst post))
        | uu____4443 -> failwith "apply_lemma: impossible: not a lemma"  in
      match uu____4375 with
      | (pre,post) ->
          let post1 =
            let uu____4475 =
              let uu____4486 =
                FStar_Syntax_Syntax.as_arg FStar_Syntax_Util.exp_unit  in
              [uu____4486]  in
            FStar_Syntax_Util.mk_app post uu____4475  in
          FStar_Pervasives_Native.Some (pre, post1)
    else
      (let uu____4516 =
         FStar_Syntax_Util.is_pure_effect ct.FStar_Syntax_Syntax.effect_name
          in
       if uu____4516
       then
         let uu____4523 =
           FStar_Syntax_Util.un_squash ct.FStar_Syntax_Syntax.result_typ  in
         FStar_Util.map_opt uu____4523
           (fun post  -> (FStar_Syntax_Util.t_true, post))
       else FStar_Pervasives_Native.None)
  
let (apply_lemma : FStar_Syntax_Syntax.term -> unit tac) =
  fun tm  ->
    let uu____4556 =
      let uu____4559 =
        mlog
          (fun uu____4564  ->
             let uu____4565 = FStar_Syntax_Print.term_to_string tm  in
             FStar_Util.print1 "apply_lemma: tm = %s\n" uu____4565)
          (fun uu____4569  ->
             let is_unit_t t =
               let uu____4576 =
                 let uu____4577 = FStar_Syntax_Subst.compress t  in
                 uu____4577.FStar_Syntax_Syntax.n  in
               match uu____4576 with
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.unit_lid
                   -> true
               | uu____4581 -> false  in
             let uu____4582 = cur_goal ()  in
             bind uu____4582
               (fun goal  ->
                  let uu____4588 =
                    let uu____4597 = FStar_Tactics_Types.goal_env goal  in
                    __tc uu____4597 tm  in
                  bind uu____4588
                    (fun uu____4612  ->
                       match uu____4612 with
                       | (tm1,t,guard) ->
                           let uu____4624 =
                             FStar_Syntax_Util.arrow_formals_comp t  in
                           (match uu____4624 with
                            | (bs,comp) ->
                                let uu____4657 = lemma_or_sq comp  in
                                (match uu____4657 with
                                 | FStar_Pervasives_Native.None  ->
                                     fail "not a lemma or squashed function"
                                 | FStar_Pervasives_Native.Some (pre,post) ->
                                     let uu____4676 =
                                       FStar_List.fold_left
                                         (fun uu____4724  ->
                                            fun uu____4725  ->
                                              match (uu____4724, uu____4725)
                                              with
                                              | ((uvs,guard1,subst1),(b,aq))
                                                  ->
                                                  let b_t =
                                                    FStar_Syntax_Subst.subst
                                                      subst1
                                                      b.FStar_Syntax_Syntax.sort
                                                     in
                                                  let uu____4838 =
                                                    is_unit_t b_t  in
                                                  if uu____4838
                                                  then
                                                    (((FStar_Syntax_Util.exp_unit,
                                                        aq) :: uvs), guard1,
                                                      ((FStar_Syntax_Syntax.NT
                                                          (b,
                                                            FStar_Syntax_Util.exp_unit))
                                                      :: subst1))
                                                  else
                                                    (let uu____4876 =
                                                       let uu____4889 =
                                                         let uu____4890 =
                                                           FStar_Tactics_Types.goal_type
                                                             goal
                                                            in
                                                         uu____4890.FStar_Syntax_Syntax.pos
                                                          in
                                                       let uu____4893 =
                                                         FStar_Tactics_Types.goal_env
                                                           goal
                                                          in
                                                       FStar_TypeChecker_Util.new_implicit_var
                                                         "apply_lemma"
                                                         uu____4889
                                                         uu____4893 b_t
                                                        in
                                                     match uu____4876 with
                                                     | (u,uu____4911,g_u) ->
                                                         let uu____4925 =
                                                           FStar_TypeChecker_Env.conj_guard
                                                             guard1 g_u
                                                            in
                                                         (((u, aq) :: uvs),
                                                           uu____4925,
                                                           ((FStar_Syntax_Syntax.NT
                                                               (b, u)) ::
                                                           subst1))))
                                         ([], guard, []) bs
                                        in
                                     (match uu____4676 with
                                      | (uvs,implicits,subst1) ->
                                          let uvs1 = FStar_List.rev uvs  in
                                          let pre1 =
                                            FStar_Syntax_Subst.subst subst1
                                              pre
                                             in
                                          let post1 =
                                            FStar_Syntax_Subst.subst subst1
                                              post
                                             in
                                          let uu____5004 =
                                            let uu____5007 =
                                              FStar_Tactics_Types.goal_env
                                                goal
                                               in
                                            let uu____5008 =
                                              FStar_Syntax_Util.mk_squash
                                                FStar_Syntax_Syntax.U_zero
                                                post1
                                               in
                                            let uu____5009 =
                                              FStar_Tactics_Types.goal_type
                                                goal
                                               in
                                            do_unify uu____5007 uu____5008
                                              uu____5009
                                             in
                                          bind uu____5004
                                            (fun b  ->
                                               if Prims.op_Negation b
                                               then
                                                 let uu____5017 =
                                                   let uu____5018 =
                                                     FStar_Tactics_Types.goal_env
                                                       goal
                                                      in
                                                   tts uu____5018 tm1  in
                                                 let uu____5019 =
                                                   let uu____5020 =
                                                     FStar_Tactics_Types.goal_env
                                                       goal
                                                      in
                                                   let uu____5021 =
                                                     FStar_Syntax_Util.mk_squash
                                                       FStar_Syntax_Syntax.U_zero
                                                       post1
                                                      in
                                                   tts uu____5020 uu____5021
                                                    in
                                                 let uu____5022 =
                                                   let uu____5023 =
                                                     FStar_Tactics_Types.goal_env
                                                       goal
                                                      in
                                                   let uu____5024 =
                                                     FStar_Tactics_Types.goal_type
                                                       goal
                                                      in
                                                   tts uu____5023 uu____5024
                                                    in
                                                 fail3
                                                   "Cannot instantiate lemma %s (with postcondition: %s) to match goal (%s)"
                                                   uu____5017 uu____5019
                                                   uu____5022
                                               else
                                                 (let uu____5026 =
                                                    add_implicits
                                                      implicits.FStar_TypeChecker_Env.implicits
                                                     in
                                                  bind uu____5026
                                                    (fun uu____5031  ->
                                                       let uu____5032 =
                                                         solve' goal
                                                           FStar_Syntax_Util.exp_unit
                                                          in
                                                       bind uu____5032
                                                         (fun uu____5040  ->
                                                            let is_free_uvar
                                                              uv t1 =
                                                              let free_uvars
                                                                =
                                                                let uu____5065
                                                                  =
                                                                  let uu____5068
                                                                    =
                                                                    FStar_Syntax_Free.uvars
                                                                    t1  in
                                                                  FStar_Util.set_elements
                                                                    uu____5068
                                                                   in
                                                                FStar_List.map
                                                                  (fun x  ->
                                                                    x.FStar_Syntax_Syntax.ctx_uvar_head)
                                                                  uu____5065
                                                                 in
                                                              FStar_List.existsML
                                                                (fun u  ->
                                                                   FStar_Syntax_Unionfind.equiv
                                                                    u uv)
                                                                free_uvars
                                                               in
                                                            let appears uv
                                                              goals =
                                                              FStar_List.existsML
                                                                (fun g'  ->
                                                                   let uu____5103
                                                                    =
                                                                    FStar_Tactics_Types.goal_type
                                                                    g'  in
                                                                   is_free_uvar
                                                                    uv
                                                                    uu____5103)
                                                                goals
                                                               in
                                                            let checkone t1
                                                              goals =
                                                              let uu____5119
                                                                =
                                                                FStar_Syntax_Util.head_and_args
                                                                  t1
                                                                 in
                                                              match uu____5119
                                                              with
                                                              | (hd1,uu____5137)
                                                                  ->
                                                                  (match 
                                                                    hd1.FStar_Syntax_Syntax.n
                                                                   with
                                                                   | 
                                                                   FStar_Syntax_Syntax.Tm_uvar
                                                                    (uv,uu____5163)
                                                                    ->
                                                                    appears
                                                                    uv.FStar_Syntax_Syntax.ctx_uvar_head
                                                                    goals
                                                                   | 
                                                                   uu____5180
                                                                    -> false)
                                                               in
                                                            let uu____5181 =
                                                              FStar_All.pipe_right
                                                                implicits.FStar_TypeChecker_Env.implicits
                                                                (mapM
                                                                   (fun imp 
                                                                    ->
                                                                    let term
                                                                    =
                                                                    imp.FStar_TypeChecker_Env.imp_tm
                                                                     in
                                                                    let ctx_uvar
                                                                    =
                                                                    imp.FStar_TypeChecker_Env.imp_uvar
                                                                     in
                                                                    let uu____5211
                                                                    =
                                                                    FStar_Syntax_Util.head_and_args
                                                                    term  in
                                                                    match uu____5211
                                                                    with
                                                                    | 
                                                                    (hd1,uu____5233)
                                                                    ->
                                                                    let uu____5258
                                                                    =
                                                                    let uu____5259
                                                                    =
                                                                    FStar_Syntax_Subst.compress
                                                                    hd1  in
                                                                    uu____5259.FStar_Syntax_Syntax.n
                                                                     in
                                                                    (match uu____5258
                                                                    with
                                                                    | 
                                                                    FStar_Syntax_Syntax.Tm_uvar
                                                                    (ctx_uvar1,uu____5267)
                                                                    ->
                                                                    let goal1
                                                                    =
                                                                    bnorm_goal
                                                                    (let uu___378_5287
                                                                    = goal
                                                                     in
                                                                    {
                                                                    FStar_Tactics_Types.goal_main_env
                                                                    =
                                                                    (uu___378_5287.FStar_Tactics_Types.goal_main_env);
                                                                    FStar_Tactics_Types.goal_ctx_uvar
                                                                    =
                                                                    ctx_uvar1;
                                                                    FStar_Tactics_Types.opts
                                                                    =
                                                                    (uu___378_5287.FStar_Tactics_Types.opts);
                                                                    FStar_Tactics_Types.is_guard
                                                                    =
                                                                    (uu___378_5287.FStar_Tactics_Types.is_guard)
                                                                    })  in
                                                                    ret
                                                                    [goal1]
                                                                    | 
                                                                    uu____5290
                                                                    ->
                                                                    let env =
                                                                    let uu___379_5292
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    goal  in
                                                                    {
                                                                    FStar_TypeChecker_Env.solver
                                                                    =
                                                                    (uu___379_5292.FStar_TypeChecker_Env.solver);
                                                                    FStar_TypeChecker_Env.range
                                                                    =
                                                                    (uu___379_5292.FStar_TypeChecker_Env.range);
                                                                    FStar_TypeChecker_Env.curmodule
                                                                    =
                                                                    (uu___379_5292.FStar_TypeChecker_Env.curmodule);
                                                                    FStar_TypeChecker_Env.gamma
                                                                    =
                                                                    (ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_gamma);
                                                                    FStar_TypeChecker_Env.gamma_sig
                                                                    =
                                                                    (uu___379_5292.FStar_TypeChecker_Env.gamma_sig);
                                                                    FStar_TypeChecker_Env.gamma_cache
                                                                    =
                                                                    (uu___379_5292.FStar_TypeChecker_Env.gamma_cache);
                                                                    FStar_TypeChecker_Env.modules
                                                                    =
                                                                    (uu___379_5292.FStar_TypeChecker_Env.modules);
                                                                    FStar_TypeChecker_Env.expected_typ
                                                                    =
                                                                    (uu___379_5292.FStar_TypeChecker_Env.expected_typ);
                                                                    FStar_TypeChecker_Env.sigtab
                                                                    =
                                                                    (uu___379_5292.FStar_TypeChecker_Env.sigtab);
                                                                    FStar_TypeChecker_Env.attrtab
                                                                    =
                                                                    (uu___379_5292.FStar_TypeChecker_Env.attrtab);
                                                                    FStar_TypeChecker_Env.is_pattern
                                                                    =
                                                                    (uu___379_5292.FStar_TypeChecker_Env.is_pattern);
                                                                    FStar_TypeChecker_Env.instantiate_imp
                                                                    =
                                                                    (uu___379_5292.FStar_TypeChecker_Env.instantiate_imp);
                                                                    FStar_TypeChecker_Env.effects
                                                                    =
                                                                    (uu___379_5292.FStar_TypeChecker_Env.effects);
                                                                    FStar_TypeChecker_Env.generalize
                                                                    =
                                                                    (uu___379_5292.FStar_TypeChecker_Env.generalize);
                                                                    FStar_TypeChecker_Env.letrecs
                                                                    =
                                                                    (uu___379_5292.FStar_TypeChecker_Env.letrecs);
                                                                    FStar_TypeChecker_Env.top_level
                                                                    =
                                                                    (uu___379_5292.FStar_TypeChecker_Env.top_level);
                                                                    FStar_TypeChecker_Env.check_uvars
                                                                    =
                                                                    (uu___379_5292.FStar_TypeChecker_Env.check_uvars);
                                                                    FStar_TypeChecker_Env.use_eq
                                                                    =
                                                                    (uu___379_5292.FStar_TypeChecker_Env.use_eq);
                                                                    FStar_TypeChecker_Env.is_iface
                                                                    =
                                                                    (uu___379_5292.FStar_TypeChecker_Env.is_iface);
                                                                    FStar_TypeChecker_Env.admit
                                                                    =
                                                                    (uu___379_5292.FStar_TypeChecker_Env.admit);
                                                                    FStar_TypeChecker_Env.lax
                                                                    =
                                                                    (uu___379_5292.FStar_TypeChecker_Env.lax);
                                                                    FStar_TypeChecker_Env.lax_universes
                                                                    =
                                                                    (uu___379_5292.FStar_TypeChecker_Env.lax_universes);
                                                                    FStar_TypeChecker_Env.phase1
                                                                    =
                                                                    (uu___379_5292.FStar_TypeChecker_Env.phase1);
                                                                    FStar_TypeChecker_Env.failhard
                                                                    =
                                                                    (uu___379_5292.FStar_TypeChecker_Env.failhard);
                                                                    FStar_TypeChecker_Env.nosynth
                                                                    =
                                                                    (uu___379_5292.FStar_TypeChecker_Env.nosynth);
                                                                    FStar_TypeChecker_Env.uvar_subtyping
                                                                    =
                                                                    (uu___379_5292.FStar_TypeChecker_Env.uvar_subtyping);
                                                                    FStar_TypeChecker_Env.tc_term
                                                                    =
                                                                    (uu___379_5292.FStar_TypeChecker_Env.tc_term);
                                                                    FStar_TypeChecker_Env.type_of
                                                                    =
                                                                    (uu___379_5292.FStar_TypeChecker_Env.type_of);
                                                                    FStar_TypeChecker_Env.universe_of
                                                                    =
                                                                    (uu___379_5292.FStar_TypeChecker_Env.universe_of);
                                                                    FStar_TypeChecker_Env.check_type_of
                                                                    =
                                                                    (uu___379_5292.FStar_TypeChecker_Env.check_type_of);
                                                                    FStar_TypeChecker_Env.use_bv_sorts
                                                                    =
                                                                    (uu___379_5292.FStar_TypeChecker_Env.use_bv_sorts);
                                                                    FStar_TypeChecker_Env.qtbl_name_and_index
                                                                    =
                                                                    (uu___379_5292.FStar_TypeChecker_Env.qtbl_name_and_index);
                                                                    FStar_TypeChecker_Env.normalized_eff_names
                                                                    =
                                                                    (uu___379_5292.FStar_TypeChecker_Env.normalized_eff_names);
                                                                    FStar_TypeChecker_Env.proof_ns
                                                                    =
                                                                    (uu___379_5292.FStar_TypeChecker_Env.proof_ns);
                                                                    FStar_TypeChecker_Env.synth_hook
                                                                    =
                                                                    (uu___379_5292.FStar_TypeChecker_Env.synth_hook);
                                                                    FStar_TypeChecker_Env.splice
                                                                    =
                                                                    (uu___379_5292.FStar_TypeChecker_Env.splice);
                                                                    FStar_TypeChecker_Env.is_native_tactic
                                                                    =
                                                                    (uu___379_5292.FStar_TypeChecker_Env.is_native_tactic);
                                                                    FStar_TypeChecker_Env.identifier_info
                                                                    =
                                                                    (uu___379_5292.FStar_TypeChecker_Env.identifier_info);
                                                                    FStar_TypeChecker_Env.tc_hooks
                                                                    =
                                                                    (uu___379_5292.FStar_TypeChecker_Env.tc_hooks);
                                                                    FStar_TypeChecker_Env.dsenv
                                                                    =
                                                                    (uu___379_5292.FStar_TypeChecker_Env.dsenv);
                                                                    FStar_TypeChecker_Env.dep_graph
                                                                    =
                                                                    (uu___379_5292.FStar_TypeChecker_Env.dep_graph)
                                                                    }  in
                                                                    let g_typ
                                                                    =
                                                                    let uu____5294
                                                                    =
                                                                    FStar_Options.__temp_fast_implicits
                                                                    ()  in
                                                                    if
                                                                    uu____5294
                                                                    then
                                                                    FStar_TypeChecker_TcTerm.check_type_of_well_typed_term
                                                                    false env
                                                                    term
                                                                    ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_typ
                                                                    else
                                                                    (let term1
                                                                    =
                                                                    bnorm env
                                                                    term  in
                                                                    let uu____5297
                                                                    =
                                                                    let uu____5304
                                                                    =
                                                                    FStar_TypeChecker_Env.set_expected_typ
                                                                    env
                                                                    ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_typ
                                                                     in
                                                                    env.FStar_TypeChecker_Env.type_of
                                                                    uu____5304
                                                                    term1  in
                                                                    match uu____5297
                                                                    with
                                                                    | 
                                                                    (uu____5305,uu____5306,g_typ)
                                                                    -> g_typ)
                                                                     in
                                                                    let uu____5308
                                                                    =
                                                                    let uu____5311
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    goal  in
                                                                    proc_guard
                                                                    "apply_lemma solved arg"
                                                                    uu____5311
                                                                    g_typ  in
                                                                    bind
                                                                    uu____5308
                                                                    (fun
                                                                    uu____5315
                                                                     ->
                                                                    ret []))))
                                                               in
                                                            bind uu____5181
                                                              (fun sub_goals 
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
                                                                    let uu____5377
                                                                    = f x xs1
                                                                     in
                                                                    if
                                                                    uu____5377
                                                                    then
                                                                    let uu____5380
                                                                    =
                                                                    filter' f
                                                                    xs1  in x
                                                                    ::
                                                                    uu____5380
                                                                    else
                                                                    filter' f
                                                                    xs1
                                                                    in
                                                                 let sub_goals2
                                                                   =
                                                                   filter'
                                                                    (fun g 
                                                                    ->
                                                                    fun goals
                                                                     ->
                                                                    let uu____5394
                                                                    =
                                                                    let uu____5395
                                                                    =
                                                                    FStar_Tactics_Types.goal_witness
                                                                    g  in
                                                                    checkone
                                                                    uu____5395
                                                                    goals  in
                                                                    Prims.op_Negation
                                                                    uu____5394)
                                                                    sub_goals1
                                                                    in
                                                                 let uu____5396
                                                                   =
                                                                   let uu____5399
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    goal  in
                                                                   proc_guard
                                                                    "apply_lemma guard"
                                                                    uu____5399
                                                                    guard
                                                                    in
                                                                 bind
                                                                   uu____5396
                                                                   (fun
                                                                    uu____5402
                                                                     ->
                                                                    let uu____5403
                                                                    =
                                                                    let uu____5406
                                                                    =
                                                                    let uu____5407
                                                                    =
                                                                    let uu____5408
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    goal  in
                                                                    let uu____5409
                                                                    =
                                                                    FStar_Syntax_Util.mk_squash
                                                                    FStar_Syntax_Syntax.U_zero
                                                                    pre1  in
                                                                    istrivial
                                                                    uu____5408
                                                                    uu____5409
                                                                     in
                                                                    Prims.op_Negation
                                                                    uu____5407
                                                                     in
                                                                    if
                                                                    uu____5406
                                                                    then
                                                                    let uu____5412
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    goal  in
                                                                    add_irrelevant_goal
                                                                    "apply_lemma precondition"
                                                                    uu____5412
                                                                    pre1
                                                                    goal.FStar_Tactics_Types.opts
                                                                    else
                                                                    ret ()
                                                                     in
                                                                    bind
                                                                    uu____5403
                                                                    (fun
                                                                    uu____5415
                                                                     ->
                                                                    add_goals
                                                                    sub_goals2)))))))))))))
         in
      focus uu____4559  in
    FStar_All.pipe_left (wrap_err "apply_lemma") uu____4556
  
let (destruct_eq' :
  FStar_Reflection_Data.typ ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun typ  ->
    let uu____5437 = FStar_Syntax_Util.destruct_typ_as_formula typ  in
    match uu____5437 with
    | FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn
        (l,uu____5447::(e1,uu____5449)::(e2,uu____5451)::[])) when
        FStar_Ident.lid_equals l FStar_Parser_Const.eq2_lid ->
        FStar_Pervasives_Native.Some (e1, e2)
    | uu____5512 -> FStar_Pervasives_Native.None
  
let (destruct_eq :
  FStar_Reflection_Data.typ ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun typ  ->
    let uu____5536 = destruct_eq' typ  in
    match uu____5536 with
    | FStar_Pervasives_Native.Some t -> FStar_Pervasives_Native.Some t
    | FStar_Pervasives_Native.None  ->
        let uu____5566 = FStar_Syntax_Util.un_squash typ  in
        (match uu____5566 with
         | FStar_Pervasives_Native.Some typ1 -> destruct_eq' typ1
         | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None)
  
let (split_env :
  FStar_Syntax_Syntax.bv ->
    env ->
      (env,FStar_Syntax_Syntax.bv Prims.list) FStar_Pervasives_Native.tuple2
        FStar_Pervasives_Native.option)
  =
  fun bvar  ->
    fun e  ->
      let rec aux e1 =
        let uu____5628 = FStar_TypeChecker_Env.pop_bv e1  in
        match uu____5628 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (bv',e') ->
            if FStar_Syntax_Syntax.bv_eq bvar bv'
            then FStar_Pervasives_Native.Some (e', [])
            else
              (let uu____5676 = aux e'  in
               FStar_Util.map_opt uu____5676
                 (fun uu____5700  ->
                    match uu____5700 with | (e'',bvs) -> (e'', (bv' :: bvs))))
         in
      let uu____5721 = aux e  in
      FStar_Util.map_opt uu____5721
        (fun uu____5745  ->
           match uu____5745 with | (e',bvs) -> (e', (FStar_List.rev bvs)))
  
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
          let uu____5812 =
            let uu____5821 = FStar_Tactics_Types.goal_env g  in
            split_env b1 uu____5821  in
          FStar_Util.map_opt uu____5812
            (fun uu____5836  ->
               match uu____5836 with
               | (e0,bvs) ->
                   let s1 bv =
                     let uu___380_5855 = bv  in
                     let uu____5856 =
                       FStar_Syntax_Subst.subst s bv.FStar_Syntax_Syntax.sort
                        in
                     {
                       FStar_Syntax_Syntax.ppname =
                         (uu___380_5855.FStar_Syntax_Syntax.ppname);
                       FStar_Syntax_Syntax.index =
                         (uu___380_5855.FStar_Syntax_Syntax.index);
                       FStar_Syntax_Syntax.sort = uu____5856
                     }  in
                   let bvs1 = FStar_List.map s1 bvs  in
                   let new_env = push_bvs e0 (b2 :: bvs1)  in
                   let new_goal =
                     let uu___381_5864 = g.FStar_Tactics_Types.goal_ctx_uvar
                        in
                     let uu____5865 =
                       FStar_TypeChecker_Env.all_binders new_env  in
                     let uu____5874 =
                       let uu____5877 = FStar_Tactics_Types.goal_type g  in
                       FStar_Syntax_Subst.subst s uu____5877  in
                     {
                       FStar_Syntax_Syntax.ctx_uvar_head =
                         (uu___381_5864.FStar_Syntax_Syntax.ctx_uvar_head);
                       FStar_Syntax_Syntax.ctx_uvar_gamma =
                         (new_env.FStar_TypeChecker_Env.gamma);
                       FStar_Syntax_Syntax.ctx_uvar_binders = uu____5865;
                       FStar_Syntax_Syntax.ctx_uvar_typ = uu____5874;
                       FStar_Syntax_Syntax.ctx_uvar_reason =
                         (uu___381_5864.FStar_Syntax_Syntax.ctx_uvar_reason);
                       FStar_Syntax_Syntax.ctx_uvar_should_check =
                         (uu___381_5864.FStar_Syntax_Syntax.ctx_uvar_should_check);
                       FStar_Syntax_Syntax.ctx_uvar_range =
                         (uu___381_5864.FStar_Syntax_Syntax.ctx_uvar_range)
                     }  in
                   let uu___382_5878 = g  in
                   {
                     FStar_Tactics_Types.goal_main_env =
                       (uu___382_5878.FStar_Tactics_Types.goal_main_env);
                     FStar_Tactics_Types.goal_ctx_uvar = new_goal;
                     FStar_Tactics_Types.opts =
                       (uu___382_5878.FStar_Tactics_Types.opts);
                     FStar_Tactics_Types.is_guard =
                       (uu___382_5878.FStar_Tactics_Types.is_guard)
                   })
  
let (rewrite : FStar_Syntax_Syntax.binder -> unit tac) =
  fun h  ->
    let uu____5888 =
      let uu____5891 = cur_goal ()  in
      bind uu____5891
        (fun goal  ->
           let uu____5899 = h  in
           match uu____5899 with
           | (bv,uu____5903) ->
               mlog
                 (fun uu____5911  ->
                    let uu____5912 = FStar_Syntax_Print.bv_to_string bv  in
                    let uu____5913 =
                      FStar_Syntax_Print.term_to_string
                        bv.FStar_Syntax_Syntax.sort
                       in
                    FStar_Util.print2 "+++Rewrite %s : %s\n" uu____5912
                      uu____5913)
                 (fun uu____5916  ->
                    let uu____5917 =
                      let uu____5926 = FStar_Tactics_Types.goal_env goal  in
                      split_env bv uu____5926  in
                    match uu____5917 with
                    | FStar_Pervasives_Native.None  ->
                        fail "binder not found in environment"
                    | FStar_Pervasives_Native.Some (e0,bvs) ->
                        let uu____5947 =
                          destruct_eq bv.FStar_Syntax_Syntax.sort  in
                        (match uu____5947 with
                         | FStar_Pervasives_Native.Some (x,e) ->
                             let uu____5962 =
                               let uu____5963 = FStar_Syntax_Subst.compress x
                                  in
                               uu____5963.FStar_Syntax_Syntax.n  in
                             (match uu____5962 with
                              | FStar_Syntax_Syntax.Tm_name x1 ->
                                  let s = [FStar_Syntax_Syntax.NT (x1, e)]
                                     in
                                  let s1 bv1 =
                                    let uu___383_5980 = bv1  in
                                    let uu____5981 =
                                      FStar_Syntax_Subst.subst s
                                        bv1.FStar_Syntax_Syntax.sort
                                       in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___383_5980.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___383_5980.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = uu____5981
                                    }  in
                                  let bvs1 = FStar_List.map s1 bvs  in
                                  let new_env = push_bvs e0 (bv :: bvs1)  in
                                  let new_goal =
                                    let uu___384_5989 =
                                      goal.FStar_Tactics_Types.goal_ctx_uvar
                                       in
                                    let uu____5990 =
                                      FStar_TypeChecker_Env.all_binders
                                        new_env
                                       in
                                    let uu____5999 =
                                      let uu____6002 =
                                        FStar_Tactics_Types.goal_type goal
                                         in
                                      FStar_Syntax_Subst.subst s uu____6002
                                       in
                                    {
                                      FStar_Syntax_Syntax.ctx_uvar_head =
                                        (uu___384_5989.FStar_Syntax_Syntax.ctx_uvar_head);
                                      FStar_Syntax_Syntax.ctx_uvar_gamma =
                                        (new_env.FStar_TypeChecker_Env.gamma);
                                      FStar_Syntax_Syntax.ctx_uvar_binders =
                                        uu____5990;
                                      FStar_Syntax_Syntax.ctx_uvar_typ =
                                        uu____5999;
                                      FStar_Syntax_Syntax.ctx_uvar_reason =
                                        (uu___384_5989.FStar_Syntax_Syntax.ctx_uvar_reason);
                                      FStar_Syntax_Syntax.ctx_uvar_should_check
                                        =
                                        (uu___384_5989.FStar_Syntax_Syntax.ctx_uvar_should_check);
                                      FStar_Syntax_Syntax.ctx_uvar_range =
                                        (uu___384_5989.FStar_Syntax_Syntax.ctx_uvar_range)
                                    }  in
                                  replace_cur
                                    (let uu___385_6005 = goal  in
                                     {
                                       FStar_Tactics_Types.goal_main_env =
                                         (uu___385_6005.FStar_Tactics_Types.goal_main_env);
                                       FStar_Tactics_Types.goal_ctx_uvar =
                                         new_goal;
                                       FStar_Tactics_Types.opts =
                                         (uu___385_6005.FStar_Tactics_Types.opts);
                                       FStar_Tactics_Types.is_guard =
                                         (uu___385_6005.FStar_Tactics_Types.is_guard)
                                     })
                              | uu____6006 ->
                                  fail
                                    "Not an equality hypothesis with a variable on the LHS")
                         | uu____6007 -> fail "Not an equality hypothesis")))
       in
    FStar_All.pipe_left (wrap_err "rewrite") uu____5888
  
let (rename_to : FStar_Syntax_Syntax.binder -> Prims.string -> unit tac) =
  fun b  ->
    fun s  ->
      let uu____6032 =
        let uu____6035 = cur_goal ()  in
        bind uu____6035
          (fun goal  ->
             let uu____6046 = b  in
             match uu____6046 with
             | (bv,uu____6050) ->
                 let bv' =
                   let uu____6056 =
                     let uu___386_6057 = bv  in
                     let uu____6058 =
                       FStar_Ident.mk_ident
                         (s,
                           ((bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange))
                        in
                     {
                       FStar_Syntax_Syntax.ppname = uu____6058;
                       FStar_Syntax_Syntax.index =
                         (uu___386_6057.FStar_Syntax_Syntax.index);
                       FStar_Syntax_Syntax.sort =
                         (uu___386_6057.FStar_Syntax_Syntax.sort)
                     }  in
                   FStar_Syntax_Syntax.freshen_bv uu____6056  in
                 let s1 =
                   let uu____6062 =
                     let uu____6063 =
                       let uu____6070 = FStar_Syntax_Syntax.bv_to_name bv'
                          in
                       (bv, uu____6070)  in
                     FStar_Syntax_Syntax.NT uu____6063  in
                   [uu____6062]  in
                 let uu____6075 = subst_goal bv bv' s1 goal  in
                 (match uu____6075 with
                  | FStar_Pervasives_Native.None  ->
                      fail "binder not found in environment"
                  | FStar_Pervasives_Native.Some goal1 -> replace_cur goal1))
         in
      FStar_All.pipe_left (wrap_err "rename_to") uu____6032
  
let (binder_retype : FStar_Syntax_Syntax.binder -> unit tac) =
  fun b  ->
    let uu____6094 =
      let uu____6097 = cur_goal ()  in
      bind uu____6097
        (fun goal  ->
           let uu____6106 = b  in
           match uu____6106 with
           | (bv,uu____6110) ->
               let uu____6115 =
                 let uu____6124 = FStar_Tactics_Types.goal_env goal  in
                 split_env bv uu____6124  in
               (match uu____6115 with
                | FStar_Pervasives_Native.None  ->
                    fail "binder is not present in environment"
                | FStar_Pervasives_Native.Some (e0,bvs) ->
                    let uu____6145 = FStar_Syntax_Util.type_u ()  in
                    (match uu____6145 with
                     | (ty,u) ->
                         let uu____6154 = new_uvar "binder_retype" e0 ty  in
                         bind uu____6154
                           (fun uu____6172  ->
                              match uu____6172 with
                              | (t',u_t') ->
                                  let bv'' =
                                    let uu___387_6182 = bv  in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___387_6182.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___387_6182.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = t'
                                    }  in
                                  let s =
                                    let uu____6186 =
                                      let uu____6187 =
                                        let uu____6194 =
                                          FStar_Syntax_Syntax.bv_to_name bv''
                                           in
                                        (bv, uu____6194)  in
                                      FStar_Syntax_Syntax.NT uu____6187  in
                                    [uu____6186]  in
                                  let bvs1 =
                                    FStar_List.map
                                      (fun b1  ->
                                         let uu___388_6206 = b1  in
                                         let uu____6207 =
                                           FStar_Syntax_Subst.subst s
                                             b1.FStar_Syntax_Syntax.sort
                                            in
                                         {
                                           FStar_Syntax_Syntax.ppname =
                                             (uu___388_6206.FStar_Syntax_Syntax.ppname);
                                           FStar_Syntax_Syntax.index =
                                             (uu___388_6206.FStar_Syntax_Syntax.index);
                                           FStar_Syntax_Syntax.sort =
                                             uu____6207
                                         }) bvs
                                     in
                                  let env' = push_bvs e0 (bv'' :: bvs1)  in
                                  bind __dismiss
                                    (fun uu____6214  ->
                                       let new_goal =
                                         let uu____6216 =
                                           FStar_Tactics_Types.goal_with_env
                                             goal env'
                                            in
                                         let uu____6217 =
                                           let uu____6218 =
                                             FStar_Tactics_Types.goal_type
                                               goal
                                              in
                                           FStar_Syntax_Subst.subst s
                                             uu____6218
                                            in
                                         FStar_Tactics_Types.goal_with_type
                                           uu____6216 uu____6217
                                          in
                                       let uu____6219 = add_goals [new_goal]
                                          in
                                       bind uu____6219
                                         (fun uu____6224  ->
                                            let uu____6225 =
                                              FStar_Syntax_Util.mk_eq2
                                                (FStar_Syntax_Syntax.U_succ u)
                                                ty
                                                bv.FStar_Syntax_Syntax.sort
                                                t'
                                               in
                                            add_irrelevant_goal
                                              "binder_retype equation" e0
                                              uu____6225
                                              goal.FStar_Tactics_Types.opts))))))
       in
    FStar_All.pipe_left (wrap_err "binder_retype") uu____6094
  
let (norm_binder_type :
  FStar_Syntax_Embeddings.norm_step Prims.list ->
    FStar_Syntax_Syntax.binder -> unit tac)
  =
  fun s  ->
    fun b  ->
      let uu____6248 =
        let uu____6251 = cur_goal ()  in
        bind uu____6251
          (fun goal  ->
             let uu____6260 = b  in
             match uu____6260 with
             | (bv,uu____6264) ->
                 let uu____6269 =
                   let uu____6278 = FStar_Tactics_Types.goal_env goal  in
                   split_env bv uu____6278  in
                 (match uu____6269 with
                  | FStar_Pervasives_Native.None  ->
                      fail "binder is not present in environment"
                  | FStar_Pervasives_Native.Some (e0,bvs) ->
                      let steps =
                        let uu____6302 =
                          FStar_TypeChecker_Normalize.tr_norm_steps s  in
                        FStar_List.append
                          [FStar_TypeChecker_Normalize.Reify;
                          FStar_TypeChecker_Normalize.UnfoldTac] uu____6302
                         in
                      let sort' =
                        normalize steps e0 bv.FStar_Syntax_Syntax.sort  in
                      let bv' =
                        let uu___389_6307 = bv  in
                        {
                          FStar_Syntax_Syntax.ppname =
                            (uu___389_6307.FStar_Syntax_Syntax.ppname);
                          FStar_Syntax_Syntax.index =
                            (uu___389_6307.FStar_Syntax_Syntax.index);
                          FStar_Syntax_Syntax.sort = sort'
                        }  in
                      let env' = push_bvs e0 (bv' :: bvs)  in
                      let uu____6309 =
                        FStar_Tactics_Types.goal_with_env goal env'  in
                      replace_cur uu____6309))
         in
      FStar_All.pipe_left (wrap_err "norm_binder_type") uu____6248
  
let (revert : unit -> unit tac) =
  fun uu____6320  ->
    let uu____6323 = cur_goal ()  in
    bind uu____6323
      (fun goal  ->
         let uu____6329 =
           let uu____6336 = FStar_Tactics_Types.goal_env goal  in
           FStar_TypeChecker_Env.pop_bv uu____6336  in
         match uu____6329 with
         | FStar_Pervasives_Native.None  ->
             fail "Cannot revert; empty context"
         | FStar_Pervasives_Native.Some (x,env') ->
             let typ' =
               let uu____6352 =
                 let uu____6355 = FStar_Tactics_Types.goal_type goal  in
                 FStar_Syntax_Syntax.mk_Total uu____6355  in
               FStar_Syntax_Util.arrow [(x, FStar_Pervasives_Native.None)]
                 uu____6352
                in
             let uu____6370 = new_uvar "revert" env' typ'  in
             bind uu____6370
               (fun uu____6385  ->
                  match uu____6385 with
                  | (r,u_r) ->
                      let uu____6394 =
                        let uu____6397 =
                          let uu____6398 =
                            let uu____6399 =
                              FStar_Tactics_Types.goal_type goal  in
                            uu____6399.FStar_Syntax_Syntax.pos  in
                          let uu____6402 =
                            let uu____6407 =
                              let uu____6408 =
                                let uu____6417 =
                                  FStar_Syntax_Syntax.bv_to_name x  in
                                FStar_Syntax_Syntax.as_arg uu____6417  in
                              [uu____6408]  in
                            FStar_Syntax_Syntax.mk_Tm_app r uu____6407  in
                          uu____6402 FStar_Pervasives_Native.None uu____6398
                           in
                        set_solution goal uu____6397  in
                      bind uu____6394
                        (fun uu____6438  ->
                           let g =
                             FStar_Tactics_Types.mk_goal env' u_r
                               goal.FStar_Tactics_Types.opts
                               goal.FStar_Tactics_Types.is_guard
                              in
                           replace_cur g)))
  
let (free_in :
  FStar_Syntax_Syntax.bv -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun bv  ->
    fun t  ->
      let uu____6450 = FStar_Syntax_Free.names t  in
      FStar_Util.set_mem bv uu____6450
  
let rec (clear : FStar_Syntax_Syntax.binder -> unit tac) =
  fun b  ->
    let bv = FStar_Pervasives_Native.fst b  in
    let uu____6465 = cur_goal ()  in
    bind uu____6465
      (fun goal  ->
         mlog
           (fun uu____6473  ->
              let uu____6474 = FStar_Syntax_Print.binder_to_string b  in
              let uu____6475 =
                let uu____6476 =
                  let uu____6477 =
                    let uu____6486 = FStar_Tactics_Types.goal_env goal  in
                    FStar_TypeChecker_Env.all_binders uu____6486  in
                  FStar_All.pipe_right uu____6477 FStar_List.length  in
                FStar_All.pipe_right uu____6476 FStar_Util.string_of_int  in
              FStar_Util.print2 "Clear of (%s), env has %s binders\n"
                uu____6474 uu____6475)
           (fun uu____6503  ->
              let uu____6504 =
                let uu____6513 = FStar_Tactics_Types.goal_env goal  in
                split_env bv uu____6513  in
              match uu____6504 with
              | FStar_Pervasives_Native.None  ->
                  fail "Cannot clear; binder not in environment"
              | FStar_Pervasives_Native.Some (e',bvs) ->
                  let rec check1 bvs1 =
                    match bvs1 with
                    | [] -> ret ()
                    | bv'::bvs2 ->
                        let uu____6552 =
                          free_in bv bv'.FStar_Syntax_Syntax.sort  in
                        if uu____6552
                        then
                          let uu____6555 =
                            let uu____6556 =
                              FStar_Syntax_Print.bv_to_string bv'  in
                            FStar_Util.format1
                              "Cannot clear; binder present in the type of %s"
                              uu____6556
                             in
                          fail uu____6555
                        else check1 bvs2
                     in
                  let uu____6558 =
                    let uu____6559 = FStar_Tactics_Types.goal_type goal  in
                    free_in bv uu____6559  in
                  if uu____6558
                  then fail "Cannot clear; binder present in goal"
                  else
                    (let uu____6563 = check1 bvs  in
                     bind uu____6563
                       (fun uu____6569  ->
                          let env' = push_bvs e' bvs  in
                          let uu____6571 =
                            let uu____6578 =
                              FStar_Tactics_Types.goal_type goal  in
                            new_uvar "clear.witness" env' uu____6578  in
                          bind uu____6571
                            (fun uu____6587  ->
                               match uu____6587 with
                               | (ut,uvar_ut) ->
                                   let uu____6596 = set_solution goal ut  in
                                   bind uu____6596
                                     (fun uu____6601  ->
                                        let uu____6602 =
                                          FStar_Tactics_Types.mk_goal env'
                                            uvar_ut
                                            goal.FStar_Tactics_Types.opts
                                            goal.FStar_Tactics_Types.is_guard
                                           in
                                        replace_cur uu____6602))))))
  
let (clear_top : unit -> unit tac) =
  fun uu____6609  ->
    let uu____6612 = cur_goal ()  in
    bind uu____6612
      (fun goal  ->
         let uu____6618 =
           let uu____6625 = FStar_Tactics_Types.goal_env goal  in
           FStar_TypeChecker_Env.pop_bv uu____6625  in
         match uu____6618 with
         | FStar_Pervasives_Native.None  ->
             fail "Cannot clear; empty context"
         | FStar_Pervasives_Native.Some (x,uu____6633) ->
             let uu____6638 = FStar_Syntax_Syntax.mk_binder x  in
             clear uu____6638)
  
let (prune : Prims.string -> unit tac) =
  fun s  ->
    let uu____6648 = cur_goal ()  in
    bind uu____6648
      (fun g  ->
         let ctx = FStar_Tactics_Types.goal_env g  in
         let ctx' =
           let uu____6658 = FStar_Ident.path_of_text s  in
           FStar_TypeChecker_Env.rem_proof_ns ctx uu____6658  in
         let g' = FStar_Tactics_Types.goal_with_env g ctx'  in
         bind __dismiss (fun uu____6661  -> add_goals [g']))
  
let (addns : Prims.string -> unit tac) =
  fun s  ->
    let uu____6671 = cur_goal ()  in
    bind uu____6671
      (fun g  ->
         let ctx = FStar_Tactics_Types.goal_env g  in
         let ctx' =
           let uu____6681 = FStar_Ident.path_of_text s  in
           FStar_TypeChecker_Env.add_proof_ns ctx uu____6681  in
         let g' = FStar_Tactics_Types.goal_with_env g ctx'  in
         bind __dismiss (fun uu____6684  -> add_goals [g']))
  
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
            let uu____6724 = FStar_Syntax_Subst.compress t  in
            uu____6724.FStar_Syntax_Syntax.n  in
          let uu____6727 =
            if d = FStar_Tactics_Types.TopDown
            then
              f env
                (let uu___393_6733 = t  in
                 {
                   FStar_Syntax_Syntax.n = tn;
                   FStar_Syntax_Syntax.pos =
                     (uu___393_6733.FStar_Syntax_Syntax.pos);
                   FStar_Syntax_Syntax.vars =
                     (uu___393_6733.FStar_Syntax_Syntax.vars)
                 })
            else ret t  in
          bind uu____6727
            (fun t1  ->
               let ff = tac_fold_env d f env  in
               let tn1 =
                 let uu____6749 =
                   let uu____6750 = FStar_Syntax_Subst.compress t1  in
                   uu____6750.FStar_Syntax_Syntax.n  in
                 match uu____6749 with
                 | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
                     let uu____6781 = ff hd1  in
                     bind uu____6781
                       (fun hd2  ->
                          let fa uu____6807 =
                            match uu____6807 with
                            | (a,q) ->
                                let uu____6828 = ff a  in
                                bind uu____6828 (fun a1  -> ret (a1, q))
                             in
                          let uu____6847 = mapM fa args  in
                          bind uu____6847
                            (fun args1  ->
                               ret (FStar_Syntax_Syntax.Tm_app (hd2, args1))))
                 | FStar_Syntax_Syntax.Tm_abs (bs,t2,k) ->
                     let uu____6929 = FStar_Syntax_Subst.open_term bs t2  in
                     (match uu____6929 with
                      | (bs1,t') ->
                          let uu____6938 =
                            let uu____6941 =
                              FStar_TypeChecker_Env.push_binders env bs1  in
                            tac_fold_env d f uu____6941 t'  in
                          bind uu____6938
                            (fun t''  ->
                               let uu____6945 =
                                 let uu____6946 =
                                   let uu____6965 =
                                     FStar_Syntax_Subst.close_binders bs1  in
                                   let uu____6974 =
                                     FStar_Syntax_Subst.close bs1 t''  in
                                   (uu____6965, uu____6974, k)  in
                                 FStar_Syntax_Syntax.Tm_abs uu____6946  in
                               ret uu____6945))
                 | FStar_Syntax_Syntax.Tm_arrow (bs,k) -> ret tn
                 | FStar_Syntax_Syntax.Tm_match (hd1,brs) ->
                     let uu____7049 = ff hd1  in
                     bind uu____7049
                       (fun hd2  ->
                          let ffb br =
                            let uu____7064 =
                              FStar_Syntax_Subst.open_branch br  in
                            match uu____7064 with
                            | (pat,w,e) ->
                                let bvs = FStar_Syntax_Syntax.pat_bvs pat  in
                                let ff1 =
                                  let uu____7096 =
                                    FStar_TypeChecker_Env.push_bvs env bvs
                                     in
                                  tac_fold_env d f uu____7096  in
                                let uu____7097 = ff1 e  in
                                bind uu____7097
                                  (fun e1  ->
                                     let br1 =
                                       FStar_Syntax_Subst.close_branch
                                         (pat, w, e1)
                                        in
                                     ret br1)
                             in
                          let uu____7112 = mapM ffb brs  in
                          bind uu____7112
                            (fun brs1  ->
                               ret (FStar_Syntax_Syntax.Tm_match (hd2, brs1))))
                 | FStar_Syntax_Syntax.Tm_let
                     ((false
                       ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inl bv;
                          FStar_Syntax_Syntax.lbunivs = uu____7156;
                          FStar_Syntax_Syntax.lbtyp = uu____7157;
                          FStar_Syntax_Syntax.lbeff = uu____7158;
                          FStar_Syntax_Syntax.lbdef = def;
                          FStar_Syntax_Syntax.lbattrs = uu____7160;
                          FStar_Syntax_Syntax.lbpos = uu____7161;_}::[]),e)
                     ->
                     let lb =
                       let uu____7186 =
                         let uu____7187 = FStar_Syntax_Subst.compress t1  in
                         uu____7187.FStar_Syntax_Syntax.n  in
                       match uu____7186 with
                       | FStar_Syntax_Syntax.Tm_let
                           ((false ,lb::[]),uu____7191) -> lb
                       | uu____7204 -> failwith "impossible"  in
                     let fflb lb1 =
                       let uu____7213 = ff lb1.FStar_Syntax_Syntax.lbdef  in
                       bind uu____7213
                         (fun def1  ->
                            ret
                              (let uu___390_7219 = lb1  in
                               {
                                 FStar_Syntax_Syntax.lbname =
                                   (uu___390_7219.FStar_Syntax_Syntax.lbname);
                                 FStar_Syntax_Syntax.lbunivs =
                                   (uu___390_7219.FStar_Syntax_Syntax.lbunivs);
                                 FStar_Syntax_Syntax.lbtyp =
                                   (uu___390_7219.FStar_Syntax_Syntax.lbtyp);
                                 FStar_Syntax_Syntax.lbeff =
                                   (uu___390_7219.FStar_Syntax_Syntax.lbeff);
                                 FStar_Syntax_Syntax.lbdef = def1;
                                 FStar_Syntax_Syntax.lbattrs =
                                   (uu___390_7219.FStar_Syntax_Syntax.lbattrs);
                                 FStar_Syntax_Syntax.lbpos =
                                   (uu___390_7219.FStar_Syntax_Syntax.lbpos)
                               }))
                        in
                     let uu____7220 = fflb lb  in
                     bind uu____7220
                       (fun lb1  ->
                          let uu____7230 =
                            let uu____7235 =
                              let uu____7236 =
                                FStar_Syntax_Syntax.mk_binder bv  in
                              [uu____7236]  in
                            FStar_Syntax_Subst.open_term uu____7235 e  in
                          match uu____7230 with
                          | (bs,e1) ->
                              let ff1 =
                                let uu____7266 =
                                  FStar_TypeChecker_Env.push_binders env bs
                                   in
                                tac_fold_env d f uu____7266  in
                              let uu____7267 = ff1 e1  in
                              bind uu____7267
                                (fun e2  ->
                                   let e3 = FStar_Syntax_Subst.close bs e2
                                      in
                                   ret
                                     (FStar_Syntax_Syntax.Tm_let
                                        ((false, [lb1]), e3))))
                 | FStar_Syntax_Syntax.Tm_let ((true ,lbs),e) ->
                     let fflb lb =
                       let uu____7308 = ff lb.FStar_Syntax_Syntax.lbdef  in
                       bind uu____7308
                         (fun def  ->
                            ret
                              (let uu___391_7314 = lb  in
                               {
                                 FStar_Syntax_Syntax.lbname =
                                   (uu___391_7314.FStar_Syntax_Syntax.lbname);
                                 FStar_Syntax_Syntax.lbunivs =
                                   (uu___391_7314.FStar_Syntax_Syntax.lbunivs);
                                 FStar_Syntax_Syntax.lbtyp =
                                   (uu___391_7314.FStar_Syntax_Syntax.lbtyp);
                                 FStar_Syntax_Syntax.lbeff =
                                   (uu___391_7314.FStar_Syntax_Syntax.lbeff);
                                 FStar_Syntax_Syntax.lbdef = def;
                                 FStar_Syntax_Syntax.lbattrs =
                                   (uu___391_7314.FStar_Syntax_Syntax.lbattrs);
                                 FStar_Syntax_Syntax.lbpos =
                                   (uu___391_7314.FStar_Syntax_Syntax.lbpos)
                               }))
                        in
                     let uu____7315 = FStar_Syntax_Subst.open_let_rec lbs e
                        in
                     (match uu____7315 with
                      | (lbs1,e1) ->
                          let uu____7330 = mapM fflb lbs1  in
                          bind uu____7330
                            (fun lbs2  ->
                               let uu____7342 = ff e1  in
                               bind uu____7342
                                 (fun e2  ->
                                    let uu____7350 =
                                      FStar_Syntax_Subst.close_let_rec lbs2
                                        e2
                                       in
                                    match uu____7350 with
                                    | (lbs3,e3) ->
                                        ret
                                          (FStar_Syntax_Syntax.Tm_let
                                             ((true, lbs3), e3)))))
                 | FStar_Syntax_Syntax.Tm_ascribed (t2,asc,eff) ->
                     let uu____7418 = ff t2  in
                     bind uu____7418
                       (fun t3  ->
                          ret
                            (FStar_Syntax_Syntax.Tm_ascribed (t3, asc, eff)))
                 | FStar_Syntax_Syntax.Tm_meta (t2,m) ->
                     let uu____7449 = ff t2  in
                     bind uu____7449
                       (fun t3  -> ret (FStar_Syntax_Syntax.Tm_meta (t3, m)))
                 | uu____7456 -> ret tn  in
               bind tn1
                 (fun tn2  ->
                    let t' =
                      let uu___392_7463 = t1  in
                      {
                        FStar_Syntax_Syntax.n = tn2;
                        FStar_Syntax_Syntax.pos =
                          (uu___392_7463.FStar_Syntax_Syntax.pos);
                        FStar_Syntax_Syntax.vars =
                          (uu___392_7463.FStar_Syntax_Syntax.vars)
                      }  in
                    if d = FStar_Tactics_Types.BottomUp
                    then f env t'
                    else ret t'))
  
let (pointwise_rec :
  FStar_Tactics_Types.proofstate ->
    unit tac ->
      FStar_Options.optionstate ->
        FStar_TypeChecker_Env.env ->
          FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term tac)
  =
  fun ps  ->
    fun tau  ->
      fun opts  ->
        fun env  ->
          fun t  ->
            let uu____7500 = FStar_TypeChecker_TcTerm.tc_term env t  in
            match uu____7500 with
            | (t1,lcomp,g) ->
                let uu____7512 =
                  (let uu____7515 =
                     FStar_Syntax_Util.is_pure_or_ghost_lcomp lcomp  in
                   Prims.op_Negation uu____7515) ||
                    (let uu____7517 = FStar_TypeChecker_Env.is_trivial g  in
                     Prims.op_Negation uu____7517)
                   in
                if uu____7512
                then ret t1
                else
                  (let rewrite_eq =
                     let typ = lcomp.FStar_Syntax_Syntax.res_typ  in
                     let uu____7525 = new_uvar "pointwise_rec" env typ  in
                     bind uu____7525
                       (fun uu____7541  ->
                          match uu____7541 with
                          | (ut,uvar_ut) ->
                              (log ps
                                 (fun uu____7554  ->
                                    let uu____7555 =
                                      FStar_Syntax_Print.term_to_string t1
                                       in
                                    let uu____7556 =
                                      FStar_Syntax_Print.term_to_string ut
                                       in
                                    FStar_Util.print2
                                      "Pointwise_rec: making equality\n\t%s ==\n\t%s\n"
                                      uu____7555 uu____7556);
                               (let uu____7557 =
                                  let uu____7560 =
                                    let uu____7561 =
                                      FStar_TypeChecker_TcTerm.universe_of
                                        env typ
                                       in
                                    FStar_Syntax_Util.mk_eq2 uu____7561 typ
                                      t1 ut
                                     in
                                  add_irrelevant_goal
                                    "pointwise_rec equation" env uu____7560
                                    opts
                                   in
                                bind uu____7557
                                  (fun uu____7564  ->
                                     let uu____7565 =
                                       bind tau
                                         (fun uu____7571  ->
                                            let ut1 =
                                              FStar_TypeChecker_Normalize.reduce_uvar_solutions
                                                env ut
                                               in
                                            log ps
                                              (fun uu____7577  ->
                                                 let uu____7578 =
                                                   FStar_Syntax_Print.term_to_string
                                                     t1
                                                    in
                                                 let uu____7579 =
                                                   FStar_Syntax_Print.term_to_string
                                                     ut1
                                                    in
                                                 FStar_Util.print2
                                                   "Pointwise_rec: succeeded rewriting\n\t%s to\n\t%s\n"
                                                   uu____7578 uu____7579);
                                            ret ut1)
                                        in
                                     focus uu____7565))))
                      in
                   let uu____7580 = trytac' rewrite_eq  in
                   bind uu____7580
                     (fun x  ->
                        match x with
                        | FStar_Util.Inl "SKIP" -> ret t1
                        | FStar_Util.Inl e -> fail e
                        | FStar_Util.Inr x1 -> ret x1))
  
type ctrl = FStar_BigInt.t
let (keepGoing : ctrl) = FStar_BigInt.zero 
let (proceedToNextSubtree : FStar_BigInt.bigint) = FStar_BigInt.one 
let (globalStop : FStar_BigInt.bigint) =
  FStar_BigInt.succ_big_int FStar_BigInt.one 
type rewrite_result = Prims.bool
let (skipThisTerm : Prims.bool) = false 
let (rewroteThisTerm : Prims.bool) = true 
type 'a ctrl_tac = ('a,ctrl) FStar_Pervasives_Native.tuple2 tac
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
          let uu____7778 = FStar_Syntax_Subst.compress t  in
          maybe_continue ctrl uu____7778
            (fun t1  ->
               let uu____7786 =
                 f env
                   (let uu___396_7795 = t1  in
                    {
                      FStar_Syntax_Syntax.n = (t1.FStar_Syntax_Syntax.n);
                      FStar_Syntax_Syntax.pos =
                        (uu___396_7795.FStar_Syntax_Syntax.pos);
                      FStar_Syntax_Syntax.vars =
                        (uu___396_7795.FStar_Syntax_Syntax.vars)
                    })
                  in
               bind uu____7786
                 (fun uu____7811  ->
                    match uu____7811 with
                    | (t2,ctrl1) ->
                        maybe_continue ctrl1 t2
                          (fun t3  ->
                             let uu____7834 =
                               let uu____7835 =
                                 FStar_Syntax_Subst.compress t3  in
                               uu____7835.FStar_Syntax_Syntax.n  in
                             match uu____7834 with
                             | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
                                 let uu____7872 =
                                   ctrl_tac_fold f env ctrl1 hd1  in
                                 bind uu____7872
                                   (fun uu____7897  ->
                                      match uu____7897 with
                                      | (hd2,ctrl2) ->
                                          let ctrl3 = keep_going ctrl2  in
                                          let uu____7913 =
                                            ctrl_tac_fold_args f env ctrl3
                                              args
                                             in
                                          bind uu____7913
                                            (fun uu____7940  ->
                                               match uu____7940 with
                                               | (args1,ctrl4) ->
                                                   ret
                                                     ((let uu___394_7970 = t3
                                                          in
                                                       {
                                                         FStar_Syntax_Syntax.n
                                                           =
                                                           (FStar_Syntax_Syntax.Tm_app
                                                              (hd2, args1));
                                                         FStar_Syntax_Syntax.pos
                                                           =
                                                           (uu___394_7970.FStar_Syntax_Syntax.pos);
                                                         FStar_Syntax_Syntax.vars
                                                           =
                                                           (uu___394_7970.FStar_Syntax_Syntax.vars)
                                                       }), ctrl4)))
                             | FStar_Syntax_Syntax.Tm_abs (bs,t4,k) ->
                                 let uu____8012 =
                                   FStar_Syntax_Subst.open_term bs t4  in
                                 (match uu____8012 with
                                  | (bs1,t') ->
                                      let uu____8027 =
                                        let uu____8034 =
                                          FStar_TypeChecker_Env.push_binders
                                            env bs1
                                           in
                                        ctrl_tac_fold f uu____8034 ctrl1 t'
                                         in
                                      bind uu____8027
                                        (fun uu____8052  ->
                                           match uu____8052 with
                                           | (t'',ctrl2) ->
                                               let uu____8067 =
                                                 let uu____8074 =
                                                   let uu___395_8077 = t4  in
                                                   let uu____8080 =
                                                     let uu____8081 =
                                                       let uu____8100 =
                                                         FStar_Syntax_Subst.close_binders
                                                           bs1
                                                          in
                                                       let uu____8109 =
                                                         FStar_Syntax_Subst.close
                                                           bs1 t''
                                                          in
                                                       (uu____8100,
                                                         uu____8109, k)
                                                        in
                                                     FStar_Syntax_Syntax.Tm_abs
                                                       uu____8081
                                                      in
                                                   {
                                                     FStar_Syntax_Syntax.n =
                                                       uu____8080;
                                                     FStar_Syntax_Syntax.pos
                                                       =
                                                       (uu___395_8077.FStar_Syntax_Syntax.pos);
                                                     FStar_Syntax_Syntax.vars
                                                       =
                                                       (uu___395_8077.FStar_Syntax_Syntax.vars)
                                                   }  in
                                                 (uu____8074, ctrl2)  in
                                               ret uu____8067))
                             | FStar_Syntax_Syntax.Tm_arrow (bs,k) ->
                                 ret (t3, ctrl1)
                             | uu____8162 -> ret (t3, ctrl1))))

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
              let uu____8209 = ctrl_tac_fold f env ctrl t  in
              bind uu____8209
                (fun uu____8233  ->
                   match uu____8233 with
                   | (t1,ctrl1) ->
                       let uu____8248 = ctrl_tac_fold_args f env ctrl1 ts1
                          in
                       bind uu____8248
                         (fun uu____8275  ->
                            match uu____8275 with
                            | (ts2,ctrl2) -> ret (((t1, q) :: ts2), ctrl2)))

let (rewrite_rec :
  FStar_Tactics_Types.proofstate ->
    (FStar_Syntax_Syntax.term -> rewrite_result ctrl_tac) ->
      unit tac ->
        FStar_Options.optionstate ->
          FStar_TypeChecker_Env.env ->
            FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term ctrl_tac)
  =
  fun ps  ->
    fun ctrl  ->
      fun rewriter  ->
        fun opts  ->
          fun env  ->
            fun t  ->
              let t1 = FStar_Syntax_Subst.compress t  in
              let uu____8359 =
                let uu____8366 =
                  add_irrelevant_goal "dummy" env FStar_Syntax_Util.t_true
                    opts
                   in
                bind uu____8366
                  (fun uu____8375  ->
                     let uu____8376 = ctrl t1  in
                     bind uu____8376
                       (fun res  ->
                          let uu____8399 = trivial ()  in
                          bind uu____8399 (fun uu____8407  -> ret res)))
                 in
              bind uu____8359
                (fun uu____8423  ->
                   match uu____8423 with
                   | (should_rewrite,ctrl1) ->
                       if Prims.op_Negation should_rewrite
                       then ret (t1, ctrl1)
                       else
                         (let uu____8447 =
                            FStar_TypeChecker_TcTerm.tc_term env t1  in
                          match uu____8447 with
                          | (t2,lcomp,g) ->
                              let uu____8463 =
                                (let uu____8466 =
                                   FStar_Syntax_Util.is_pure_or_ghost_lcomp
                                     lcomp
                                    in
                                 Prims.op_Negation uu____8466) ||
                                  (let uu____8468 =
                                     FStar_TypeChecker_Env.is_trivial g  in
                                   Prims.op_Negation uu____8468)
                                 in
                              if uu____8463
                              then ret (t2, globalStop)
                              else
                                (let typ = lcomp.FStar_Syntax_Syntax.res_typ
                                    in
                                 let uu____8481 =
                                   new_uvar "pointwise_rec" env typ  in
                                 bind uu____8481
                                   (fun uu____8501  ->
                                      match uu____8501 with
                                      | (ut,uvar_ut) ->
                                          (log ps
                                             (fun uu____8518  ->
                                                let uu____8519 =
                                                  FStar_Syntax_Print.term_to_string
                                                    t2
                                                   in
                                                let uu____8520 =
                                                  FStar_Syntax_Print.term_to_string
                                                    ut
                                                   in
                                                FStar_Util.print2
                                                  "Pointwise_rec: making equality\n\t%s ==\n\t%s\n"
                                                  uu____8519 uu____8520);
                                           (let uu____8521 =
                                              let uu____8524 =
                                                let uu____8525 =
                                                  FStar_TypeChecker_TcTerm.universe_of
                                                    env typ
                                                   in
                                                FStar_Syntax_Util.mk_eq2
                                                  uu____8525 typ t2 ut
                                                 in
                                              add_irrelevant_goal
                                                "rewrite_rec equation" env
                                                uu____8524 opts
                                               in
                                            bind uu____8521
                                              (fun uu____8532  ->
                                                 let uu____8533 =
                                                   bind rewriter
                                                     (fun uu____8547  ->
                                                        let ut1 =
                                                          FStar_TypeChecker_Normalize.reduce_uvar_solutions
                                                            env ut
                                                           in
                                                        log ps
                                                          (fun uu____8553  ->
                                                             let uu____8554 =
                                                               FStar_Syntax_Print.term_to_string
                                                                 t2
                                                                in
                                                             let uu____8555 =
                                                               FStar_Syntax_Print.term_to_string
                                                                 ut1
                                                                in
                                                             FStar_Util.print2
                                                               "rewrite_rec: succeeded rewriting\n\t%s to\n\t%s\n"
                                                               uu____8554
                                                               uu____8555);
                                                        ret (ut1, ctrl1))
                                                    in
                                                 focus uu____8533)))))))
  
let (topdown_rewrite :
  (FStar_Syntax_Syntax.term ->
     (Prims.bool,FStar_BigInt.t) FStar_Pervasives_Native.tuple2 tac)
    -> unit tac -> unit tac)
  =
  fun ctrl  ->
    fun rewriter  ->
      let uu____8596 =
        bind get
          (fun ps  ->
             let uu____8606 =
               match ps.FStar_Tactics_Types.goals with
               | g::gs -> (g, gs)
               | [] -> failwith "no goals"  in
             match uu____8606 with
             | (g,gs) ->
                 let gt1 = FStar_Tactics_Types.goal_type g  in
                 (log ps
                    (fun uu____8643  ->
                       let uu____8644 = FStar_Syntax_Print.term_to_string gt1
                          in
                       FStar_Util.print1 "Topdown_rewrite starting with %s\n"
                         uu____8644);
                  bind dismiss_all
                    (fun uu____8647  ->
                       let uu____8648 =
                         let uu____8655 = FStar_Tactics_Types.goal_env g  in
                         ctrl_tac_fold
                           (rewrite_rec ps ctrl rewriter
                              g.FStar_Tactics_Types.opts) uu____8655
                           keepGoing gt1
                          in
                       bind uu____8648
                         (fun uu____8667  ->
                            match uu____8667 with
                            | (gt',uu____8675) ->
                                (log ps
                                   (fun uu____8679  ->
                                      let uu____8680 =
                                        FStar_Syntax_Print.term_to_string gt'
                                         in
                                      FStar_Util.print1
                                        "Topdown_rewrite seems to have succeded with %s\n"
                                        uu____8680);
                                 (let uu____8681 = push_goals gs  in
                                  bind uu____8681
                                    (fun uu____8686  ->
                                       let uu____8687 =
                                         let uu____8690 =
                                           FStar_Tactics_Types.goal_with_type
                                             g gt'
                                            in
                                         [uu____8690]  in
                                       add_goals uu____8687)))))))
         in
      FStar_All.pipe_left (wrap_err "topdown_rewrite") uu____8596
  
let (pointwise : FStar_Tactics_Types.direction -> unit tac -> unit tac) =
  fun d  ->
    fun tau  ->
      let uu____8713 =
        bind get
          (fun ps  ->
             let uu____8723 =
               match ps.FStar_Tactics_Types.goals with
               | g::gs -> (g, gs)
               | [] -> failwith "no goals"  in
             match uu____8723 with
             | (g,gs) ->
                 let gt1 = FStar_Tactics_Types.goal_type g  in
                 (log ps
                    (fun uu____8760  ->
                       let uu____8761 = FStar_Syntax_Print.term_to_string gt1
                          in
                       FStar_Util.print1 "Pointwise starting with %s\n"
                         uu____8761);
                  bind dismiss_all
                    (fun uu____8764  ->
                       let uu____8765 =
                         let uu____8768 = FStar_Tactics_Types.goal_env g  in
                         tac_fold_env d
                           (pointwise_rec ps tau g.FStar_Tactics_Types.opts)
                           uu____8768 gt1
                          in
                       bind uu____8765
                         (fun gt'  ->
                            log ps
                              (fun uu____8776  ->
                                 let uu____8777 =
                                   FStar_Syntax_Print.term_to_string gt'  in
                                 FStar_Util.print1
                                   "Pointwise seems to have succeded with %s\n"
                                   uu____8777);
                            (let uu____8778 = push_goals gs  in
                             bind uu____8778
                               (fun uu____8783  ->
                                  let uu____8784 =
                                    let uu____8787 =
                                      FStar_Tactics_Types.goal_with_type g
                                        gt'
                                       in
                                    [uu____8787]  in
                                  add_goals uu____8784))))))
         in
      FStar_All.pipe_left (wrap_err "pointwise") uu____8713
  
let (trefl : unit -> unit tac) =
  fun uu____8798  ->
    let uu____8801 =
      let uu____8804 = cur_goal ()  in
      bind uu____8804
        (fun g  ->
           let uu____8822 =
             let uu____8827 = FStar_Tactics_Types.goal_type g  in
             FStar_Syntax_Util.un_squash uu____8827  in
           match uu____8822 with
           | FStar_Pervasives_Native.Some t ->
               let uu____8835 = FStar_Syntax_Util.head_and_args' t  in
               (match uu____8835 with
                | (hd1,args) ->
                    let uu____8874 =
                      let uu____8887 =
                        let uu____8888 = FStar_Syntax_Util.un_uinst hd1  in
                        uu____8888.FStar_Syntax_Syntax.n  in
                      (uu____8887, args)  in
                    (match uu____8874 with
                     | (FStar_Syntax_Syntax.Tm_fvar
                        fv,uu____8902::(l,uu____8904)::(r,uu____8906)::[])
                         when
                         FStar_Syntax_Syntax.fv_eq_lid fv
                           FStar_Parser_Const.eq2_lid
                         ->
                         let uu____8953 =
                           let uu____8956 = FStar_Tactics_Types.goal_env g
                              in
                           do_unify uu____8956 l r  in
                         bind uu____8953
                           (fun b  ->
                              if b
                              then solve' g FStar_Syntax_Util.exp_unit
                              else
                                (let l1 =
                                   let uu____8963 =
                                     FStar_Tactics_Types.goal_env g  in
                                   FStar_TypeChecker_Normalize.normalize
                                     [FStar_TypeChecker_Normalize.UnfoldUntil
                                        FStar_Syntax_Syntax.delta_constant;
                                     FStar_TypeChecker_Normalize.Primops;
                                     FStar_TypeChecker_Normalize.UnfoldTac]
                                     uu____8963 l
                                    in
                                 let r1 =
                                   let uu____8965 =
                                     FStar_Tactics_Types.goal_env g  in
                                   FStar_TypeChecker_Normalize.normalize
                                     [FStar_TypeChecker_Normalize.UnfoldUntil
                                        FStar_Syntax_Syntax.delta_constant;
                                     FStar_TypeChecker_Normalize.Primops;
                                     FStar_TypeChecker_Normalize.UnfoldTac]
                                     uu____8965 r
                                    in
                                 let uu____8966 =
                                   let uu____8969 =
                                     FStar_Tactics_Types.goal_env g  in
                                   do_unify uu____8969 l1 r1  in
                                 bind uu____8966
                                   (fun b1  ->
                                      if b1
                                      then
                                        solve' g FStar_Syntax_Util.exp_unit
                                      else
                                        (let uu____8975 =
                                           let uu____8976 =
                                             FStar_Tactics_Types.goal_env g
                                              in
                                           tts uu____8976 l1  in
                                         let uu____8977 =
                                           let uu____8978 =
                                             FStar_Tactics_Types.goal_env g
                                              in
                                           tts uu____8978 r1  in
                                         fail2
                                           "not a trivial equality ((%s) vs (%s))"
                                           uu____8975 uu____8977))))
                     | (hd2,uu____8980) ->
                         let uu____8997 =
                           let uu____8998 = FStar_Tactics_Types.goal_env g
                              in
                           tts uu____8998 t  in
                         fail1 "trefl: not an equality (%s)" uu____8997))
           | FStar_Pervasives_Native.None  -> fail "not an irrelevant goal")
       in
    FStar_All.pipe_left (wrap_err "trefl") uu____8801
  
let (dup : unit -> unit tac) =
  fun uu____9011  ->
    let uu____9014 = cur_goal ()  in
    bind uu____9014
      (fun g  ->
         let uu____9020 =
           let uu____9027 = FStar_Tactics_Types.goal_env g  in
           let uu____9028 = FStar_Tactics_Types.goal_type g  in
           new_uvar "dup" uu____9027 uu____9028  in
         bind uu____9020
           (fun uu____9037  ->
              match uu____9037 with
              | (u,u_uvar) ->
                  let g' =
                    let uu___397_9047 = g  in
                    {
                      FStar_Tactics_Types.goal_main_env =
                        (uu___397_9047.FStar_Tactics_Types.goal_main_env);
                      FStar_Tactics_Types.goal_ctx_uvar = u_uvar;
                      FStar_Tactics_Types.opts =
                        (uu___397_9047.FStar_Tactics_Types.opts);
                      FStar_Tactics_Types.is_guard =
                        (uu___397_9047.FStar_Tactics_Types.is_guard)
                    }  in
                  bind __dismiss
                    (fun uu____9050  ->
                       let uu____9051 =
                         let uu____9054 = FStar_Tactics_Types.goal_env g  in
                         let uu____9055 =
                           let uu____9056 =
                             let uu____9057 = FStar_Tactics_Types.goal_env g
                                in
                             let uu____9058 = FStar_Tactics_Types.goal_type g
                                in
                             FStar_TypeChecker_TcTerm.universe_of uu____9057
                               uu____9058
                              in
                           let uu____9059 = FStar_Tactics_Types.goal_type g
                              in
                           let uu____9060 =
                             FStar_Tactics_Types.goal_witness g  in
                           FStar_Syntax_Util.mk_eq2 uu____9056 uu____9059 u
                             uu____9060
                            in
                         add_irrelevant_goal "dup equation" uu____9054
                           uu____9055 g.FStar_Tactics_Types.opts
                          in
                       bind uu____9051
                         (fun uu____9063  ->
                            let uu____9064 = add_goals [g']  in
                            bind uu____9064 (fun uu____9068  -> ret ())))))
  
let (flip : unit -> unit tac) =
  fun uu____9075  ->
    bind get
      (fun ps  ->
         match ps.FStar_Tactics_Types.goals with
         | g1::g2::gs ->
             set
               (let uu___398_9092 = ps  in
                {
                  FStar_Tactics_Types.main_context =
                    (uu___398_9092.FStar_Tactics_Types.main_context);
                  FStar_Tactics_Types.main_goal =
                    (uu___398_9092.FStar_Tactics_Types.main_goal);
                  FStar_Tactics_Types.all_implicits =
                    (uu___398_9092.FStar_Tactics_Types.all_implicits);
                  FStar_Tactics_Types.goals = (g2 :: g1 :: gs);
                  FStar_Tactics_Types.smt_goals =
                    (uu___398_9092.FStar_Tactics_Types.smt_goals);
                  FStar_Tactics_Types.depth =
                    (uu___398_9092.FStar_Tactics_Types.depth);
                  FStar_Tactics_Types.__dump =
                    (uu___398_9092.FStar_Tactics_Types.__dump);
                  FStar_Tactics_Types.psc =
                    (uu___398_9092.FStar_Tactics_Types.psc);
                  FStar_Tactics_Types.entry_range =
                    (uu___398_9092.FStar_Tactics_Types.entry_range);
                  FStar_Tactics_Types.guard_policy =
                    (uu___398_9092.FStar_Tactics_Types.guard_policy);
                  FStar_Tactics_Types.freshness =
                    (uu___398_9092.FStar_Tactics_Types.freshness);
                  FStar_Tactics_Types.tac_verb_dbg =
                    (uu___398_9092.FStar_Tactics_Types.tac_verb_dbg)
                })
         | uu____9093 -> fail "flip: less than 2 goals")
  
let (later : unit -> unit tac) =
  fun uu____9102  ->
    bind get
      (fun ps  ->
         match ps.FStar_Tactics_Types.goals with
         | [] -> ret ()
         | g::gs ->
             set
               (let uu___399_9115 = ps  in
                {
                  FStar_Tactics_Types.main_context =
                    (uu___399_9115.FStar_Tactics_Types.main_context);
                  FStar_Tactics_Types.main_goal =
                    (uu___399_9115.FStar_Tactics_Types.main_goal);
                  FStar_Tactics_Types.all_implicits =
                    (uu___399_9115.FStar_Tactics_Types.all_implicits);
                  FStar_Tactics_Types.goals = (FStar_List.append gs [g]);
                  FStar_Tactics_Types.smt_goals =
                    (uu___399_9115.FStar_Tactics_Types.smt_goals);
                  FStar_Tactics_Types.depth =
                    (uu___399_9115.FStar_Tactics_Types.depth);
                  FStar_Tactics_Types.__dump =
                    (uu___399_9115.FStar_Tactics_Types.__dump);
                  FStar_Tactics_Types.psc =
                    (uu___399_9115.FStar_Tactics_Types.psc);
                  FStar_Tactics_Types.entry_range =
                    (uu___399_9115.FStar_Tactics_Types.entry_range);
                  FStar_Tactics_Types.guard_policy =
                    (uu___399_9115.FStar_Tactics_Types.guard_policy);
                  FStar_Tactics_Types.freshness =
                    (uu___399_9115.FStar_Tactics_Types.freshness);
                  FStar_Tactics_Types.tac_verb_dbg =
                    (uu___399_9115.FStar_Tactics_Types.tac_verb_dbg)
                }))
  
let (qed : unit -> unit tac) =
  fun uu____9122  ->
    bind get
      (fun ps  ->
         match ps.FStar_Tactics_Types.goals with
         | [] -> ret ()
         | uu____9129 -> fail "Not done!")
  
let (cases :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 tac)
  =
  fun t  ->
    let uu____9149 =
      let uu____9156 = cur_goal ()  in
      bind uu____9156
        (fun g  ->
           let uu____9166 =
             let uu____9175 = FStar_Tactics_Types.goal_env g  in
             __tc uu____9175 t  in
           bind uu____9166
             (fun uu____9203  ->
                match uu____9203 with
                | (t1,typ,guard) ->
                    let uu____9219 = FStar_Syntax_Util.head_and_args typ  in
                    (match uu____9219 with
                     | (hd1,args) ->
                         let uu____9268 =
                           let uu____9283 =
                             let uu____9284 = FStar_Syntax_Util.un_uinst hd1
                                in
                             uu____9284.FStar_Syntax_Syntax.n  in
                           (uu____9283, args)  in
                         (match uu____9268 with
                          | (FStar_Syntax_Syntax.Tm_fvar
                             fv,(p,uu____9305)::(q,uu____9307)::[]) when
                              FStar_Syntax_Syntax.fv_eq_lid fv
                                FStar_Parser_Const.or_lid
                              ->
                              let v_p =
                                FStar_Syntax_Syntax.new_bv
                                  FStar_Pervasives_Native.None p
                                 in
                              let v_q =
                                FStar_Syntax_Syntax.new_bv
                                  FStar_Pervasives_Native.None q
                                 in
                              let g1 =
                                let uu____9361 =
                                  let uu____9362 =
                                    FStar_Tactics_Types.goal_env g  in
                                  FStar_TypeChecker_Env.push_bv uu____9362
                                    v_p
                                   in
                                FStar_Tactics_Types.goal_with_env g
                                  uu____9361
                                 in
                              let g2 =
                                let uu____9364 =
                                  let uu____9365 =
                                    FStar_Tactics_Types.goal_env g  in
                                  FStar_TypeChecker_Env.push_bv uu____9365
                                    v_q
                                   in
                                FStar_Tactics_Types.goal_with_env g
                                  uu____9364
                                 in
                              bind __dismiss
                                (fun uu____9372  ->
                                   let uu____9373 = add_goals [g1; g2]  in
                                   bind uu____9373
                                     (fun uu____9382  ->
                                        let uu____9383 =
                                          let uu____9388 =
                                            FStar_Syntax_Syntax.bv_to_name
                                              v_p
                                             in
                                          let uu____9389 =
                                            FStar_Syntax_Syntax.bv_to_name
                                              v_q
                                             in
                                          (uu____9388, uu____9389)  in
                                        ret uu____9383))
                          | uu____9394 ->
                              let uu____9409 =
                                let uu____9410 =
                                  FStar_Tactics_Types.goal_env g  in
                                tts uu____9410 typ  in
                              fail1 "Not a disjunction: %s" uu____9409))))
       in
    FStar_All.pipe_left (wrap_err "cases") uu____9149
  
let (set_options : Prims.string -> unit tac) =
  fun s  ->
    let uu____9440 =
      let uu____9443 = cur_goal ()  in
      bind uu____9443
        (fun g  ->
           FStar_Options.push ();
           (let uu____9456 = FStar_Util.smap_copy g.FStar_Tactics_Types.opts
               in
            FStar_Options.set uu____9456);
           (let res = FStar_Options.set_options FStar_Options.Set s  in
            let opts' = FStar_Options.peek ()  in
            FStar_Options.pop ();
            (match res with
             | FStar_Getopt.Success  ->
                 let g' =
                   let uu___400_9463 = g  in
                   {
                     FStar_Tactics_Types.goal_main_env =
                       (uu___400_9463.FStar_Tactics_Types.goal_main_env);
                     FStar_Tactics_Types.goal_ctx_uvar =
                       (uu___400_9463.FStar_Tactics_Types.goal_ctx_uvar);
                     FStar_Tactics_Types.opts = opts';
                     FStar_Tactics_Types.is_guard =
                       (uu___400_9463.FStar_Tactics_Types.is_guard)
                   }  in
                 replace_cur g'
             | FStar_Getopt.Error err ->
                 fail2 "Setting options `%s` failed: %s" s err
             | FStar_Getopt.Help  ->
                 fail1 "Setting options `%s` failed (got `Help`?)" s)))
       in
    FStar_All.pipe_left (wrap_err "set_options") uu____9440
  
let (top_env : unit -> env tac) =
  fun uu____9475  ->
    bind get
      (fun ps  -> FStar_All.pipe_left ret ps.FStar_Tactics_Types.main_context)
  
let (cur_env : unit -> env tac) =
  fun uu____9488  ->
    let uu____9491 = cur_goal ()  in
    bind uu____9491
      (fun g  ->
         let uu____9497 = FStar_Tactics_Types.goal_env g  in
         FStar_All.pipe_left ret uu____9497)
  
let (cur_goal' : unit -> FStar_Syntax_Syntax.term tac) =
  fun uu____9506  ->
    let uu____9509 = cur_goal ()  in
    bind uu____9509
      (fun g  ->
         let uu____9515 = FStar_Tactics_Types.goal_type g  in
         FStar_All.pipe_left ret uu____9515)
  
let (cur_witness : unit -> FStar_Syntax_Syntax.term tac) =
  fun uu____9524  ->
    let uu____9527 = cur_goal ()  in
    bind uu____9527
      (fun g  ->
         let uu____9533 = FStar_Tactics_Types.goal_witness g  in
         FStar_All.pipe_left ret uu____9533)
  
let (lax_on : unit -> Prims.bool tac) =
  fun uu____9542  ->
    let uu____9545 = cur_env ()  in
    bind uu____9545
      (fun e  ->
         let uu____9551 =
           (FStar_Options.lax ()) || e.FStar_TypeChecker_Env.lax  in
         ret uu____9551)
  
let (unquote :
  FStar_Reflection_Data.typ ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term tac)
  =
  fun ty  ->
    fun tm  ->
      let uu____9566 =
        mlog
          (fun uu____9571  ->
             let uu____9572 = FStar_Syntax_Print.term_to_string tm  in
             FStar_Util.print1 "unquote: tm = %s\n" uu____9572)
          (fun uu____9575  ->
             let uu____9576 = cur_goal ()  in
             bind uu____9576
               (fun goal  ->
                  let env =
                    let uu____9584 = FStar_Tactics_Types.goal_env goal  in
                    FStar_TypeChecker_Env.set_expected_typ uu____9584 ty  in
                  let uu____9585 = __tc env tm  in
                  bind uu____9585
                    (fun uu____9604  ->
                       match uu____9604 with
                       | (tm1,typ,guard) ->
                           mlog
                             (fun uu____9618  ->
                                let uu____9619 =
                                  FStar_Syntax_Print.term_to_string tm1  in
                                FStar_Util.print1 "unquote: tm' = %s\n"
                                  uu____9619)
                             (fun uu____9621  ->
                                mlog
                                  (fun uu____9624  ->
                                     let uu____9625 =
                                       FStar_Syntax_Print.term_to_string typ
                                        in
                                     FStar_Util.print1 "unquote: typ = %s\n"
                                       uu____9625)
                                  (fun uu____9628  ->
                                     let uu____9629 =
                                       proc_guard "unquote" env guard  in
                                     bind uu____9629
                                       (fun uu____9633  -> ret tm1))))))
         in
      FStar_All.pipe_left (wrap_err "unquote") uu____9566
  
let (uvar_env :
  env ->
    FStar_Reflection_Data.typ FStar_Pervasives_Native.option ->
      FStar_Syntax_Syntax.term tac)
  =
  fun env  ->
    fun ty  ->
      let uu____9656 =
        match ty with
        | FStar_Pervasives_Native.Some ty1 -> ret ty1
        | FStar_Pervasives_Native.None  ->
            let uu____9662 =
              let uu____9669 =
                let uu____9670 = FStar_Syntax_Util.type_u ()  in
                FStar_All.pipe_left FStar_Pervasives_Native.fst uu____9670
                 in
              new_uvar "uvar_env.2" env uu____9669  in
            bind uu____9662
              (fun uu____9686  ->
                 match uu____9686 with | (typ,uvar_typ) -> ret typ)
         in
      bind uu____9656
        (fun typ  ->
           let uu____9698 = new_uvar "uvar_env" env typ  in
           bind uu____9698
             (fun uu____9712  -> match uu____9712 with | (t,uvar_t) -> ret t))
  
let (unshelve : FStar_Syntax_Syntax.term -> unit tac) =
  fun t  ->
    let uu____9730 =
      bind get
        (fun ps  ->
           let env = ps.FStar_Tactics_Types.main_context  in
           let opts =
             match ps.FStar_Tactics_Types.goals with
             | g::uu____9749 -> g.FStar_Tactics_Types.opts
             | uu____9752 -> FStar_Options.peek ()  in
           let uu____9755 = FStar_Syntax_Util.head_and_args t  in
           match uu____9755 with
           | ({
                FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                  (ctx_uvar,uu____9775);
                FStar_Syntax_Syntax.pos = uu____9776;
                FStar_Syntax_Syntax.vars = uu____9777;_},uu____9778)
               ->
               let env1 =
                 let uu___401_9820 = env  in
                 {
                   FStar_TypeChecker_Env.solver =
                     (uu___401_9820.FStar_TypeChecker_Env.solver);
                   FStar_TypeChecker_Env.range =
                     (uu___401_9820.FStar_TypeChecker_Env.range);
                   FStar_TypeChecker_Env.curmodule =
                     (uu___401_9820.FStar_TypeChecker_Env.curmodule);
                   FStar_TypeChecker_Env.gamma =
                     (ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_gamma);
                   FStar_TypeChecker_Env.gamma_sig =
                     (uu___401_9820.FStar_TypeChecker_Env.gamma_sig);
                   FStar_TypeChecker_Env.gamma_cache =
                     (uu___401_9820.FStar_TypeChecker_Env.gamma_cache);
                   FStar_TypeChecker_Env.modules =
                     (uu___401_9820.FStar_TypeChecker_Env.modules);
                   FStar_TypeChecker_Env.expected_typ =
                     (uu___401_9820.FStar_TypeChecker_Env.expected_typ);
                   FStar_TypeChecker_Env.sigtab =
                     (uu___401_9820.FStar_TypeChecker_Env.sigtab);
                   FStar_TypeChecker_Env.attrtab =
                     (uu___401_9820.FStar_TypeChecker_Env.attrtab);
                   FStar_TypeChecker_Env.is_pattern =
                     (uu___401_9820.FStar_TypeChecker_Env.is_pattern);
                   FStar_TypeChecker_Env.instantiate_imp =
                     (uu___401_9820.FStar_TypeChecker_Env.instantiate_imp);
                   FStar_TypeChecker_Env.effects =
                     (uu___401_9820.FStar_TypeChecker_Env.effects);
                   FStar_TypeChecker_Env.generalize =
                     (uu___401_9820.FStar_TypeChecker_Env.generalize);
                   FStar_TypeChecker_Env.letrecs =
                     (uu___401_9820.FStar_TypeChecker_Env.letrecs);
                   FStar_TypeChecker_Env.top_level =
                     (uu___401_9820.FStar_TypeChecker_Env.top_level);
                   FStar_TypeChecker_Env.check_uvars =
                     (uu___401_9820.FStar_TypeChecker_Env.check_uvars);
                   FStar_TypeChecker_Env.use_eq =
                     (uu___401_9820.FStar_TypeChecker_Env.use_eq);
                   FStar_TypeChecker_Env.is_iface =
                     (uu___401_9820.FStar_TypeChecker_Env.is_iface);
                   FStar_TypeChecker_Env.admit =
                     (uu___401_9820.FStar_TypeChecker_Env.admit);
                   FStar_TypeChecker_Env.lax =
                     (uu___401_9820.FStar_TypeChecker_Env.lax);
                   FStar_TypeChecker_Env.lax_universes =
                     (uu___401_9820.FStar_TypeChecker_Env.lax_universes);
                   FStar_TypeChecker_Env.phase1 =
                     (uu___401_9820.FStar_TypeChecker_Env.phase1);
                   FStar_TypeChecker_Env.failhard =
                     (uu___401_9820.FStar_TypeChecker_Env.failhard);
                   FStar_TypeChecker_Env.nosynth =
                     (uu___401_9820.FStar_TypeChecker_Env.nosynth);
                   FStar_TypeChecker_Env.uvar_subtyping =
                     (uu___401_9820.FStar_TypeChecker_Env.uvar_subtyping);
                   FStar_TypeChecker_Env.tc_term =
                     (uu___401_9820.FStar_TypeChecker_Env.tc_term);
                   FStar_TypeChecker_Env.type_of =
                     (uu___401_9820.FStar_TypeChecker_Env.type_of);
                   FStar_TypeChecker_Env.universe_of =
                     (uu___401_9820.FStar_TypeChecker_Env.universe_of);
                   FStar_TypeChecker_Env.check_type_of =
                     (uu___401_9820.FStar_TypeChecker_Env.check_type_of);
                   FStar_TypeChecker_Env.use_bv_sorts =
                     (uu___401_9820.FStar_TypeChecker_Env.use_bv_sorts);
                   FStar_TypeChecker_Env.qtbl_name_and_index =
                     (uu___401_9820.FStar_TypeChecker_Env.qtbl_name_and_index);
                   FStar_TypeChecker_Env.normalized_eff_names =
                     (uu___401_9820.FStar_TypeChecker_Env.normalized_eff_names);
                   FStar_TypeChecker_Env.proof_ns =
                     (uu___401_9820.FStar_TypeChecker_Env.proof_ns);
                   FStar_TypeChecker_Env.synth_hook =
                     (uu___401_9820.FStar_TypeChecker_Env.synth_hook);
                   FStar_TypeChecker_Env.splice =
                     (uu___401_9820.FStar_TypeChecker_Env.splice);
                   FStar_TypeChecker_Env.is_native_tactic =
                     (uu___401_9820.FStar_TypeChecker_Env.is_native_tactic);
                   FStar_TypeChecker_Env.identifier_info =
                     (uu___401_9820.FStar_TypeChecker_Env.identifier_info);
                   FStar_TypeChecker_Env.tc_hooks =
                     (uu___401_9820.FStar_TypeChecker_Env.tc_hooks);
                   FStar_TypeChecker_Env.dsenv =
                     (uu___401_9820.FStar_TypeChecker_Env.dsenv);
                   FStar_TypeChecker_Env.dep_graph =
                     (uu___401_9820.FStar_TypeChecker_Env.dep_graph)
                 }  in
               let g = FStar_Tactics_Types.mk_goal env1 ctx_uvar opts false
                  in
               let uu____9822 =
                 let uu____9825 = bnorm_goal g  in [uu____9825]  in
               add_goals uu____9822
           | uu____9826 -> fail "not a uvar")
       in
    FStar_All.pipe_left (wrap_err "unshelve") uu____9730
  
let (tac_and : Prims.bool tac -> Prims.bool tac -> Prims.bool tac) =
  fun t1  ->
    fun t2  ->
      let comp =
        bind t1
          (fun b  ->
             let uu____9875 = if b then t2 else ret false  in
             bind uu____9875 (fun b'  -> if b' then ret b' else fail ""))
         in
      let uu____9886 = trytac comp  in
      bind uu____9886
        (fun uu___342_9894  ->
           match uu___342_9894 with
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
        let uu____9920 =
          bind get
            (fun ps  ->
               let uu____9926 = __tc e t1  in
               bind uu____9926
                 (fun uu____9946  ->
                    match uu____9946 with
                    | (t11,ty1,g1) ->
                        let uu____9958 = __tc e t2  in
                        bind uu____9958
                          (fun uu____9978  ->
                             match uu____9978 with
                             | (t21,ty2,g2) ->
                                 let uu____9990 =
                                   proc_guard "unify_env g1" e g1  in
                                 bind uu____9990
                                   (fun uu____9995  ->
                                      let uu____9996 =
                                        proc_guard "unify_env g2" e g2  in
                                      bind uu____9996
                                        (fun uu____10002  ->
                                           let uu____10003 =
                                             do_unify e ty1 ty2  in
                                           let uu____10006 =
                                             do_unify e t11 t21  in
                                           tac_and uu____10003 uu____10006)))))
           in
        FStar_All.pipe_left (wrap_err "unify_env") uu____9920
  
let (launch_process :
  Prims.string -> Prims.string Prims.list -> Prims.string -> Prims.string tac)
  =
  fun prog  ->
    fun args  ->
      fun input  ->
        bind idtac
          (fun uu____10039  ->
             let uu____10040 = FStar_Options.unsafe_tactic_exec ()  in
             if uu____10040
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
        (fun uu____10061  ->
           let uu____10062 =
             FStar_Syntax_Syntax.gen_bv nm FStar_Pervasives_Native.None t  in
           ret uu____10062)
  
let (change : FStar_Reflection_Data.typ -> unit tac) =
  fun ty  ->
    let uu____10072 =
      mlog
        (fun uu____10077  ->
           let uu____10078 = FStar_Syntax_Print.term_to_string ty  in
           FStar_Util.print1 "change: ty = %s\n" uu____10078)
        (fun uu____10081  ->
           let uu____10082 = cur_goal ()  in
           bind uu____10082
             (fun g  ->
                let uu____10088 =
                  let uu____10097 = FStar_Tactics_Types.goal_env g  in
                  __tc uu____10097 ty  in
                bind uu____10088
                  (fun uu____10109  ->
                     match uu____10109 with
                     | (ty1,uu____10119,guard) ->
                         let uu____10121 =
                           let uu____10124 = FStar_Tactics_Types.goal_env g
                              in
                           proc_guard "change" uu____10124 guard  in
                         bind uu____10121
                           (fun uu____10127  ->
                              let uu____10128 =
                                let uu____10131 =
                                  FStar_Tactics_Types.goal_env g  in
                                let uu____10132 =
                                  FStar_Tactics_Types.goal_type g  in
                                do_unify uu____10131 uu____10132 ty1  in
                              bind uu____10128
                                (fun bb  ->
                                   if bb
                                   then
                                     let uu____10138 =
                                       FStar_Tactics_Types.goal_with_type g
                                         ty1
                                        in
                                     replace_cur uu____10138
                                   else
                                     (let steps =
                                        [FStar_TypeChecker_Normalize.Reify;
                                        FStar_TypeChecker_Normalize.UnfoldUntil
                                          FStar_Syntax_Syntax.delta_constant;
                                        FStar_TypeChecker_Normalize.AllowUnboundUniverses;
                                        FStar_TypeChecker_Normalize.Primops;
                                        FStar_TypeChecker_Normalize.Simplify;
                                        FStar_TypeChecker_Normalize.UnfoldTac;
                                        FStar_TypeChecker_Normalize.Unmeta]
                                         in
                                      let ng =
                                        let uu____10144 =
                                          FStar_Tactics_Types.goal_env g  in
                                        let uu____10145 =
                                          FStar_Tactics_Types.goal_type g  in
                                        normalize steps uu____10144
                                          uu____10145
                                         in
                                      let nty =
                                        let uu____10147 =
                                          FStar_Tactics_Types.goal_env g  in
                                        normalize steps uu____10147 ty1  in
                                      let uu____10148 =
                                        let uu____10151 =
                                          FStar_Tactics_Types.goal_env g  in
                                        do_unify uu____10151 ng nty  in
                                      bind uu____10148
                                        (fun b  ->
                                           if b
                                           then
                                             let uu____10157 =
                                               FStar_Tactics_Types.goal_with_type
                                                 g ty1
                                                in
                                             replace_cur uu____10157
                                           else fail "not convertible")))))))
       in
    FStar_All.pipe_left (wrap_err "change") uu____10072
  
let failwhen : 'a . Prims.bool -> Prims.string -> (unit -> 'a tac) -> 'a tac
  = fun b  -> fun msg  -> fun k  -> if b then fail msg else k () 
let (t_destruct :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.fv,FStar_BigInt.t) FStar_Pervasives_Native.tuple2
      Prims.list tac)
  =
  fun s_tm  ->
    let uu____10220 =
      let uu____10229 = cur_goal ()  in
      bind uu____10229
        (fun g  ->
           let uu____10241 =
             let uu____10250 = FStar_Tactics_Types.goal_env g  in
             __tc uu____10250 s_tm  in
           bind uu____10241
             (fun uu____10268  ->
                match uu____10268 with
                | (s_tm1,s_ty,guard) ->
                    let uu____10286 =
                      let uu____10289 = FStar_Tactics_Types.goal_env g  in
                      proc_guard "destruct" uu____10289 guard  in
                    bind uu____10286
                      (fun uu____10301  ->
                         let uu____10302 =
                           FStar_Syntax_Util.head_and_args' s_ty  in
                         match uu____10302 with
                         | (h,args) ->
                             let uu____10347 =
                               let uu____10354 =
                                 let uu____10355 =
                                   FStar_Syntax_Subst.compress h  in
                                 uu____10355.FStar_Syntax_Syntax.n  in
                               match uu____10354 with
                               | FStar_Syntax_Syntax.Tm_fvar fv ->
                                   ret (fv, [])
                               | FStar_Syntax_Syntax.Tm_uinst
                                   ({
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.Tm_fvar fv;
                                      FStar_Syntax_Syntax.pos = uu____10370;
                                      FStar_Syntax_Syntax.vars = uu____10371;_},us)
                                   -> ret (fv, us)
                               | uu____10381 -> fail "type is not an fv"  in
                             bind uu____10347
                               (fun uu____10401  ->
                                  match uu____10401 with
                                  | (fv,a_us) ->
                                      let t_lid =
                                        FStar_Syntax_Syntax.lid_of_fv fv  in
                                      let uu____10417 =
                                        let uu____10420 =
                                          FStar_Tactics_Types.goal_env g  in
                                        FStar_TypeChecker_Env.lookup_sigelt
                                          uu____10420 t_lid
                                         in
                                      (match uu____10417 with
                                       | FStar_Pervasives_Native.None  ->
                                           fail
                                             "type not found in environment"
                                       | FStar_Pervasives_Native.Some se ->
                                           (match se.FStar_Syntax_Syntax.sigel
                                            with
                                            | FStar_Syntax_Syntax.Sig_inductive_typ
                                                (_lid,t_us,t_ps,t_ty,mut,c_lids)
                                                ->
                                                failwhen
                                                  ((FStar_List.length a_us)
                                                     <>
                                                     (FStar_List.length t_us))
                                                  "t_us don't match?"
                                                  (fun uu____10469  ->
                                                     let uu____10470 =
                                                       FStar_Syntax_Subst.open_term
                                                         t_ps t_ty
                                                        in
                                                     match uu____10470 with
                                                     | (t_ps1,t_ty1) ->
                                                         let uu____10485 =
                                                           mapM
                                                             (fun c_lid  ->
                                                                let uu____10513
                                                                  =
                                                                  let uu____10516
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    g  in
                                                                  FStar_TypeChecker_Env.lookup_sigelt
                                                                    uu____10516
                                                                    c_lid
                                                                   in
                                                                match uu____10513
                                                                with
                                                                | FStar_Pervasives_Native.None
                                                                     ->
                                                                    fail
                                                                    "ctor not found?"
                                                                | FStar_Pervasives_Native.Some
                                                                    se1 ->
                                                                    (
                                                                    match 
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
                                                                    uu____10586
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
                                                                    let uu____10591
                                                                    =
                                                                    FStar_TypeChecker_Env.inst_tscheme
                                                                    (c_us,
                                                                    c_ty1)
                                                                     in
                                                                    match uu____10591
                                                                    with
                                                                    | 
                                                                    (c_us1,c_ty2)
                                                                    ->
                                                                    let uu____10614
                                                                    =
                                                                    FStar_Syntax_Util.arrow_formals_comp
                                                                    c_ty2  in
                                                                    (match uu____10614
                                                                    with
                                                                    | 
                                                                    (bs,comp)
                                                                    ->
                                                                    let uu____10657
                                                                    =
                                                                    FStar_List.splitAt
                                                                    nparam bs
                                                                     in
                                                                    (match uu____10657
                                                                    with
                                                                    | 
                                                                    (d_ps,bs1)
                                                                    ->
                                                                    let uu____10730
                                                                    =
                                                                    let uu____10731
                                                                    =
                                                                    FStar_Syntax_Util.is_total_comp
                                                                    comp  in
                                                                    Prims.op_Negation
                                                                    uu____10731
                                                                     in
                                                                    failwhen
                                                                    uu____10730
                                                                    "not total?"
                                                                    (fun
                                                                    uu____10748
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
                                                                    uu___343_10764
                                                                    =
                                                                    match uu___343_10764
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    (FStar_Syntax_Syntax.Implicit
                                                                    uu____10767)
                                                                    -> true
                                                                    | 
                                                                    uu____10768
                                                                    -> false
                                                                     in
                                                                    let uu____10771
                                                                    =
                                                                    FStar_List.splitAt
                                                                    nparam
                                                                    args  in
                                                                    match uu____10771
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
                                                                    uu____10904
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
                                                                    uu____10966
                                                                     ->
                                                                    match uu____10966
                                                                    with
                                                                    | 
                                                                    ((bv,uu____10986),
                                                                    (t,uu____10988))
                                                                    ->
                                                                    FStar_Syntax_Syntax.NT
                                                                    (bv, t))
                                                                    d_ps_a_ps
                                                                     in
                                                                    let bs2 =
                                                                    FStar_Syntax_Subst.subst_binders
                                                                    subst1
                                                                    bs1  in
                                                                    let subpats_1
                                                                    =
                                                                    FStar_List.map
                                                                    (fun
                                                                    uu____11056
                                                                     ->
                                                                    match uu____11056
                                                                    with
                                                                    | 
                                                                    ((bv,uu____11082),
                                                                    (t,uu____11084))
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
                                                                    uu____11139
                                                                     ->
                                                                    match uu____11139
                                                                    with
                                                                    | 
                                                                    (bv,aq)
                                                                    ->
                                                                    ((mk_pat
                                                                    (FStar_Syntax_Syntax.Pat_var
                                                                    bv)),
                                                                    (is_imp
                                                                    aq))) bs2
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
                                                                    env s_ty
                                                                     in
                                                                    let uu____11189
                                                                    =
                                                                    FStar_TypeChecker_TcTerm.tc_pat
                                                                    (let uu___402_11206
                                                                    = env  in
                                                                    {
                                                                    FStar_TypeChecker_Env.solver
                                                                    =
                                                                    (uu___402_11206.FStar_TypeChecker_Env.solver);
                                                                    FStar_TypeChecker_Env.range
                                                                    =
                                                                    (uu___402_11206.FStar_TypeChecker_Env.range);
                                                                    FStar_TypeChecker_Env.curmodule
                                                                    =
                                                                    (uu___402_11206.FStar_TypeChecker_Env.curmodule);
                                                                    FStar_TypeChecker_Env.gamma
                                                                    =
                                                                    (uu___402_11206.FStar_TypeChecker_Env.gamma);
                                                                    FStar_TypeChecker_Env.gamma_sig
                                                                    =
                                                                    (uu___402_11206.FStar_TypeChecker_Env.gamma_sig);
                                                                    FStar_TypeChecker_Env.gamma_cache
                                                                    =
                                                                    (uu___402_11206.FStar_TypeChecker_Env.gamma_cache);
                                                                    FStar_TypeChecker_Env.modules
                                                                    =
                                                                    (uu___402_11206.FStar_TypeChecker_Env.modules);
                                                                    FStar_TypeChecker_Env.expected_typ
                                                                    =
                                                                    (uu___402_11206.FStar_TypeChecker_Env.expected_typ);
                                                                    FStar_TypeChecker_Env.sigtab
                                                                    =
                                                                    (uu___402_11206.FStar_TypeChecker_Env.sigtab);
                                                                    FStar_TypeChecker_Env.attrtab
                                                                    =
                                                                    (uu___402_11206.FStar_TypeChecker_Env.attrtab);
                                                                    FStar_TypeChecker_Env.is_pattern
                                                                    =
                                                                    (uu___402_11206.FStar_TypeChecker_Env.is_pattern);
                                                                    FStar_TypeChecker_Env.instantiate_imp
                                                                    =
                                                                    (uu___402_11206.FStar_TypeChecker_Env.instantiate_imp);
                                                                    FStar_TypeChecker_Env.effects
                                                                    =
                                                                    (uu___402_11206.FStar_TypeChecker_Env.effects);
                                                                    FStar_TypeChecker_Env.generalize
                                                                    =
                                                                    (uu___402_11206.FStar_TypeChecker_Env.generalize);
                                                                    FStar_TypeChecker_Env.letrecs
                                                                    =
                                                                    (uu___402_11206.FStar_TypeChecker_Env.letrecs);
                                                                    FStar_TypeChecker_Env.top_level
                                                                    =
                                                                    (uu___402_11206.FStar_TypeChecker_Env.top_level);
                                                                    FStar_TypeChecker_Env.check_uvars
                                                                    =
                                                                    (uu___402_11206.FStar_TypeChecker_Env.check_uvars);
                                                                    FStar_TypeChecker_Env.use_eq
                                                                    =
                                                                    (uu___402_11206.FStar_TypeChecker_Env.use_eq);
                                                                    FStar_TypeChecker_Env.is_iface
                                                                    =
                                                                    (uu___402_11206.FStar_TypeChecker_Env.is_iface);
                                                                    FStar_TypeChecker_Env.admit
                                                                    =
                                                                    (uu___402_11206.FStar_TypeChecker_Env.admit);
                                                                    FStar_TypeChecker_Env.lax
                                                                    = true;
                                                                    FStar_TypeChecker_Env.lax_universes
                                                                    =
                                                                    (uu___402_11206.FStar_TypeChecker_Env.lax_universes);
                                                                    FStar_TypeChecker_Env.phase1
                                                                    =
                                                                    (uu___402_11206.FStar_TypeChecker_Env.phase1);
                                                                    FStar_TypeChecker_Env.failhard
                                                                    =
                                                                    (uu___402_11206.FStar_TypeChecker_Env.failhard);
                                                                    FStar_TypeChecker_Env.nosynth
                                                                    =
                                                                    (uu___402_11206.FStar_TypeChecker_Env.nosynth);
                                                                    FStar_TypeChecker_Env.uvar_subtyping
                                                                    =
                                                                    (uu___402_11206.FStar_TypeChecker_Env.uvar_subtyping);
                                                                    FStar_TypeChecker_Env.tc_term
                                                                    =
                                                                    (uu___402_11206.FStar_TypeChecker_Env.tc_term);
                                                                    FStar_TypeChecker_Env.type_of
                                                                    =
                                                                    (uu___402_11206.FStar_TypeChecker_Env.type_of);
                                                                    FStar_TypeChecker_Env.universe_of
                                                                    =
                                                                    (uu___402_11206.FStar_TypeChecker_Env.universe_of);
                                                                    FStar_TypeChecker_Env.check_type_of
                                                                    =
                                                                    (uu___402_11206.FStar_TypeChecker_Env.check_type_of);
                                                                    FStar_TypeChecker_Env.use_bv_sorts
                                                                    =
                                                                    (uu___402_11206.FStar_TypeChecker_Env.use_bv_sorts);
                                                                    FStar_TypeChecker_Env.qtbl_name_and_index
                                                                    =
                                                                    (uu___402_11206.FStar_TypeChecker_Env.qtbl_name_and_index);
                                                                    FStar_TypeChecker_Env.normalized_eff_names
                                                                    =
                                                                    (uu___402_11206.FStar_TypeChecker_Env.normalized_eff_names);
                                                                    FStar_TypeChecker_Env.proof_ns
                                                                    =
                                                                    (uu___402_11206.FStar_TypeChecker_Env.proof_ns);
                                                                    FStar_TypeChecker_Env.synth_hook
                                                                    =
                                                                    (uu___402_11206.FStar_TypeChecker_Env.synth_hook);
                                                                    FStar_TypeChecker_Env.splice
                                                                    =
                                                                    (uu___402_11206.FStar_TypeChecker_Env.splice);
                                                                    FStar_TypeChecker_Env.is_native_tactic
                                                                    =
                                                                    (uu___402_11206.FStar_TypeChecker_Env.is_native_tactic);
                                                                    FStar_TypeChecker_Env.identifier_info
                                                                    =
                                                                    (uu___402_11206.FStar_TypeChecker_Env.identifier_info);
                                                                    FStar_TypeChecker_Env.tc_hooks
                                                                    =
                                                                    (uu___402_11206.FStar_TypeChecker_Env.tc_hooks);
                                                                    FStar_TypeChecker_Env.dsenv
                                                                    =
                                                                    (uu___402_11206.FStar_TypeChecker_Env.dsenv);
                                                                    FStar_TypeChecker_Env.dep_graph
                                                                    =
                                                                    (uu___402_11206.FStar_TypeChecker_Env.dep_graph)
                                                                    }) true
                                                                    s_ty pat
                                                                     in
                                                                    match uu____11189
                                                                    with
                                                                    | 
                                                                    (uu____11219,uu____11220,uu____11221,pat_t,uu____11223,uu____11224)
                                                                    ->
                                                                    let eq_b
                                                                    =
                                                                    let uu____11230
                                                                    =
                                                                    let uu____11231
                                                                    =
                                                                    FStar_Syntax_Util.mk_eq2
                                                                    equ s_ty
                                                                    s_tm1
                                                                    pat_t  in
                                                                    FStar_Syntax_Util.mk_squash
                                                                    equ
                                                                    uu____11231
                                                                     in
                                                                    FStar_Syntax_Syntax.gen_bv
                                                                    "breq"
                                                                    FStar_Pervasives_Native.None
                                                                    uu____11230
                                                                     in
                                                                    let cod1
                                                                    =
                                                                    let uu____11235
                                                                    =
                                                                    let uu____11244
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_binder
                                                                    eq_b  in
                                                                    [uu____11244]
                                                                     in
                                                                    let uu____11263
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Total
                                                                    cod  in
                                                                    FStar_Syntax_Util.arrow
                                                                    uu____11235
                                                                    uu____11263
                                                                     in
                                                                    let nty =
                                                                    let uu____11269
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Total
                                                                    cod1  in
                                                                    FStar_Syntax_Util.arrow
                                                                    bs2
                                                                    uu____11269
                                                                     in
                                                                    let uu____11272
                                                                    =
                                                                    new_uvar
                                                                    "destruct branch"
                                                                    env nty
                                                                     in
                                                                    bind
                                                                    uu____11272
                                                                    (fun
                                                                    uu____11301
                                                                     ->
                                                                    match uu____11301
                                                                    with
                                                                    | 
                                                                    (uvt,uv)
                                                                    ->
                                                                    let g' =
                                                                    FStar_Tactics_Types.mk_goal
                                                                    env uv
                                                                    g.FStar_Tactics_Types.opts
                                                                    false  in
                                                                    let brt =
                                                                    FStar_Syntax_Util.mk_app_binders
                                                                    uvt bs2
                                                                     in
                                                                    let brt1
                                                                    =
                                                                    let uu____11327
                                                                    =
                                                                    let uu____11338
                                                                    =
                                                                    FStar_Syntax_Syntax.as_arg
                                                                    FStar_Syntax_Util.exp_unit
                                                                     in
                                                                    [uu____11338]
                                                                     in
                                                                    FStar_Syntax_Util.mk_app
                                                                    brt
                                                                    uu____11327
                                                                     in
                                                                    let br =
                                                                    FStar_Syntax_Subst.close_branch
                                                                    (pat,
                                                                    FStar_Pervasives_Native.None,
                                                                    brt1)  in
                                                                    let uu____11374
                                                                    =
                                                                    let uu____11385
                                                                    =
                                                                    let uu____11390
                                                                    =
                                                                    FStar_BigInt.of_int_fs
                                                                    (FStar_List.length
                                                                    bs2)  in
                                                                    (fv1,
                                                                    uu____11390)
                                                                     in
                                                                    (g', br,
                                                                    uu____11385)
                                                                     in
                                                                    ret
                                                                    uu____11374))))))
                                                                    | 
                                                                    uu____11411
                                                                    ->
                                                                    fail
                                                                    "impossible: not a ctor"))
                                                             c_lids
                                                            in
                                                         bind uu____10485
                                                           (fun goal_brs  ->
                                                              let uu____11460
                                                                =
                                                                FStar_List.unzip3
                                                                  goal_brs
                                                                 in
                                                              match uu____11460
                                                              with
                                                              | (goals,brs,infos)
                                                                  ->
                                                                  let w =
                                                                    FStar_Syntax_Syntax.mk
                                                                    (FStar_Syntax_Syntax.Tm_match
                                                                    (s_tm1,
                                                                    brs))
                                                                    FStar_Pervasives_Native.None
                                                                    s_tm1.FStar_Syntax_Syntax.pos
                                                                     in
                                                                  let uu____11533
                                                                    =
                                                                    solve' g
                                                                    w  in
                                                                  bind
                                                                    uu____11533
                                                                    (
                                                                    fun
                                                                    uu____11544
                                                                     ->
                                                                    let uu____11545
                                                                    =
                                                                    add_goals
                                                                    goals  in
                                                                    bind
                                                                    uu____11545
                                                                    (fun
                                                                    uu____11555
                                                                     ->
                                                                    ret infos))))
                                            | uu____11562 ->
                                                fail "not an inductive type"))))))
       in
    FStar_All.pipe_left (wrap_err "destruct") uu____10220
  
let rec last : 'a . 'a Prims.list -> 'a =
  fun l  ->
    match l with
    | [] -> failwith "last: empty list"
    | x::[] -> x
    | uu____11607::xs -> last xs
  
let rec init : 'a . 'a Prims.list -> 'a Prims.list =
  fun l  ->
    match l with
    | [] -> failwith "init: empty list"
    | x::[] -> []
    | x::xs -> let uu____11635 = init xs  in x :: uu____11635
  
let rec (inspect :
  FStar_Syntax_Syntax.term -> FStar_Reflection_Data.term_view tac) =
  fun t  ->
    let uu____11647 =
      let t1 = FStar_Syntax_Util.unascribe t  in
      let t2 = FStar_Syntax_Util.un_uinst t1  in
      match t2.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_meta (t3,uu____11655) -> inspect t3
      | FStar_Syntax_Syntax.Tm_name bv ->
          FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_Var bv)
      | FStar_Syntax_Syntax.Tm_bvar bv ->
          FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_BVar bv)
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_FVar fv)
      | FStar_Syntax_Syntax.Tm_app (hd1,[]) ->
          failwith "empty arguments on Tm_app"
      | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
          let uu____11720 = last args  in
          (match uu____11720 with
           | (a,q) ->
               let q' = FStar_Reflection_Basic.inspect_aqual q  in
               let uu____11750 =
                 let uu____11751 =
                   let uu____11756 =
                     let uu____11757 =
                       let uu____11762 = init args  in
                       FStar_Syntax_Syntax.mk_Tm_app hd1 uu____11762  in
                     uu____11757 FStar_Pervasives_Native.None
                       t2.FStar_Syntax_Syntax.pos
                      in
                   (uu____11756, (a, q'))  in
                 FStar_Reflection_Data.Tv_App uu____11751  in
               FStar_All.pipe_left ret uu____11750)
      | FStar_Syntax_Syntax.Tm_abs ([],uu____11775,uu____11776) ->
          failwith "empty arguments on Tm_abs"
      | FStar_Syntax_Syntax.Tm_abs (bs,t3,k) ->
          let uu____11828 = FStar_Syntax_Subst.open_term bs t3  in
          (match uu____11828 with
           | (bs1,t4) ->
               (match bs1 with
                | [] -> failwith "impossible"
                | b::bs2 ->
                    let uu____11869 =
                      let uu____11870 =
                        let uu____11875 = FStar_Syntax_Util.abs bs2 t4 k  in
                        (b, uu____11875)  in
                      FStar_Reflection_Data.Tv_Abs uu____11870  in
                    FStar_All.pipe_left ret uu____11869))
      | FStar_Syntax_Syntax.Tm_type uu____11878 ->
          FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_Type ())
      | FStar_Syntax_Syntax.Tm_arrow ([],k) ->
          failwith "empty binders on arrow"
      | FStar_Syntax_Syntax.Tm_arrow uu____11902 ->
          let uu____11917 = FStar_Syntax_Util.arrow_one t2  in
          (match uu____11917 with
           | FStar_Pervasives_Native.Some (b,c) ->
               FStar_All.pipe_left ret
                 (FStar_Reflection_Data.Tv_Arrow (b, c))
           | FStar_Pervasives_Native.None  -> failwith "impossible")
      | FStar_Syntax_Syntax.Tm_refine (bv,t3) ->
          let b = FStar_Syntax_Syntax.mk_binder bv  in
          let uu____11947 = FStar_Syntax_Subst.open_term [b] t3  in
          (match uu____11947 with
           | (b',t4) ->
               let b1 =
                 match b' with
                 | b'1::[] -> b'1
                 | uu____12000 -> failwith "impossible"  in
               FStar_All.pipe_left ret
                 (FStar_Reflection_Data.Tv_Refine
                    ((FStar_Pervasives_Native.fst b1), t4)))
      | FStar_Syntax_Syntax.Tm_constant c ->
          let uu____12012 =
            let uu____12013 = FStar_Reflection_Basic.inspect_const c  in
            FStar_Reflection_Data.Tv_Const uu____12013  in
          FStar_All.pipe_left ret uu____12012
      | FStar_Syntax_Syntax.Tm_uvar (ctx_u,s) ->
          let uu____12034 =
            let uu____12035 =
              let uu____12040 =
                let uu____12041 =
                  FStar_Syntax_Unionfind.uvar_id
                    ctx_u.FStar_Syntax_Syntax.ctx_uvar_head
                   in
                FStar_BigInt.of_int_fs uu____12041  in
              (uu____12040, (ctx_u, s))  in
            FStar_Reflection_Data.Tv_Uvar uu____12035  in
          FStar_All.pipe_left ret uu____12034
      | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),t21) ->
          if lb.FStar_Syntax_Syntax.lbunivs <> []
          then FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown
          else
            (match lb.FStar_Syntax_Syntax.lbname with
             | FStar_Util.Inr uu____12075 ->
                 FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown
             | FStar_Util.Inl bv ->
                 let b = FStar_Syntax_Syntax.mk_binder bv  in
                 let uu____12080 = FStar_Syntax_Subst.open_term [b] t21  in
                 (match uu____12080 with
                  | (bs,t22) ->
                      let b1 =
                        match bs with
                        | b1::[] -> b1
                        | uu____12133 ->
                            failwith
                              "impossible: open_term returned different amount of binders"
                         in
                      FStar_All.pipe_left ret
                        (FStar_Reflection_Data.Tv_Let
                           (false, (FStar_Pervasives_Native.fst b1),
                             (lb.FStar_Syntax_Syntax.lbdef), t22))))
      | FStar_Syntax_Syntax.Tm_let ((true ,lb::[]),t21) ->
          if lb.FStar_Syntax_Syntax.lbunivs <> []
          then FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown
          else
            (match lb.FStar_Syntax_Syntax.lbname with
             | FStar_Util.Inr uu____12167 ->
                 FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown
             | FStar_Util.Inl bv ->
                 let uu____12171 = FStar_Syntax_Subst.open_let_rec [lb] t21
                    in
                 (match uu____12171 with
                  | (lbs,t22) ->
                      (match lbs with
                       | lb1::[] ->
                           (match lb1.FStar_Syntax_Syntax.lbname with
                            | FStar_Util.Inr uu____12191 ->
                                ret FStar_Reflection_Data.Tv_Unknown
                            | FStar_Util.Inl bv1 ->
                                FStar_All.pipe_left ret
                                  (FStar_Reflection_Data.Tv_Let
                                     (true, bv1,
                                       (lb1.FStar_Syntax_Syntax.lbdef), t22)))
                       | uu____12195 ->
                           failwith
                             "impossible: open_term returned different amount of binders")))
      | FStar_Syntax_Syntax.Tm_match (t3,brs) ->
          let rec inspect_pat p =
            match p.FStar_Syntax_Syntax.v with
            | FStar_Syntax_Syntax.Pat_constant c ->
                let uu____12249 = FStar_Reflection_Basic.inspect_const c  in
                FStar_Reflection_Data.Pat_Constant uu____12249
            | FStar_Syntax_Syntax.Pat_cons (fv,ps) ->
                let uu____12268 =
                  let uu____12275 =
                    FStar_List.map
                      (fun uu____12287  ->
                         match uu____12287 with
                         | (p1,uu____12295) -> inspect_pat p1) ps
                     in
                  (fv, uu____12275)  in
                FStar_Reflection_Data.Pat_Cons uu____12268
            | FStar_Syntax_Syntax.Pat_var bv ->
                FStar_Reflection_Data.Pat_Var bv
            | FStar_Syntax_Syntax.Pat_wild bv ->
                FStar_Reflection_Data.Pat_Wild bv
            | FStar_Syntax_Syntax.Pat_dot_term (bv,t4) ->
                FStar_Reflection_Data.Pat_Dot_Term (bv, t4)
             in
          let brs1 = FStar_List.map FStar_Syntax_Subst.open_branch brs  in
          let brs2 =
            FStar_List.map
              (fun uu___344_12389  ->
                 match uu___344_12389 with
                 | (pat,uu____12411,t4) ->
                     let uu____12429 = inspect_pat pat  in (uu____12429, t4))
              brs1
             in
          FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_Match (t3, brs2))
      | FStar_Syntax_Syntax.Tm_unknown  ->
          FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown
      | uu____12438 ->
          ((let uu____12440 =
              let uu____12445 =
                let uu____12446 = FStar_Syntax_Print.tag_of_term t2  in
                let uu____12447 = FStar_Syntax_Print.term_to_string t2  in
                FStar_Util.format2
                  "inspect: outside of expected syntax (%s, %s)\n"
                  uu____12446 uu____12447
                 in
              (FStar_Errors.Warning_CantInspect, uu____12445)  in
            FStar_Errors.log_issue t2.FStar_Syntax_Syntax.pos uu____12440);
           FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown)
       in
    wrap_err "inspect" uu____11647
  
let (pack : FStar_Reflection_Data.term_view -> FStar_Syntax_Syntax.term tac)
  =
  fun tv  ->
    match tv with
    | FStar_Reflection_Data.Tv_Var bv ->
        let uu____12460 = FStar_Syntax_Syntax.bv_to_name bv  in
        FStar_All.pipe_left ret uu____12460
    | FStar_Reflection_Data.Tv_BVar bv ->
        let uu____12464 = FStar_Syntax_Syntax.bv_to_tm bv  in
        FStar_All.pipe_left ret uu____12464
    | FStar_Reflection_Data.Tv_FVar fv ->
        let uu____12468 = FStar_Syntax_Syntax.fv_to_tm fv  in
        FStar_All.pipe_left ret uu____12468
    | FStar_Reflection_Data.Tv_App (l,(r,q)) ->
        let q' = FStar_Reflection_Basic.pack_aqual q  in
        let uu____12475 = FStar_Syntax_Util.mk_app l [(r, q')]  in
        FStar_All.pipe_left ret uu____12475
    | FStar_Reflection_Data.Tv_Abs (b,t) ->
        let uu____12500 =
          FStar_Syntax_Util.abs [b] t FStar_Pervasives_Native.None  in
        FStar_All.pipe_left ret uu____12500
    | FStar_Reflection_Data.Tv_Arrow (b,c) ->
        let uu____12517 = FStar_Syntax_Util.arrow [b] c  in
        FStar_All.pipe_left ret uu____12517
    | FStar_Reflection_Data.Tv_Type () ->
        FStar_All.pipe_left ret FStar_Syntax_Util.ktype
    | FStar_Reflection_Data.Tv_Refine (bv,t) ->
        let uu____12536 = FStar_Syntax_Util.refine bv t  in
        FStar_All.pipe_left ret uu____12536
    | FStar_Reflection_Data.Tv_Const c ->
        let uu____12540 =
          let uu____12541 =
            let uu____12548 =
              let uu____12549 = FStar_Reflection_Basic.pack_const c  in
              FStar_Syntax_Syntax.Tm_constant uu____12549  in
            FStar_Syntax_Syntax.mk uu____12548  in
          uu____12541 FStar_Pervasives_Native.None FStar_Range.dummyRange  in
        FStar_All.pipe_left ret uu____12540
    | FStar_Reflection_Data.Tv_Uvar (_u,ctx_u_s) ->
        let uu____12557 =
          FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_uvar ctx_u_s)
            FStar_Pervasives_Native.None FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____12557
    | FStar_Reflection_Data.Tv_Let (false ,bv,t1,t2) ->
        let lb =
          FStar_Syntax_Util.mk_letbinding (FStar_Util.Inl bv) []
            bv.FStar_Syntax_Syntax.sort FStar_Parser_Const.effect_Tot_lid t1
            [] FStar_Range.dummyRange
           in
        let uu____12566 =
          let uu____12567 =
            let uu____12574 =
              let uu____12575 =
                let uu____12588 =
                  let uu____12591 =
                    let uu____12592 = FStar_Syntax_Syntax.mk_binder bv  in
                    [uu____12592]  in
                  FStar_Syntax_Subst.close uu____12591 t2  in
                ((false, [lb]), uu____12588)  in
              FStar_Syntax_Syntax.Tm_let uu____12575  in
            FStar_Syntax_Syntax.mk uu____12574  in
          uu____12567 FStar_Pervasives_Native.None FStar_Range.dummyRange  in
        FStar_All.pipe_left ret uu____12566
    | FStar_Reflection_Data.Tv_Let (true ,bv,t1,t2) ->
        let lb =
          FStar_Syntax_Util.mk_letbinding (FStar_Util.Inl bv) []
            bv.FStar_Syntax_Syntax.sort FStar_Parser_Const.effect_Tot_lid t1
            [] FStar_Range.dummyRange
           in
        let uu____12632 = FStar_Syntax_Subst.close_let_rec [lb] t2  in
        (match uu____12632 with
         | (lbs,body) ->
             let uu____12647 =
               FStar_Syntax_Syntax.mk
                 (FStar_Syntax_Syntax.Tm_let ((true, lbs), body))
                 FStar_Pervasives_Native.None FStar_Range.dummyRange
                in
             FStar_All.pipe_left ret uu____12647)
    | FStar_Reflection_Data.Tv_Match (t,brs) ->
        let wrap v1 =
          {
            FStar_Syntax_Syntax.v = v1;
            FStar_Syntax_Syntax.p = FStar_Range.dummyRange
          }  in
        let rec pack_pat p =
          match p with
          | FStar_Reflection_Data.Pat_Constant c ->
              let uu____12681 =
                let uu____12682 = FStar_Reflection_Basic.pack_const c  in
                FStar_Syntax_Syntax.Pat_constant uu____12682  in
              FStar_All.pipe_left wrap uu____12681
          | FStar_Reflection_Data.Pat_Cons (fv,ps) ->
              let uu____12689 =
                let uu____12690 =
                  let uu____12703 =
                    FStar_List.map
                      (fun p1  ->
                         let uu____12719 = pack_pat p1  in
                         (uu____12719, false)) ps
                     in
                  (fv, uu____12703)  in
                FStar_Syntax_Syntax.Pat_cons uu____12690  in
              FStar_All.pipe_left wrap uu____12689
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
            (fun uu___345_12765  ->
               match uu___345_12765 with
               | (pat,t1) ->
                   let uu____12782 = pack_pat pat  in
                   (uu____12782, FStar_Pervasives_Native.None, t1)) brs
           in
        let brs2 = FStar_List.map FStar_Syntax_Subst.close_branch brs1  in
        let uu____12830 =
          FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_match (t, brs2))
            FStar_Pervasives_Native.None FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____12830
    | FStar_Reflection_Data.Tv_AscribedT (e,t,tacopt) ->
        let uu____12858 =
          FStar_Syntax_Syntax.mk
            (FStar_Syntax_Syntax.Tm_ascribed
               (e, ((FStar_Util.Inl t), tacopt),
                 FStar_Pervasives_Native.None)) FStar_Pervasives_Native.None
            FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____12858
    | FStar_Reflection_Data.Tv_AscribedC (e,c,tacopt) ->
        let uu____12904 =
          FStar_Syntax_Syntax.mk
            (FStar_Syntax_Syntax.Tm_ascribed
               (e, ((FStar_Util.Inr c), tacopt),
                 FStar_Pervasives_Native.None)) FStar_Pervasives_Native.None
            FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____12904
    | FStar_Reflection_Data.Tv_Unknown  ->
        let uu____12943 =
          FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown
            FStar_Pervasives_Native.None FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____12943
  
let (goal_of_goal_ty :
  env ->
    FStar_Reflection_Data.typ ->
      (FStar_Tactics_Types.goal,FStar_TypeChecker_Env.guard_t)
        FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun typ  ->
      let uu____12964 =
        FStar_TypeChecker_Util.new_implicit_var "proofstate_of_goal_ty"
          typ.FStar_Syntax_Syntax.pos env typ
         in
      match uu____12964 with
      | (u,ctx_uvars,g_u) ->
          let uu____12996 = FStar_List.hd ctx_uvars  in
          (match uu____12996 with
           | (ctx_uvar,uu____13010) ->
               let g =
                 let uu____13012 = FStar_Options.peek ()  in
                 FStar_Tactics_Types.mk_goal env ctx_uvar uu____13012 false
                  in
               (g, g_u))
  
let (proofstate_of_goal_ty :
  FStar_Range.range ->
    env ->
      FStar_Reflection_Data.typ ->
        (FStar_Tactics_Types.proofstate,FStar_Syntax_Syntax.term)
          FStar_Pervasives_Native.tuple2)
  =
  fun rng  ->
    fun env  ->
      fun typ  ->
        let uu____13032 = goal_of_goal_ty env typ  in
        match uu____13032 with
        | (g,g_u) ->
            let ps =
              let uu____13044 =
                FStar_TypeChecker_Env.debug env
                  (FStar_Options.Other "TacVerbose")
                 in
              {
                FStar_Tactics_Types.main_context = env;
                FStar_Tactics_Types.main_goal = g;
                FStar_Tactics_Types.all_implicits =
                  (g_u.FStar_TypeChecker_Env.implicits);
                FStar_Tactics_Types.goals = [g];
                FStar_Tactics_Types.smt_goals = [];
                FStar_Tactics_Types.depth = (Prims.parse_int "0");
                FStar_Tactics_Types.__dump =
                  (fun ps  -> fun msg  -> dump_proofstate ps msg);
                FStar_Tactics_Types.psc =
                  FStar_TypeChecker_Normalize.null_psc;
                FStar_Tactics_Types.entry_range = rng;
                FStar_Tactics_Types.guard_policy = FStar_Tactics_Types.SMT;
                FStar_Tactics_Types.freshness = (Prims.parse_int "0");
                FStar_Tactics_Types.tac_verb_dbg = uu____13044
              }  in
            let uu____13049 = FStar_Tactics_Types.goal_witness g  in
            (ps, uu____13049)
  