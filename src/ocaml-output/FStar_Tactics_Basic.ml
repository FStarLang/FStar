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
  
let (compress_implicits : unit tac) =
  bind get
    (fun ps  ->
       let imps = ps.FStar_Tactics_Types.all_implicits  in
       let g =
         let uu___353_1281 = FStar_TypeChecker_Env.trivial_guard  in
         {
           FStar_TypeChecker_Env.guard_f =
             (uu___353_1281.FStar_TypeChecker_Env.guard_f);
           FStar_TypeChecker_Env.deferred =
             (uu___353_1281.FStar_TypeChecker_Env.deferred);
           FStar_TypeChecker_Env.univ_ineqs =
             (uu___353_1281.FStar_TypeChecker_Env.univ_ineqs);
           FStar_TypeChecker_Env.implicits = imps
         }  in
       let g1 =
         FStar_TypeChecker_Rel.resolve_implicits_tac
           ps.FStar_Tactics_Types.main_context g
          in
       let ps' =
         let uu___354_1284 = ps  in
         {
           FStar_Tactics_Types.main_context =
             (uu___354_1284.FStar_Tactics_Types.main_context);
           FStar_Tactics_Types.main_goal =
             (uu___354_1284.FStar_Tactics_Types.main_goal);
           FStar_Tactics_Types.all_implicits =
             (g1.FStar_TypeChecker_Env.implicits);
           FStar_Tactics_Types.goals =
             (uu___354_1284.FStar_Tactics_Types.goals);
           FStar_Tactics_Types.smt_goals =
             (uu___354_1284.FStar_Tactics_Types.smt_goals);
           FStar_Tactics_Types.depth =
             (uu___354_1284.FStar_Tactics_Types.depth);
           FStar_Tactics_Types.__dump =
             (uu___354_1284.FStar_Tactics_Types.__dump);
           FStar_Tactics_Types.psc = (uu___354_1284.FStar_Tactics_Types.psc);
           FStar_Tactics_Types.entry_range =
             (uu___354_1284.FStar_Tactics_Types.entry_range);
           FStar_Tactics_Types.guard_policy =
             (uu___354_1284.FStar_Tactics_Types.guard_policy);
           FStar_Tactics_Types.freshness =
             (uu___354_1284.FStar_Tactics_Types.freshness);
           FStar_Tactics_Types.tac_verb_dbg =
             (uu___354_1284.FStar_Tactics_Types.tac_verb_dbg)
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
          (fun uu____1307  ->
             (let uu____1309 =
                FStar_TypeChecker_Env.debug env (FStar_Options.Other "1346")
                 in
              if uu____1309
              then
                (FStar_Options.push ();
                 (let uu____1311 =
                    FStar_Options.set_options FStar_Options.Set
                      "--debug_level Rel --debug_level RelCheck"
                     in
                  ()))
              else ());
             (let uu____1313 = __do_unify env t1 t2  in
              bind uu____1313
                (fun r  ->
                   (let uu____1320 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "1346")
                       in
                    if uu____1320 then FStar_Options.pop () else ());
                   bind compress_implicits (fun uu____1323  -> ret r))))
  
let (remove_solved_goals : unit tac) =
  bind get
    (fun ps  ->
       let ps' =
         let uu___355_1330 = ps  in
         let uu____1331 =
           FStar_List.filter
             (fun g  ->
                let uu____1337 = check_goal_solved g  in
                FStar_Option.isNone uu____1337) ps.FStar_Tactics_Types.goals
            in
         {
           FStar_Tactics_Types.main_context =
             (uu___355_1330.FStar_Tactics_Types.main_context);
           FStar_Tactics_Types.main_goal =
             (uu___355_1330.FStar_Tactics_Types.main_goal);
           FStar_Tactics_Types.all_implicits =
             (uu___355_1330.FStar_Tactics_Types.all_implicits);
           FStar_Tactics_Types.goals = uu____1331;
           FStar_Tactics_Types.smt_goals =
             (uu___355_1330.FStar_Tactics_Types.smt_goals);
           FStar_Tactics_Types.depth =
             (uu___355_1330.FStar_Tactics_Types.depth);
           FStar_Tactics_Types.__dump =
             (uu___355_1330.FStar_Tactics_Types.__dump);
           FStar_Tactics_Types.psc = (uu___355_1330.FStar_Tactics_Types.psc);
           FStar_Tactics_Types.entry_range =
             (uu___355_1330.FStar_Tactics_Types.entry_range);
           FStar_Tactics_Types.guard_policy =
             (uu___355_1330.FStar_Tactics_Types.guard_policy);
           FStar_Tactics_Types.freshness =
             (uu___355_1330.FStar_Tactics_Types.freshness);
           FStar_Tactics_Types.tac_verb_dbg =
             (uu___355_1330.FStar_Tactics_Types.tac_verb_dbg)
         }  in
       set ps')
  
let (set_solution :
  FStar_Tactics_Types.goal -> FStar_Syntax_Syntax.term -> unit tac) =
  fun goal  ->
    fun solution  ->
      let uu____1354 =
        FStar_Syntax_Unionfind.find
          (goal.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_head
         in
      match uu____1354 with
      | FStar_Pervasives_Native.Some uu____1359 ->
          let uu____1360 =
            let uu____1361 = goal_to_string_verbose goal  in
            FStar_Util.format1 "Goal %s is already solved" uu____1361  in
          fail uu____1360
      | FStar_Pervasives_Native.None  ->
          (FStar_Syntax_Unionfind.change
             (goal.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_head
             solution;
           ret ())
  
let (trysolve :
  FStar_Tactics_Types.goal -> FStar_Syntax_Syntax.term -> Prims.bool tac) =
  fun goal  ->
    fun solution  ->
      let uu____1377 = FStar_Tactics_Types.goal_env goal  in
      let uu____1378 = FStar_Tactics_Types.goal_witness goal  in
      do_unify uu____1377 solution uu____1378
  
let (__dismiss : unit tac) =
  bind get
    (fun p  ->
       let uu____1384 =
         let uu___356_1385 = p  in
         let uu____1386 = FStar_List.tl p.FStar_Tactics_Types.goals  in
         {
           FStar_Tactics_Types.main_context =
             (uu___356_1385.FStar_Tactics_Types.main_context);
           FStar_Tactics_Types.main_goal =
             (uu___356_1385.FStar_Tactics_Types.main_goal);
           FStar_Tactics_Types.all_implicits =
             (uu___356_1385.FStar_Tactics_Types.all_implicits);
           FStar_Tactics_Types.goals = uu____1386;
           FStar_Tactics_Types.smt_goals =
             (uu___356_1385.FStar_Tactics_Types.smt_goals);
           FStar_Tactics_Types.depth =
             (uu___356_1385.FStar_Tactics_Types.depth);
           FStar_Tactics_Types.__dump =
             (uu___356_1385.FStar_Tactics_Types.__dump);
           FStar_Tactics_Types.psc = (uu___356_1385.FStar_Tactics_Types.psc);
           FStar_Tactics_Types.entry_range =
             (uu___356_1385.FStar_Tactics_Types.entry_range);
           FStar_Tactics_Types.guard_policy =
             (uu___356_1385.FStar_Tactics_Types.guard_policy);
           FStar_Tactics_Types.freshness =
             (uu___356_1385.FStar_Tactics_Types.freshness);
           FStar_Tactics_Types.tac_verb_dbg =
             (uu___356_1385.FStar_Tactics_Types.tac_verb_dbg)
         }  in
       set uu____1384)
  
let (dismiss : unit -> unit tac) =
  fun uu____1395  ->
    bind get
      (fun p  ->
         match p.FStar_Tactics_Types.goals with
         | [] -> fail "dismiss: no more goals"
         | uu____1402 -> __dismiss)
  
let (solve :
  FStar_Tactics_Types.goal -> FStar_Syntax_Syntax.term -> unit tac) =
  fun goal  ->
    fun solution  ->
      let e = FStar_Tactics_Types.goal_env goal  in
      mlog
        (fun uu____1423  ->
           let uu____1424 =
             let uu____1425 = FStar_Tactics_Types.goal_witness goal  in
             FStar_Syntax_Print.term_to_string uu____1425  in
           let uu____1426 = FStar_Syntax_Print.term_to_string solution  in
           FStar_Util.print2 "solve %s := %s\n" uu____1424 uu____1426)
        (fun uu____1429  ->
           let uu____1430 = trysolve goal solution  in
           bind uu____1430
             (fun b  ->
                if b
                then bind __dismiss (fun uu____1438  -> remove_solved_goals)
                else
                  (let uu____1440 =
                     let uu____1441 =
                       let uu____1442 = FStar_Tactics_Types.goal_env goal  in
                       tts uu____1442 solution  in
                     let uu____1443 =
                       let uu____1444 = FStar_Tactics_Types.goal_env goal  in
                       let uu____1445 = FStar_Tactics_Types.goal_witness goal
                          in
                       tts uu____1444 uu____1445  in
                     let uu____1446 =
                       let uu____1447 = FStar_Tactics_Types.goal_env goal  in
                       let uu____1448 = FStar_Tactics_Types.goal_type goal
                          in
                       tts uu____1447 uu____1448  in
                     FStar_Util.format3 "%s does not solve %s : %s"
                       uu____1441 uu____1443 uu____1446
                      in
                   fail uu____1440)))
  
let (solve' :
  FStar_Tactics_Types.goal -> FStar_Syntax_Syntax.term -> unit tac) =
  fun goal  ->
    fun solution  ->
      let uu____1463 = set_solution goal solution  in
      bind uu____1463
        (fun uu____1467  ->
           bind __dismiss (fun uu____1469  -> remove_solved_goals))
  
let (dismiss_all : unit tac) =
  bind get
    (fun p  ->
       set
         (let uu___357_1476 = p  in
          {
            FStar_Tactics_Types.main_context =
              (uu___357_1476.FStar_Tactics_Types.main_context);
            FStar_Tactics_Types.main_goal =
              (uu___357_1476.FStar_Tactics_Types.main_goal);
            FStar_Tactics_Types.all_implicits =
              (uu___357_1476.FStar_Tactics_Types.all_implicits);
            FStar_Tactics_Types.goals = [];
            FStar_Tactics_Types.smt_goals =
              (uu___357_1476.FStar_Tactics_Types.smt_goals);
            FStar_Tactics_Types.depth =
              (uu___357_1476.FStar_Tactics_Types.depth);
            FStar_Tactics_Types.__dump =
              (uu___357_1476.FStar_Tactics_Types.__dump);
            FStar_Tactics_Types.psc = (uu___357_1476.FStar_Tactics_Types.psc);
            FStar_Tactics_Types.entry_range =
              (uu___357_1476.FStar_Tactics_Types.entry_range);
            FStar_Tactics_Types.guard_policy =
              (uu___357_1476.FStar_Tactics_Types.guard_policy);
            FStar_Tactics_Types.freshness =
              (uu___357_1476.FStar_Tactics_Types.freshness);
            FStar_Tactics_Types.tac_verb_dbg =
              (uu___357_1476.FStar_Tactics_Types.tac_verb_dbg)
          }))
  
let (nwarn : Prims.int FStar_ST.ref) =
  FStar_Util.mk_ref (Prims.parse_int "0") 
let (check_valid_goal : FStar_Tactics_Types.goal -> unit) =
  fun g  ->
    let uu____1495 = FStar_Options.defensive ()  in
    if uu____1495
    then
      let b = true  in
      let env = FStar_Tactics_Types.goal_env g  in
      let b1 =
        b &&
          (let uu____1500 = FStar_Tactics_Types.goal_witness g  in
           FStar_TypeChecker_Env.closed env uu____1500)
         in
      let b2 =
        b1 &&
          (let uu____1503 = FStar_Tactics_Types.goal_type g  in
           FStar_TypeChecker_Env.closed env uu____1503)
         in
      let rec aux b3 e =
        let uu____1515 = FStar_TypeChecker_Env.pop_bv e  in
        match uu____1515 with
        | FStar_Pervasives_Native.None  -> b3
        | FStar_Pervasives_Native.Some (bv,e1) ->
            let b4 =
              b3 &&
                (FStar_TypeChecker_Env.closed e1 bv.FStar_Syntax_Syntax.sort)
               in
            aux b4 e1
         in
      let uu____1533 =
        (let uu____1536 = aux b2 env  in Prims.op_Negation uu____1536) &&
          (let uu____1538 = FStar_ST.op_Bang nwarn  in
           uu____1538 < (Prims.parse_int "5"))
         in
      (if uu____1533
       then
         ((let uu____1559 =
             let uu____1560 = FStar_Tactics_Types.goal_type g  in
             uu____1560.FStar_Syntax_Syntax.pos  in
           let uu____1563 =
             let uu____1568 =
               let uu____1569 = goal_to_string_verbose g  in
               FStar_Util.format1
                 "The following goal is ill-formed. Keeping calm and carrying on...\n<%s>\n\n"
                 uu____1569
                in
             (FStar_Errors.Warning_IllFormedGoal, uu____1568)  in
           FStar_Errors.log_issue uu____1559 uu____1563);
          (let uu____1570 =
             let uu____1571 = FStar_ST.op_Bang nwarn  in
             uu____1571 + (Prims.parse_int "1")  in
           FStar_ST.op_Colon_Equals nwarn uu____1570))
       else ())
    else ()
  
let (add_goals : FStar_Tactics_Types.goal Prims.list -> unit tac) =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___358_1631 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___358_1631.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___358_1631.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___358_1631.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (FStar_List.append gs p.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (uu___358_1631.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___358_1631.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___358_1631.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___358_1631.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___358_1631.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___358_1631.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___358_1631.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___358_1631.FStar_Tactics_Types.tac_verb_dbg)
            }))
  
let (add_smt_goals : FStar_Tactics_Types.goal Prims.list -> unit tac) =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___359_1651 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___359_1651.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___359_1651.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___359_1651.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___359_1651.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (FStar_List.append gs p.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___359_1651.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___359_1651.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___359_1651.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___359_1651.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___359_1651.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___359_1651.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___359_1651.FStar_Tactics_Types.tac_verb_dbg)
            }))
  
let (push_goals : FStar_Tactics_Types.goal Prims.list -> unit tac) =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___360_1671 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___360_1671.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___360_1671.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___360_1671.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (FStar_List.append p.FStar_Tactics_Types.goals gs);
              FStar_Tactics_Types.smt_goals =
                (uu___360_1671.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___360_1671.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___360_1671.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___360_1671.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___360_1671.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___360_1671.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___360_1671.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___360_1671.FStar_Tactics_Types.tac_verb_dbg)
            }))
  
let (push_smt_goals : FStar_Tactics_Types.goal Prims.list -> unit tac) =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___361_1691 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___361_1691.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___361_1691.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___361_1691.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___361_1691.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (FStar_List.append p.FStar_Tactics_Types.smt_goals gs);
              FStar_Tactics_Types.depth =
                (uu___361_1691.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___361_1691.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___361_1691.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___361_1691.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___361_1691.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___361_1691.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___361_1691.FStar_Tactics_Types.tac_verb_dbg)
            }))
  
let (replace_cur : FStar_Tactics_Types.goal -> unit tac) =
  fun g  -> bind __dismiss (fun uu____1702  -> add_goals [g]) 
let (add_implicits : implicits -> unit tac) =
  fun i  ->
    bind get
      (fun p  ->
         set
           (let uu___362_1716 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___362_1716.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___362_1716.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (FStar_List.append i p.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___362_1716.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (uu___362_1716.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___362_1716.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___362_1716.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___362_1716.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___362_1716.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___362_1716.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___362_1716.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___362_1716.FStar_Tactics_Types.tac_verb_dbg)
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
        let uu____1744 =
          FStar_TypeChecker_Env.new_implicit_var_aux reason
            typ.FStar_Syntax_Syntax.pos env typ
            FStar_Syntax_Syntax.Allow_untyped
           in
        match uu____1744 with
        | (u,ctx_uvar,g_u) ->
            let uu____1778 =
              add_implicits g_u.FStar_TypeChecker_Env.implicits  in
            bind uu____1778
              (fun uu____1787  ->
                 let uu____1788 =
                   let uu____1793 =
                     let uu____1794 = FStar_List.hd ctx_uvar  in
                     FStar_Pervasives_Native.fst uu____1794  in
                   (u, uu____1793)  in
                 ret uu____1788)
  
let (is_true : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____1812 = FStar_Syntax_Util.un_squash t  in
    match uu____1812 with
    | FStar_Pervasives_Native.Some t' ->
        let uu____1822 =
          let uu____1823 = FStar_Syntax_Subst.compress t'  in
          uu____1823.FStar_Syntax_Syntax.n  in
        (match uu____1822 with
         | FStar_Syntax_Syntax.Tm_fvar fv ->
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.true_lid
         | uu____1827 -> false)
    | uu____1828 -> false
  
let (is_false : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____1838 = FStar_Syntax_Util.un_squash t  in
    match uu____1838 with
    | FStar_Pervasives_Native.Some t' ->
        let uu____1848 =
          let uu____1849 = FStar_Syntax_Subst.compress t'  in
          uu____1849.FStar_Syntax_Syntax.n  in
        (match uu____1848 with
         | FStar_Syntax_Syntax.Tm_fvar fv ->
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.false_lid
         | uu____1853 -> false)
    | uu____1854 -> false
  
let (cur_goal : unit -> FStar_Tactics_Types.goal tac) =
  fun uu____1865  ->
    bind get
      (fun p  ->
         match p.FStar_Tactics_Types.goals with
         | [] -> fail "No more goals (1)"
         | hd1::tl1 ->
             let uu____1876 =
               FStar_Syntax_Unionfind.find
                 (hd1.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_head
                in
             (match uu____1876 with
              | FStar_Pervasives_Native.None  -> ret hd1
              | FStar_Pervasives_Native.Some t ->
                  ((let uu____1883 = goal_to_string_verbose hd1  in
                    let uu____1884 = FStar_Syntax_Print.term_to_string t  in
                    FStar_Util.print2
                      "!!!!!!!!!!!! GOAL IS ALREADY SOLVED! %s\nsol is %s\n"
                      uu____1883 uu____1884);
                   ret hd1)))
  
let (tadmit : unit -> unit tac) =
  fun uu____1891  ->
    let uu____1894 =
      bind get
        (fun ps  ->
           let uu____1900 = cur_goal ()  in
           bind uu____1900
             (fun g  ->
                (let uu____1907 =
                   let uu____1908 = FStar_Tactics_Types.goal_type g  in
                   uu____1908.FStar_Syntax_Syntax.pos  in
                 let uu____1911 =
                   let uu____1916 =
                     let uu____1917 = goal_to_string ps g  in
                     FStar_Util.format1 "Tactics admitted goal <%s>\n\n"
                       uu____1917
                      in
                   (FStar_Errors.Warning_TacAdmit, uu____1916)  in
                 FStar_Errors.log_issue uu____1907 uu____1911);
                solve' g FStar_Syntax_Util.exp_unit))
       in
    FStar_All.pipe_left (wrap_err "tadmit") uu____1894
  
let (fresh : unit -> FStar_BigInt.t tac) =
  fun uu____1928  ->
    bind get
      (fun ps  ->
         let n1 = ps.FStar_Tactics_Types.freshness  in
         let ps1 =
           let uu___363_1938 = ps  in
           {
             FStar_Tactics_Types.main_context =
               (uu___363_1938.FStar_Tactics_Types.main_context);
             FStar_Tactics_Types.main_goal =
               (uu___363_1938.FStar_Tactics_Types.main_goal);
             FStar_Tactics_Types.all_implicits =
               (uu___363_1938.FStar_Tactics_Types.all_implicits);
             FStar_Tactics_Types.goals =
               (uu___363_1938.FStar_Tactics_Types.goals);
             FStar_Tactics_Types.smt_goals =
               (uu___363_1938.FStar_Tactics_Types.smt_goals);
             FStar_Tactics_Types.depth =
               (uu___363_1938.FStar_Tactics_Types.depth);
             FStar_Tactics_Types.__dump =
               (uu___363_1938.FStar_Tactics_Types.__dump);
             FStar_Tactics_Types.psc =
               (uu___363_1938.FStar_Tactics_Types.psc);
             FStar_Tactics_Types.entry_range =
               (uu___363_1938.FStar_Tactics_Types.entry_range);
             FStar_Tactics_Types.guard_policy =
               (uu___363_1938.FStar_Tactics_Types.guard_policy);
             FStar_Tactics_Types.freshness = (n1 + (Prims.parse_int "1"));
             FStar_Tactics_Types.tac_verb_dbg =
               (uu___363_1938.FStar_Tactics_Types.tac_verb_dbg)
           }  in
         let uu____1939 = set ps1  in
         bind uu____1939
           (fun uu____1944  ->
              let uu____1945 = FStar_BigInt.of_int_fs n1  in ret uu____1945))
  
let (ngoals : unit -> FStar_BigInt.t tac) =
  fun uu____1952  ->
    bind get
      (fun ps  ->
         let n1 = FStar_List.length ps.FStar_Tactics_Types.goals  in
         let uu____1960 = FStar_BigInt.of_int_fs n1  in ret uu____1960)
  
let (ngoals_smt : unit -> FStar_BigInt.t tac) =
  fun uu____1973  ->
    bind get
      (fun ps  ->
         let n1 = FStar_List.length ps.FStar_Tactics_Types.smt_goals  in
         let uu____1981 = FStar_BigInt.of_int_fs n1  in ret uu____1981)
  
let (is_guard : unit -> Prims.bool tac) =
  fun uu____1994  ->
    let uu____1997 = cur_goal ()  in
    bind uu____1997 (fun g  -> ret g.FStar_Tactics_Types.is_guard)
  
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
            let uu____2029 = env.FStar_TypeChecker_Env.universe_of env phi
               in
            FStar_Syntax_Util.mk_squash uu____2029 phi  in
          let uu____2030 = new_uvar reason env typ  in
          bind uu____2030
            (fun uu____2045  ->
               match uu____2045 with
               | (uu____2052,ctx_uvar) ->
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
             (fun uu____2097  ->
                let uu____2098 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.print1 "Tac> __tc(%s)\n" uu____2098)
             (fun uu____2101  ->
                let e1 =
                  let uu___364_2103 = e  in
                  {
                    FStar_TypeChecker_Env.solver =
                      (uu___364_2103.FStar_TypeChecker_Env.solver);
                    FStar_TypeChecker_Env.range =
                      (uu___364_2103.FStar_TypeChecker_Env.range);
                    FStar_TypeChecker_Env.curmodule =
                      (uu___364_2103.FStar_TypeChecker_Env.curmodule);
                    FStar_TypeChecker_Env.gamma =
                      (uu___364_2103.FStar_TypeChecker_Env.gamma);
                    FStar_TypeChecker_Env.gamma_sig =
                      (uu___364_2103.FStar_TypeChecker_Env.gamma_sig);
                    FStar_TypeChecker_Env.gamma_cache =
                      (uu___364_2103.FStar_TypeChecker_Env.gamma_cache);
                    FStar_TypeChecker_Env.modules =
                      (uu___364_2103.FStar_TypeChecker_Env.modules);
                    FStar_TypeChecker_Env.expected_typ =
                      (uu___364_2103.FStar_TypeChecker_Env.expected_typ);
                    FStar_TypeChecker_Env.sigtab =
                      (uu___364_2103.FStar_TypeChecker_Env.sigtab);
                    FStar_TypeChecker_Env.attrtab =
                      (uu___364_2103.FStar_TypeChecker_Env.attrtab);
                    FStar_TypeChecker_Env.is_pattern =
                      (uu___364_2103.FStar_TypeChecker_Env.is_pattern);
                    FStar_TypeChecker_Env.instantiate_imp =
                      (uu___364_2103.FStar_TypeChecker_Env.instantiate_imp);
                    FStar_TypeChecker_Env.effects =
                      (uu___364_2103.FStar_TypeChecker_Env.effects);
                    FStar_TypeChecker_Env.generalize =
                      (uu___364_2103.FStar_TypeChecker_Env.generalize);
                    FStar_TypeChecker_Env.letrecs =
                      (uu___364_2103.FStar_TypeChecker_Env.letrecs);
                    FStar_TypeChecker_Env.top_level =
                      (uu___364_2103.FStar_TypeChecker_Env.top_level);
                    FStar_TypeChecker_Env.check_uvars =
                      (uu___364_2103.FStar_TypeChecker_Env.check_uvars);
                    FStar_TypeChecker_Env.use_eq =
                      (uu___364_2103.FStar_TypeChecker_Env.use_eq);
                    FStar_TypeChecker_Env.is_iface =
                      (uu___364_2103.FStar_TypeChecker_Env.is_iface);
                    FStar_TypeChecker_Env.admit =
                      (uu___364_2103.FStar_TypeChecker_Env.admit);
                    FStar_TypeChecker_Env.lax =
                      (uu___364_2103.FStar_TypeChecker_Env.lax);
                    FStar_TypeChecker_Env.lax_universes =
                      (uu___364_2103.FStar_TypeChecker_Env.lax_universes);
                    FStar_TypeChecker_Env.phase1 =
                      (uu___364_2103.FStar_TypeChecker_Env.phase1);
                    FStar_TypeChecker_Env.failhard =
                      (uu___364_2103.FStar_TypeChecker_Env.failhard);
                    FStar_TypeChecker_Env.nosynth =
                      (uu___364_2103.FStar_TypeChecker_Env.nosynth);
                    FStar_TypeChecker_Env.uvar_subtyping = false;
                    FStar_TypeChecker_Env.tc_term =
                      (uu___364_2103.FStar_TypeChecker_Env.tc_term);
                    FStar_TypeChecker_Env.type_of =
                      (uu___364_2103.FStar_TypeChecker_Env.type_of);
                    FStar_TypeChecker_Env.universe_of =
                      (uu___364_2103.FStar_TypeChecker_Env.universe_of);
                    FStar_TypeChecker_Env.check_type_of =
                      (uu___364_2103.FStar_TypeChecker_Env.check_type_of);
                    FStar_TypeChecker_Env.use_bv_sorts =
                      (uu___364_2103.FStar_TypeChecker_Env.use_bv_sorts);
                    FStar_TypeChecker_Env.qtbl_name_and_index =
                      (uu___364_2103.FStar_TypeChecker_Env.qtbl_name_and_index);
                    FStar_TypeChecker_Env.normalized_eff_names =
                      (uu___364_2103.FStar_TypeChecker_Env.normalized_eff_names);
                    FStar_TypeChecker_Env.proof_ns =
                      (uu___364_2103.FStar_TypeChecker_Env.proof_ns);
                    FStar_TypeChecker_Env.synth_hook =
                      (uu___364_2103.FStar_TypeChecker_Env.synth_hook);
                    FStar_TypeChecker_Env.splice =
                      (uu___364_2103.FStar_TypeChecker_Env.splice);
                    FStar_TypeChecker_Env.is_native_tactic =
                      (uu___364_2103.FStar_TypeChecker_Env.is_native_tactic);
                    FStar_TypeChecker_Env.identifier_info =
                      (uu___364_2103.FStar_TypeChecker_Env.identifier_info);
                    FStar_TypeChecker_Env.tc_hooks =
                      (uu___364_2103.FStar_TypeChecker_Env.tc_hooks);
                    FStar_TypeChecker_Env.dsenv =
                      (uu___364_2103.FStar_TypeChecker_Env.dsenv);
                    FStar_TypeChecker_Env.dep_graph =
                      (uu___364_2103.FStar_TypeChecker_Env.dep_graph)
                  }  in
                try
                  let uu____2123 =
                    (ps.FStar_Tactics_Types.main_context).FStar_TypeChecker_Env.type_of
                      e1 t
                     in
                  ret uu____2123
                with
                | FStar_Errors.Err (uu____2150,msg) ->
                    let uu____2152 = tts e1 t  in
                    let uu____2153 =
                      let uu____2154 = FStar_TypeChecker_Env.all_binders e1
                         in
                      FStar_All.pipe_right uu____2154
                        (FStar_Syntax_Print.binders_to_string ", ")
                       in
                    fail3 "Cannot type %s in context (%s). Error = (%s)"
                      uu____2152 uu____2153 msg
                | FStar_Errors.Error (uu____2161,msg,uu____2163) ->
                    let uu____2164 = tts e1 t  in
                    let uu____2165 =
                      let uu____2166 = FStar_TypeChecker_Env.all_binders e1
                         in
                      FStar_All.pipe_right uu____2166
                        (FStar_Syntax_Print.binders_to_string ", ")
                       in
                    fail3 "Cannot type %s in context (%s). Error = (%s)"
                      uu____2164 uu____2165 msg))
  
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
  fun uu____2193  ->
    bind get (fun ps  -> ret ps.FStar_Tactics_Types.guard_policy)
  
let (set_guard_policy : FStar_Tactics_Types.guard_policy -> unit tac) =
  fun pol  ->
    bind get
      (fun ps  ->
         set
           (let uu___367_2211 = ps  in
            {
              FStar_Tactics_Types.main_context =
                (uu___367_2211.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___367_2211.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___367_2211.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___367_2211.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (uu___367_2211.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___367_2211.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___367_2211.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___367_2211.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___367_2211.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy = pol;
              FStar_Tactics_Types.freshness =
                (uu___367_2211.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___367_2211.FStar_Tactics_Types.tac_verb_dbg)
            }))
  
let with_policy : 'a . FStar_Tactics_Types.guard_policy -> 'a tac -> 'a tac =
  fun pol  ->
    fun t  ->
      let uu____2235 = get_guard_policy ()  in
      bind uu____2235
        (fun old_pol  ->
           let uu____2241 = set_guard_policy pol  in
           bind uu____2241
             (fun uu____2245  ->
                bind t
                  (fun r  ->
                     let uu____2249 = set_guard_policy old_pol  in
                     bind uu____2249 (fun uu____2253  -> ret r))))
  
let (getopts : FStar_Options.optionstate tac) =
  let uu____2256 = let uu____2261 = cur_goal ()  in trytac uu____2261  in
  bind uu____2256
    (fun uu___338_2268  ->
       match uu___338_2268 with
       | FStar_Pervasives_Native.Some g -> ret g.FStar_Tactics_Types.opts
       | FStar_Pervasives_Native.None  ->
           let uu____2274 = FStar_Options.peek ()  in ret uu____2274)
  
let (proc_guard :
  Prims.string -> env -> FStar_TypeChecker_Env.guard_t -> unit tac) =
  fun reason  ->
    fun e  ->
      fun g  ->
        bind getopts
          (fun opts  ->
             let uu____2297 =
               let uu____2298 = FStar_TypeChecker_Rel.simplify_guard e g  in
               uu____2298.FStar_TypeChecker_Env.guard_f  in
             match uu____2297 with
             | FStar_TypeChecker_Common.Trivial  -> ret ()
             | FStar_TypeChecker_Common.NonTrivial f ->
                 let uu____2302 = istrivial e f  in
                 if uu____2302
                 then ret ()
                 else
                   bind get
                     (fun ps  ->
                        match ps.FStar_Tactics_Types.guard_policy with
                        | FStar_Tactics_Types.Drop  -> ret ()
                        | FStar_Tactics_Types.Goal  ->
                            let uu____2310 =
                              mk_irrelevant_goal reason e f opts  in
                            bind uu____2310
                              (fun goal  ->
                                 let goal1 =
                                   let uu___368_2317 = goal  in
                                   {
                                     FStar_Tactics_Types.goal_main_env =
                                       (uu___368_2317.FStar_Tactics_Types.goal_main_env);
                                     FStar_Tactics_Types.goal_ctx_uvar =
                                       (uu___368_2317.FStar_Tactics_Types.goal_ctx_uvar);
                                     FStar_Tactics_Types.opts =
                                       (uu___368_2317.FStar_Tactics_Types.opts);
                                     FStar_Tactics_Types.is_guard = true
                                   }  in
                                 push_goals [goal1])
                        | FStar_Tactics_Types.SMT  ->
                            let uu____2318 =
                              mk_irrelevant_goal reason e f opts  in
                            bind uu____2318
                              (fun goal  ->
                                 let goal1 =
                                   let uu___369_2325 = goal  in
                                   {
                                     FStar_Tactics_Types.goal_main_env =
                                       (uu___369_2325.FStar_Tactics_Types.goal_main_env);
                                     FStar_Tactics_Types.goal_ctx_uvar =
                                       (uu___369_2325.FStar_Tactics_Types.goal_ctx_uvar);
                                     FStar_Tactics_Types.opts =
                                       (uu___369_2325.FStar_Tactics_Types.opts);
                                     FStar_Tactics_Types.is_guard = true
                                   }  in
                                 push_smt_goals [goal1])
                        | FStar_Tactics_Types.Force  ->
                            (try
                               let uu____2333 =
                                 let uu____2334 =
                                   let uu____2335 =
                                     FStar_TypeChecker_Rel.discharge_guard_no_smt
                                       e g
                                      in
                                   FStar_All.pipe_left
                                     FStar_TypeChecker_Env.is_trivial
                                     uu____2335
                                    in
                                 Prims.op_Negation uu____2334  in
                               if uu____2333
                               then
                                 mlog
                                   (fun uu____2340  ->
                                      let uu____2341 =
                                        FStar_TypeChecker_Rel.guard_to_string
                                          e g
                                         in
                                      FStar_Util.print1 "guard = %s\n"
                                        uu____2341)
                                   (fun uu____2343  ->
                                      fail1 "Forcing the guard failed %s)"
                                        reason)
                               else ret ()
                             with
                             | uu____2350 ->
                                 mlog
                                   (fun uu____2353  ->
                                      let uu____2354 =
                                        FStar_TypeChecker_Rel.guard_to_string
                                          e g
                                         in
                                      FStar_Util.print1 "guard = %s\n"
                                        uu____2354)
                                   (fun uu____2356  ->
                                      fail1 "Forcing the guard failed (%s)"
                                        reason))))
  
let (tc : FStar_Syntax_Syntax.term -> FStar_Reflection_Data.typ tac) =
  fun t  ->
    let uu____2366 =
      let uu____2369 = cur_goal ()  in
      bind uu____2369
        (fun goal  ->
           let uu____2375 =
             let uu____2384 = FStar_Tactics_Types.goal_env goal  in
             __tc uu____2384 t  in
           bind uu____2375
             (fun uu____2396  ->
                match uu____2396 with
                | (t1,typ,guard) ->
                    let uu____2408 =
                      let uu____2411 = FStar_Tactics_Types.goal_env goal  in
                      proc_guard "tc" uu____2411 guard  in
                    bind uu____2408 (fun uu____2413  -> ret typ)))
       in
    FStar_All.pipe_left (wrap_err "tc") uu____2366
  
let (add_irrelevant_goal :
  Prims.string ->
    env -> FStar_Reflection_Data.typ -> FStar_Options.optionstate -> unit tac)
  =
  fun reason  ->
    fun env  ->
      fun phi  ->
        fun opts  ->
          let uu____2442 = mk_irrelevant_goal reason env phi opts  in
          bind uu____2442 (fun goal  -> add_goals [goal])
  
let (trivial : unit -> unit tac) =
  fun uu____2453  ->
    let uu____2456 = cur_goal ()  in
    bind uu____2456
      (fun goal  ->
         let uu____2462 =
           let uu____2463 = FStar_Tactics_Types.goal_env goal  in
           let uu____2464 = FStar_Tactics_Types.goal_type goal  in
           istrivial uu____2463 uu____2464  in
         if uu____2462
         then solve' goal FStar_Syntax_Util.exp_unit
         else
           (let uu____2468 =
              let uu____2469 = FStar_Tactics_Types.goal_env goal  in
              let uu____2470 = FStar_Tactics_Types.goal_type goal  in
              tts uu____2469 uu____2470  in
            fail1 "Not a trivial goal: %s" uu____2468))
  
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
          let uu____2499 =
            let uu____2500 = FStar_TypeChecker_Rel.simplify_guard e g  in
            uu____2500.FStar_TypeChecker_Env.guard_f  in
          match uu____2499 with
          | FStar_TypeChecker_Common.Trivial  ->
              ret FStar_Pervasives_Native.None
          | FStar_TypeChecker_Common.NonTrivial f ->
              let uu____2508 = istrivial e f  in
              if uu____2508
              then ret FStar_Pervasives_Native.None
              else
                (let uu____2516 = mk_irrelevant_goal reason e f opts  in
                 bind uu____2516
                   (fun goal  ->
                      ret
                        (FStar_Pervasives_Native.Some
                           (let uu___372_2526 = goal  in
                            {
                              FStar_Tactics_Types.goal_main_env =
                                (uu___372_2526.FStar_Tactics_Types.goal_main_env);
                              FStar_Tactics_Types.goal_ctx_uvar =
                                (uu___372_2526.FStar_Tactics_Types.goal_ctx_uvar);
                              FStar_Tactics_Types.opts =
                                (uu___372_2526.FStar_Tactics_Types.opts);
                              FStar_Tactics_Types.is_guard = true
                            }))))
  
let (smt : unit -> unit tac) =
  fun uu____2533  ->
    let uu____2536 = cur_goal ()  in
    bind uu____2536
      (fun g  ->
         let uu____2542 = is_irrelevant g  in
         if uu____2542
         then bind __dismiss (fun uu____2546  -> add_smt_goals [g])
         else
           (let uu____2548 =
              let uu____2549 = FStar_Tactics_Types.goal_env g  in
              let uu____2550 = FStar_Tactics_Types.goal_type g  in
              tts uu____2549 uu____2550  in
            fail1 "goal is not irrelevant: cannot dispatch to smt (%s)"
              uu____2548))
  
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
             let uu____2599 =
               try
                 let uu____2633 =
                   let uu____2642 = FStar_BigInt.to_int_fs n1  in
                   FStar_List.splitAt uu____2642 p.FStar_Tactics_Types.goals
                    in
                 ret uu____2633
               with | uu____2664 -> fail "divide: not enough goals"  in
             bind uu____2599
               (fun uu____2690  ->
                  match uu____2690 with
                  | (lgs,rgs) ->
                      let lp =
                        let uu___373_2716 = p  in
                        {
                          FStar_Tactics_Types.main_context =
                            (uu___373_2716.FStar_Tactics_Types.main_context);
                          FStar_Tactics_Types.main_goal =
                            (uu___373_2716.FStar_Tactics_Types.main_goal);
                          FStar_Tactics_Types.all_implicits =
                            (uu___373_2716.FStar_Tactics_Types.all_implicits);
                          FStar_Tactics_Types.goals = lgs;
                          FStar_Tactics_Types.smt_goals = [];
                          FStar_Tactics_Types.depth =
                            (uu___373_2716.FStar_Tactics_Types.depth);
                          FStar_Tactics_Types.__dump =
                            (uu___373_2716.FStar_Tactics_Types.__dump);
                          FStar_Tactics_Types.psc =
                            (uu___373_2716.FStar_Tactics_Types.psc);
                          FStar_Tactics_Types.entry_range =
                            (uu___373_2716.FStar_Tactics_Types.entry_range);
                          FStar_Tactics_Types.guard_policy =
                            (uu___373_2716.FStar_Tactics_Types.guard_policy);
                          FStar_Tactics_Types.freshness =
                            (uu___373_2716.FStar_Tactics_Types.freshness);
                          FStar_Tactics_Types.tac_verb_dbg =
                            (uu___373_2716.FStar_Tactics_Types.tac_verb_dbg)
                        }  in
                      let uu____2717 = set lp  in
                      bind uu____2717
                        (fun uu____2725  ->
                           bind l
                             (fun a  ->
                                bind get
                                  (fun lp'  ->
                                     let rp =
                                       let uu___374_2741 = lp'  in
                                       {
                                         FStar_Tactics_Types.main_context =
                                           (uu___374_2741.FStar_Tactics_Types.main_context);
                                         FStar_Tactics_Types.main_goal =
                                           (uu___374_2741.FStar_Tactics_Types.main_goal);
                                         FStar_Tactics_Types.all_implicits =
                                           (uu___374_2741.FStar_Tactics_Types.all_implicits);
                                         FStar_Tactics_Types.goals = rgs;
                                         FStar_Tactics_Types.smt_goals = [];
                                         FStar_Tactics_Types.depth =
                                           (uu___374_2741.FStar_Tactics_Types.depth);
                                         FStar_Tactics_Types.__dump =
                                           (uu___374_2741.FStar_Tactics_Types.__dump);
                                         FStar_Tactics_Types.psc =
                                           (uu___374_2741.FStar_Tactics_Types.psc);
                                         FStar_Tactics_Types.entry_range =
                                           (uu___374_2741.FStar_Tactics_Types.entry_range);
                                         FStar_Tactics_Types.guard_policy =
                                           (uu___374_2741.FStar_Tactics_Types.guard_policy);
                                         FStar_Tactics_Types.freshness =
                                           (uu___374_2741.FStar_Tactics_Types.freshness);
                                         FStar_Tactics_Types.tac_verb_dbg =
                                           (uu___374_2741.FStar_Tactics_Types.tac_verb_dbg)
                                       }  in
                                     let uu____2742 = set rp  in
                                     bind uu____2742
                                       (fun uu____2750  ->
                                          bind r
                                            (fun b  ->
                                               bind get
                                                 (fun rp'  ->
                                                    let p' =
                                                      let uu___375_2766 = rp'
                                                         in
                                                      {
                                                        FStar_Tactics_Types.main_context
                                                          =
                                                          (uu___375_2766.FStar_Tactics_Types.main_context);
                                                        FStar_Tactics_Types.main_goal
                                                          =
                                                          (uu___375_2766.FStar_Tactics_Types.main_goal);
                                                        FStar_Tactics_Types.all_implicits
                                                          =
                                                          (uu___375_2766.FStar_Tactics_Types.all_implicits);
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
                                                          (uu___375_2766.FStar_Tactics_Types.depth);
                                                        FStar_Tactics_Types.__dump
                                                          =
                                                          (uu___375_2766.FStar_Tactics_Types.__dump);
                                                        FStar_Tactics_Types.psc
                                                          =
                                                          (uu___375_2766.FStar_Tactics_Types.psc);
                                                        FStar_Tactics_Types.entry_range
                                                          =
                                                          (uu___375_2766.FStar_Tactics_Types.entry_range);
                                                        FStar_Tactics_Types.guard_policy
                                                          =
                                                          (uu___375_2766.FStar_Tactics_Types.guard_policy);
                                                        FStar_Tactics_Types.freshness
                                                          =
                                                          (uu___375_2766.FStar_Tactics_Types.freshness);
                                                        FStar_Tactics_Types.tac_verb_dbg
                                                          =
                                                          (uu___375_2766.FStar_Tactics_Types.tac_verb_dbg)
                                                      }  in
                                                    let uu____2767 = set p'
                                                       in
                                                    bind uu____2767
                                                      (fun uu____2775  ->
                                                         bind
                                                           remove_solved_goals
                                                           (fun uu____2781 
                                                              -> ret (a, b)))))))))))
  
let focus : 'a . 'a tac -> 'a tac =
  fun f  ->
    let uu____2802 = divide FStar_BigInt.one f idtac  in
    bind uu____2802
      (fun uu____2815  -> match uu____2815 with | (a,()) -> ret a)
  
let rec map : 'a . 'a tac -> 'a Prims.list tac =
  fun tau  ->
    bind get
      (fun p  ->
         match p.FStar_Tactics_Types.goals with
         | [] -> ret []
         | uu____2852::uu____2853 ->
             let uu____2856 =
               let uu____2865 = map tau  in
               divide FStar_BigInt.one tau uu____2865  in
             bind uu____2856
               (fun uu____2883  ->
                  match uu____2883 with | (h,t) -> ret (h :: t)))
  
let (seq : unit tac -> unit tac -> unit tac) =
  fun t1  ->
    fun t2  ->
      let uu____2924 =
        bind t1
          (fun uu____2929  ->
             let uu____2930 = map t2  in
             bind uu____2930 (fun uu____2938  -> ret ()))
         in
      focus uu____2924
  
let (intro : unit -> FStar_Syntax_Syntax.binder tac) =
  fun uu____2947  ->
    let uu____2950 =
      let uu____2953 = cur_goal ()  in
      bind uu____2953
        (fun goal  ->
           let uu____2962 =
             let uu____2969 = FStar_Tactics_Types.goal_type goal  in
             FStar_Syntax_Util.arrow_one uu____2969  in
           match uu____2962 with
           | FStar_Pervasives_Native.Some (b,c) ->
               let uu____2978 =
                 let uu____2979 = FStar_Syntax_Util.is_total_comp c  in
                 Prims.op_Negation uu____2979  in
               if uu____2978
               then fail "Codomain is effectful"
               else
                 (let env' =
                    let uu____2984 = FStar_Tactics_Types.goal_env goal  in
                    FStar_TypeChecker_Env.push_binders uu____2984 [b]  in
                  let typ' = comp_to_typ c  in
                  let uu____2998 = new_uvar "intro" env' typ'  in
                  bind uu____2998
                    (fun uu____3014  ->
                       match uu____3014 with
                       | (body,ctx_uvar) ->
                           let sol =
                             FStar_Syntax_Util.abs [b] body
                               FStar_Pervasives_Native.None
                              in
                           let uu____3038 = set_solution goal sol  in
                           bind uu____3038
                             (fun uu____3044  ->
                                let g =
                                  FStar_Tactics_Types.mk_goal env' ctx_uvar
                                    goal.FStar_Tactics_Types.opts
                                    goal.FStar_Tactics_Types.is_guard
                                   in
                                let uu____3046 =
                                  let uu____3049 = bnorm_goal g  in
                                  replace_cur uu____3049  in
                                bind uu____3046 (fun uu____3051  -> ret b))))
           | FStar_Pervasives_Native.None  ->
               let uu____3056 =
                 let uu____3057 = FStar_Tactics_Types.goal_env goal  in
                 let uu____3058 = FStar_Tactics_Types.goal_type goal  in
                 tts uu____3057 uu____3058  in
               fail1 "goal is not an arrow (%s)" uu____3056)
       in
    FStar_All.pipe_left (wrap_err "intro") uu____2950
  
let (intro_rec :
  unit ->
    (FStar_Syntax_Syntax.binder,FStar_Syntax_Syntax.binder)
      FStar_Pervasives_Native.tuple2 tac)
  =
  fun uu____3073  ->
    let uu____3080 = cur_goal ()  in
    bind uu____3080
      (fun goal  ->
         FStar_Util.print_string
           "WARNING (intro_rec): calling this is known to cause normalizer loops\n";
         FStar_Util.print_string
           "WARNING (intro_rec): proceed at your own risk...\n";
         (let uu____3097 =
            let uu____3104 = FStar_Tactics_Types.goal_type goal  in
            FStar_Syntax_Util.arrow_one uu____3104  in
          match uu____3097 with
          | FStar_Pervasives_Native.Some (b,c) ->
              let uu____3117 =
                let uu____3118 = FStar_Syntax_Util.is_total_comp c  in
                Prims.op_Negation uu____3118  in
              if uu____3117
              then fail "Codomain is effectful"
              else
                (let bv =
                   let uu____3131 = FStar_Tactics_Types.goal_type goal  in
                   FStar_Syntax_Syntax.gen_bv "__recf"
                     FStar_Pervasives_Native.None uu____3131
                    in
                 let bs =
                   let uu____3141 = FStar_Syntax_Syntax.mk_binder bv  in
                   [uu____3141; b]  in
                 let env' =
                   let uu____3167 = FStar_Tactics_Types.goal_env goal  in
                   FStar_TypeChecker_Env.push_binders uu____3167 bs  in
                 let uu____3168 =
                   let uu____3175 = comp_to_typ c  in
                   new_uvar "intro_rec" env' uu____3175  in
                 bind uu____3168
                   (fun uu____3194  ->
                      match uu____3194 with
                      | (u,ctx_uvar_u) ->
                          let lb =
                            let uu____3208 =
                              FStar_Tactics_Types.goal_type goal  in
                            let uu____3211 =
                              FStar_Syntax_Util.abs [b] u
                                FStar_Pervasives_Native.None
                               in
                            FStar_Syntax_Util.mk_letbinding
                              (FStar_Util.Inl bv) [] uu____3208
                              FStar_Parser_Const.effect_Tot_lid uu____3211 []
                              FStar_Range.dummyRange
                             in
                          let body = FStar_Syntax_Syntax.bv_to_name bv  in
                          let uu____3229 =
                            FStar_Syntax_Subst.close_let_rec [lb] body  in
                          (match uu____3229 with
                           | (lbs,body1) ->
                               let tm =
                                 let uu____3251 =
                                   let uu____3252 =
                                     FStar_Tactics_Types.goal_witness goal
                                      in
                                   uu____3252.FStar_Syntax_Syntax.pos  in
                                 FStar_Syntax_Syntax.mk
                                   (FStar_Syntax_Syntax.Tm_let
                                      ((true, lbs), body1))
                                   FStar_Pervasives_Native.None uu____3251
                                  in
                               let uu____3265 = set_solution goal tm  in
                               bind uu____3265
                                 (fun uu____3274  ->
                                    let uu____3275 =
                                      let uu____3278 =
                                        bnorm_goal
                                          (let uu___378_3281 = goal  in
                                           {
                                             FStar_Tactics_Types.goal_main_env
                                               =
                                               (uu___378_3281.FStar_Tactics_Types.goal_main_env);
                                             FStar_Tactics_Types.goal_ctx_uvar
                                               = ctx_uvar_u;
                                             FStar_Tactics_Types.opts =
                                               (uu___378_3281.FStar_Tactics_Types.opts);
                                             FStar_Tactics_Types.is_guard =
                                               (uu___378_3281.FStar_Tactics_Types.is_guard)
                                           })
                                         in
                                      replace_cur uu____3278  in
                                    bind uu____3275
                                      (fun uu____3288  ->
                                         let uu____3289 =
                                           let uu____3294 =
                                             FStar_Syntax_Syntax.mk_binder bv
                                              in
                                           (uu____3294, b)  in
                                         ret uu____3289)))))
          | FStar_Pervasives_Native.None  ->
              let uu____3303 =
                let uu____3304 = FStar_Tactics_Types.goal_env goal  in
                let uu____3305 = FStar_Tactics_Types.goal_type goal  in
                tts uu____3304 uu____3305  in
              fail1 "intro_rec: goal is not an arrow (%s)" uu____3303))
  
let (norm : FStar_Syntax_Embeddings.norm_step Prims.list -> unit tac) =
  fun s  ->
    let uu____3323 = cur_goal ()  in
    bind uu____3323
      (fun goal  ->
         mlog
           (fun uu____3330  ->
              let uu____3331 =
                let uu____3332 = FStar_Tactics_Types.goal_witness goal  in
                FStar_Syntax_Print.term_to_string uu____3332  in
              FStar_Util.print1 "norm: witness = %s\n" uu____3331)
           (fun uu____3337  ->
              let steps =
                let uu____3341 = FStar_TypeChecker_Normalize.tr_norm_steps s
                   in
                FStar_List.append
                  [FStar_TypeChecker_Normalize.Reify;
                  FStar_TypeChecker_Normalize.UnfoldTac] uu____3341
                 in
              let t =
                let uu____3345 = FStar_Tactics_Types.goal_env goal  in
                let uu____3346 = FStar_Tactics_Types.goal_type goal  in
                normalize steps uu____3345 uu____3346  in
              let uu____3347 = FStar_Tactics_Types.goal_with_type goal t  in
              replace_cur uu____3347))
  
let (norm_term_env :
  env ->
    FStar_Syntax_Embeddings.norm_step Prims.list ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term tac)
  =
  fun e  ->
    fun s  ->
      fun t  ->
        let uu____3371 =
          mlog
            (fun uu____3376  ->
               let uu____3377 = FStar_Syntax_Print.term_to_string t  in
               FStar_Util.print1 "norm_term: tm = %s\n" uu____3377)
            (fun uu____3379  ->
               bind get
                 (fun ps  ->
                    let opts =
                      match ps.FStar_Tactics_Types.goals with
                      | g::uu____3385 -> g.FStar_Tactics_Types.opts
                      | uu____3388 -> FStar_Options.peek ()  in
                    mlog
                      (fun uu____3393  ->
                         let uu____3394 = FStar_Syntax_Print.term_to_string t
                            in
                         FStar_Util.print1 "norm_term_env: t = %s\n"
                           uu____3394)
                      (fun uu____3397  ->
                         let uu____3398 = __tc e t  in
                         bind uu____3398
                           (fun uu____3419  ->
                              match uu____3419 with
                              | (t1,uu____3429,uu____3430) ->
                                  let steps =
                                    let uu____3434 =
                                      FStar_TypeChecker_Normalize.tr_norm_steps
                                        s
                                       in
                                    FStar_List.append
                                      [FStar_TypeChecker_Normalize.Reify;
                                      FStar_TypeChecker_Normalize.UnfoldTac]
                                      uu____3434
                                     in
                                  let t2 =
                                    normalize steps
                                      ps.FStar_Tactics_Types.main_context t1
                                     in
                                  ret t2))))
           in
        FStar_All.pipe_left (wrap_err "norm_term") uu____3371
  
let (refine_intro : unit -> unit tac) =
  fun uu____3448  ->
    let uu____3451 =
      let uu____3454 = cur_goal ()  in
      bind uu____3454
        (fun g  ->
           let uu____3461 =
             let uu____3472 = FStar_Tactics_Types.goal_env g  in
             let uu____3473 = FStar_Tactics_Types.goal_type g  in
             FStar_TypeChecker_Rel.base_and_refinement uu____3472 uu____3473
              in
           match uu____3461 with
           | (uu____3476,FStar_Pervasives_Native.None ) ->
               fail "not a refinement"
           | (t,FStar_Pervasives_Native.Some (bv,phi)) ->
               let g1 = FStar_Tactics_Types.goal_with_type g t  in
               let uu____3501 =
                 let uu____3506 =
                   let uu____3511 =
                     let uu____3512 = FStar_Syntax_Syntax.mk_binder bv  in
                     [uu____3512]  in
                   FStar_Syntax_Subst.open_term uu____3511 phi  in
                 match uu____3506 with
                 | (bvs,phi1) ->
                     let uu____3537 =
                       let uu____3538 = FStar_List.hd bvs  in
                       FStar_Pervasives_Native.fst uu____3538  in
                     (uu____3537, phi1)
                  in
               (match uu____3501 with
                | (bv1,phi1) ->
                    let uu____3557 =
                      let uu____3560 = FStar_Tactics_Types.goal_env g  in
                      let uu____3561 =
                        let uu____3562 =
                          let uu____3565 =
                            let uu____3566 =
                              let uu____3573 =
                                FStar_Tactics_Types.goal_witness g  in
                              (bv1, uu____3573)  in
                            FStar_Syntax_Syntax.NT uu____3566  in
                          [uu____3565]  in
                        FStar_Syntax_Subst.subst uu____3562 phi1  in
                      mk_irrelevant_goal "refine_intro refinement" uu____3560
                        uu____3561 g.FStar_Tactics_Types.opts
                       in
                    bind uu____3557
                      (fun g2  ->
                         bind __dismiss
                           (fun uu____3581  -> add_goals [g1; g2]))))
       in
    FStar_All.pipe_left (wrap_err "refine_intro") uu____3451
  
let (__exact_now : Prims.bool -> FStar_Syntax_Syntax.term -> unit tac) =
  fun set_expected_typ1  ->
    fun t  ->
      let uu____3600 = cur_goal ()  in
      bind uu____3600
        (fun goal  ->
           let env =
             if set_expected_typ1
             then
               let uu____3608 = FStar_Tactics_Types.goal_env goal  in
               let uu____3609 = FStar_Tactics_Types.goal_type goal  in
               FStar_TypeChecker_Env.set_expected_typ uu____3608 uu____3609
             else FStar_Tactics_Types.goal_env goal  in
           let uu____3611 = __tc env t  in
           bind uu____3611
             (fun uu____3630  ->
                match uu____3630 with
                | (t1,typ,guard) ->
                    mlog
                      (fun uu____3645  ->
                         let uu____3646 =
                           FStar_Syntax_Print.term_to_string typ  in
                         let uu____3647 =
                           let uu____3648 = FStar_Tactics_Types.goal_env goal
                              in
                           FStar_TypeChecker_Rel.guard_to_string uu____3648
                             guard
                            in
                         FStar_Util.print2
                           "__exact_now: got type %s\n__exact_now: and guard %s\n"
                           uu____3646 uu____3647)
                      (fun uu____3651  ->
                         let uu____3652 =
                           let uu____3655 = FStar_Tactics_Types.goal_env goal
                              in
                           proc_guard "__exact typing" uu____3655 guard  in
                         bind uu____3652
                           (fun uu____3657  ->
                              mlog
                                (fun uu____3661  ->
                                   let uu____3662 =
                                     FStar_Syntax_Print.term_to_string typ
                                      in
                                   let uu____3663 =
                                     let uu____3664 =
                                       FStar_Tactics_Types.goal_type goal  in
                                     FStar_Syntax_Print.term_to_string
                                       uu____3664
                                      in
                                   FStar_Util.print2
                                     "__exact_now: unifying %s and %s\n"
                                     uu____3662 uu____3663)
                                (fun uu____3667  ->
                                   let uu____3668 =
                                     let uu____3671 =
                                       FStar_Tactics_Types.goal_env goal  in
                                     let uu____3672 =
                                       FStar_Tactics_Types.goal_type goal  in
                                     do_unify uu____3671 typ uu____3672  in
                                   bind uu____3668
                                     (fun b  ->
                                        if b
                                        then solve goal t1
                                        else
                                          (let uu____3678 =
                                             let uu____3679 =
                                               FStar_Tactics_Types.goal_env
                                                 goal
                                                in
                                             tts uu____3679 t1  in
                                           let uu____3680 =
                                             let uu____3681 =
                                               FStar_Tactics_Types.goal_env
                                                 goal
                                                in
                                             tts uu____3681 typ  in
                                           let uu____3682 =
                                             let uu____3683 =
                                               FStar_Tactics_Types.goal_env
                                                 goal
                                                in
                                             let uu____3684 =
                                               FStar_Tactics_Types.goal_type
                                                 goal
                                                in
                                             tts uu____3683 uu____3684  in
                                           let uu____3685 =
                                             let uu____3686 =
                                               FStar_Tactics_Types.goal_env
                                                 goal
                                                in
                                             let uu____3687 =
                                               FStar_Tactics_Types.goal_witness
                                                 goal
                                                in
                                             tts uu____3686 uu____3687  in
                                           fail4
                                             "%s : %s does not exactly solve the goal %s (witness = %s)"
                                             uu____3678 uu____3680 uu____3682
                                             uu____3685)))))))
  
let (t_exact : Prims.bool -> FStar_Syntax_Syntax.term -> unit tac) =
  fun set_expected_typ1  ->
    fun tm  ->
      let uu____3702 =
        mlog
          (fun uu____3707  ->
             let uu____3708 = FStar_Syntax_Print.term_to_string tm  in
             FStar_Util.print1 "t_exact: tm = %s\n" uu____3708)
          (fun uu____3711  ->
             let uu____3712 =
               let uu____3719 = __exact_now set_expected_typ1 tm  in
               trytac' uu____3719  in
             bind uu____3712
               (fun uu___340_3728  ->
                  match uu___340_3728 with
                  | FStar_Util.Inr r -> ret ()
                  | FStar_Util.Inl e ->
                      mlog
                        (fun uu____3738  ->
                           FStar_Util.print_string
                             "__exact_now failed, trying refine...\n")
                        (fun uu____3741  ->
                           let uu____3742 =
                             let uu____3749 =
                               let uu____3752 =
                                 norm [FStar_Syntax_Embeddings.Delta]  in
                               bind uu____3752
                                 (fun uu____3757  ->
                                    let uu____3758 = refine_intro ()  in
                                    bind uu____3758
                                      (fun uu____3762  ->
                                         __exact_now set_expected_typ1 tm))
                                in
                             trytac' uu____3749  in
                           bind uu____3742
                             (fun uu___339_3769  ->
                                match uu___339_3769 with
                                | FStar_Util.Inr r -> ret ()
                                | FStar_Util.Inl uu____3777 -> fail e))))
         in
      FStar_All.pipe_left (wrap_err "exact") uu____3702
  
let rec mapM : 'a 'b . ('a -> 'b tac) -> 'a Prims.list -> 'b Prims.list tac =
  fun f  ->
    fun l  ->
      match l with
      | [] -> ret []
      | x::xs ->
          let uu____3827 = f x  in
          bind uu____3827
            (fun y  ->
               let uu____3835 = mapM f xs  in
               bind uu____3835 (fun ys  -> ret (y :: ys)))
  
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
          let uu____3906 = do_unify e ty1 ty2  in
          bind uu____3906
            (fun uu___341_3918  ->
               if uu___341_3918
               then ret acc
               else
                 (let uu____3937 = FStar_Syntax_Util.arrow_one ty1  in
                  match uu____3937 with
                  | FStar_Pervasives_Native.None  ->
                      let uu____3958 = FStar_Syntax_Print.term_to_string ty1
                         in
                      let uu____3959 = FStar_Syntax_Print.term_to_string ty2
                         in
                      fail2 "Could not instantiate, %s to %s" uu____3958
                        uu____3959
                  | FStar_Pervasives_Native.Some (b,c) ->
                      let uu____3974 =
                        let uu____3975 = FStar_Syntax_Util.is_total_comp c
                           in
                        Prims.op_Negation uu____3975  in
                      if uu____3974
                      then fail "Codomain is effectful"
                      else
                        (let uu____3995 =
                           new_uvar "apply arg" e
                             (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                            in
                         bind uu____3995
                           (fun uu____4021  ->
                              match uu____4021 with
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
      let uu____4107 =
        mlog
          (fun uu____4112  ->
             let uu____4113 = FStar_Syntax_Print.term_to_string tm  in
             FStar_Util.print1 "apply: tm = %s\n" uu____4113)
          (fun uu____4116  ->
             let uu____4117 = cur_goal ()  in
             bind uu____4117
               (fun goal  ->
                  let e = FStar_Tactics_Types.goal_env goal  in
                  let uu____4125 = __tc e tm  in
                  bind uu____4125
                    (fun uu____4146  ->
                       match uu____4146 with
                       | (tm1,typ,guard) ->
                           let typ1 = bnorm e typ  in
                           let uu____4159 =
                             let uu____4170 =
                               FStar_Tactics_Types.goal_type goal  in
                             try_match_by_application e typ1 uu____4170  in
                           bind uu____4159
                             (fun uvs  ->
                                let w =
                                  FStar_List.fold_right
                                    (fun uu____4213  ->
                                       fun w  ->
                                         match uu____4213 with
                                         | (uvt,q,uu____4231) ->
                                             FStar_Syntax_Util.mk_app w
                                               [(uvt, q)]) uvs tm1
                                   in
                                let uvset =
                                  let uu____4263 =
                                    FStar_Syntax_Free.new_uv_set ()  in
                                  FStar_List.fold_right
                                    (fun uu____4280  ->
                                       fun s  ->
                                         match uu____4280 with
                                         | (uu____4292,uu____4293,uv) ->
                                             let uu____4295 =
                                               FStar_Syntax_Free.uvars
                                                 uv.FStar_Syntax_Syntax.ctx_uvar_typ
                                                in
                                             FStar_Util.set_union s
                                               uu____4295) uvs uu____4263
                                   in
                                let free_in_some_goal uv =
                                  FStar_Util.set_mem uv uvset  in
                                let uu____4304 = solve' goal w  in
                                bind uu____4304
                                  (fun uu____4309  ->
                                     let uu____4310 =
                                       mapM
                                         (fun uu____4327  ->
                                            match uu____4327 with
                                            | (uvt,q,uv) ->
                                                let uu____4339 =
                                                  FStar_Syntax_Unionfind.find
                                                    uv.FStar_Syntax_Syntax.ctx_uvar_head
                                                   in
                                                (match uu____4339 with
                                                 | FStar_Pervasives_Native.Some
                                                     uu____4344 -> ret ()
                                                 | FStar_Pervasives_Native.None
                                                      ->
                                                     let uu____4345 =
                                                       uopt &&
                                                         (free_in_some_goal
                                                            uv)
                                                        in
                                                     if uu____4345
                                                     then ret ()
                                                     else
                                                       (let uu____4349 =
                                                          let uu____4352 =
                                                            bnorm_goal
                                                              (let uu___379_4355
                                                                 = goal  in
                                                               {
                                                                 FStar_Tactics_Types.goal_main_env
                                                                   =
                                                                   (uu___379_4355.FStar_Tactics_Types.goal_main_env);
                                                                 FStar_Tactics_Types.goal_ctx_uvar
                                                                   = uv;
                                                                 FStar_Tactics_Types.opts
                                                                   =
                                                                   (uu___379_4355.FStar_Tactics_Types.opts);
                                                                 FStar_Tactics_Types.is_guard
                                                                   = false
                                                               })
                                                             in
                                                          [uu____4352]  in
                                                        add_goals uu____4349)))
                                         uvs
                                        in
                                     bind uu____4310
                                       (fun uu____4359  ->
                                          proc_guard "apply guard" e guard))))))
         in
      FStar_All.pipe_left (wrap_err "apply") uu____4107
  
let (lemma_or_sq :
  FStar_Syntax_Syntax.comp ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun c  ->
    let ct = FStar_Syntax_Util.comp_to_comp_typ_nouniv c  in
    let uu____4384 =
      FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
        FStar_Parser_Const.effect_Lemma_lid
       in
    if uu____4384
    then
      let uu____4391 =
        match ct.FStar_Syntax_Syntax.effect_args with
        | pre::post::uu____4406 ->
            ((FStar_Pervasives_Native.fst pre),
              (FStar_Pervasives_Native.fst post))
        | uu____4459 -> failwith "apply_lemma: impossible: not a lemma"  in
      match uu____4391 with
      | (pre,post) ->
          let post1 =
            let uu____4491 =
              let uu____4502 =
                FStar_Syntax_Syntax.as_arg FStar_Syntax_Util.exp_unit  in
              [uu____4502]  in
            FStar_Syntax_Util.mk_app post uu____4491  in
          FStar_Pervasives_Native.Some (pre, post1)
    else
      (let uu____4532 =
         FStar_Syntax_Util.is_pure_effect ct.FStar_Syntax_Syntax.effect_name
          in
       if uu____4532
       then
         let uu____4539 =
           FStar_Syntax_Util.un_squash ct.FStar_Syntax_Syntax.result_typ  in
         FStar_Util.map_opt uu____4539
           (fun post  -> (FStar_Syntax_Util.t_true, post))
       else FStar_Pervasives_Native.None)
  
let (apply_lemma : FStar_Syntax_Syntax.term -> unit tac) =
  fun tm  ->
    let uu____4572 =
      let uu____4575 =
        mlog
          (fun uu____4580  ->
             let uu____4581 = FStar_Syntax_Print.term_to_string tm  in
             FStar_Util.print1 "apply_lemma: tm = %s\n" uu____4581)
          (fun uu____4585  ->
             let is_unit_t t =
               let uu____4592 =
                 let uu____4593 = FStar_Syntax_Subst.compress t  in
                 uu____4593.FStar_Syntax_Syntax.n  in
               match uu____4592 with
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.unit_lid
                   -> true
               | uu____4597 -> false  in
             let uu____4598 = cur_goal ()  in
             bind uu____4598
               (fun goal  ->
                  let uu____4604 =
                    let uu____4613 = FStar_Tactics_Types.goal_env goal  in
                    __tc uu____4613 tm  in
                  bind uu____4604
                    (fun uu____4628  ->
                       match uu____4628 with
                       | (tm1,t,guard) ->
                           let uu____4640 =
                             FStar_Syntax_Util.arrow_formals_comp t  in
                           (match uu____4640 with
                            | (bs,comp) ->
                                let uu____4673 = lemma_or_sq comp  in
                                (match uu____4673 with
                                 | FStar_Pervasives_Native.None  ->
                                     fail "not a lemma or squashed function"
                                 | FStar_Pervasives_Native.Some (pre,post) ->
                                     let uu____4692 =
                                       FStar_List.fold_left
                                         (fun uu____4740  ->
                                            fun uu____4741  ->
                                              match (uu____4740, uu____4741)
                                              with
                                              | ((uvs,guard1,subst1),(b,aq))
                                                  ->
                                                  let b_t =
                                                    FStar_Syntax_Subst.subst
                                                      subst1
                                                      b.FStar_Syntax_Syntax.sort
                                                     in
                                                  let uu____4854 =
                                                    is_unit_t b_t  in
                                                  if uu____4854
                                                  then
                                                    (((FStar_Syntax_Util.exp_unit,
                                                        aq) :: uvs), guard1,
                                                      ((FStar_Syntax_Syntax.NT
                                                          (b,
                                                            FStar_Syntax_Util.exp_unit))
                                                      :: subst1))
                                                  else
                                                    (let uu____4892 =
                                                       let uu____4905 =
                                                         let uu____4906 =
                                                           FStar_Tactics_Types.goal_type
                                                             goal
                                                            in
                                                         uu____4906.FStar_Syntax_Syntax.pos
                                                          in
                                                       let uu____4909 =
                                                         FStar_Tactics_Types.goal_env
                                                           goal
                                                          in
                                                       FStar_TypeChecker_Util.new_implicit_var
                                                         "apply_lemma"
                                                         uu____4905
                                                         uu____4909 b_t
                                                        in
                                                     match uu____4892 with
                                                     | (u,uu____4927,g_u) ->
                                                         let uu____4941 =
                                                           FStar_TypeChecker_Env.conj_guard
                                                             guard1 g_u
                                                            in
                                                         (((u, aq) :: uvs),
                                                           uu____4941,
                                                           ((FStar_Syntax_Syntax.NT
                                                               (b, u)) ::
                                                           subst1))))
                                         ([], guard, []) bs
                                        in
                                     (match uu____4692 with
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
                                          let uu____5020 =
                                            let uu____5023 =
                                              FStar_Tactics_Types.goal_env
                                                goal
                                               in
                                            let uu____5024 =
                                              FStar_Syntax_Util.mk_squash
                                                FStar_Syntax_Syntax.U_zero
                                                post1
                                               in
                                            let uu____5025 =
                                              FStar_Tactics_Types.goal_type
                                                goal
                                               in
                                            do_unify uu____5023 uu____5024
                                              uu____5025
                                             in
                                          bind uu____5020
                                            (fun b  ->
                                               if Prims.op_Negation b
                                               then
                                                 let uu____5033 =
                                                   let uu____5034 =
                                                     FStar_Tactics_Types.goal_env
                                                       goal
                                                      in
                                                   tts uu____5034 tm1  in
                                                 let uu____5035 =
                                                   let uu____5036 =
                                                     FStar_Tactics_Types.goal_env
                                                       goal
                                                      in
                                                   let uu____5037 =
                                                     FStar_Syntax_Util.mk_squash
                                                       FStar_Syntax_Syntax.U_zero
                                                       post1
                                                      in
                                                   tts uu____5036 uu____5037
                                                    in
                                                 let uu____5038 =
                                                   let uu____5039 =
                                                     FStar_Tactics_Types.goal_env
                                                       goal
                                                      in
                                                   let uu____5040 =
                                                     FStar_Tactics_Types.goal_type
                                                       goal
                                                      in
                                                   tts uu____5039 uu____5040
                                                    in
                                                 fail3
                                                   "Cannot instantiate lemma %s (with postcondition: %s) to match goal (%s)"
                                                   uu____5033 uu____5035
                                                   uu____5038
                                               else
                                                 (let uu____5042 =
                                                    add_implicits
                                                      implicits.FStar_TypeChecker_Env.implicits
                                                     in
                                                  bind uu____5042
                                                    (fun uu____5047  ->
                                                       let uu____5048 =
                                                         solve' goal
                                                           FStar_Syntax_Util.exp_unit
                                                          in
                                                       bind uu____5048
                                                         (fun uu____5056  ->
                                                            let is_free_uvar
                                                              uv t1 =
                                                              let free_uvars
                                                                =
                                                                let uu____5081
                                                                  =
                                                                  let uu____5084
                                                                    =
                                                                    FStar_Syntax_Free.uvars
                                                                    t1  in
                                                                  FStar_Util.set_elements
                                                                    uu____5084
                                                                   in
                                                                FStar_List.map
                                                                  (fun x  ->
                                                                    x.FStar_Syntax_Syntax.ctx_uvar_head)
                                                                  uu____5081
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
                                                                   let uu____5119
                                                                    =
                                                                    FStar_Tactics_Types.goal_type
                                                                    g'  in
                                                                   is_free_uvar
                                                                    uv
                                                                    uu____5119)
                                                                goals
                                                               in
                                                            let checkone t1
                                                              goals =
                                                              let uu____5135
                                                                =
                                                                FStar_Syntax_Util.head_and_args
                                                                  t1
                                                                 in
                                                              match uu____5135
                                                              with
                                                              | (hd1,uu____5153)
                                                                  ->
                                                                  (match 
                                                                    hd1.FStar_Syntax_Syntax.n
                                                                   with
                                                                   | 
                                                                   FStar_Syntax_Syntax.Tm_uvar
                                                                    (uv,uu____5179)
                                                                    ->
                                                                    appears
                                                                    uv.FStar_Syntax_Syntax.ctx_uvar_head
                                                                    goals
                                                                   | 
                                                                   uu____5196
                                                                    -> false)
                                                               in
                                                            let uu____5197 =
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
                                                                    let uu____5227
                                                                    =
                                                                    FStar_Syntax_Util.head_and_args
                                                                    term  in
                                                                    match uu____5227
                                                                    with
                                                                    | 
                                                                    (hd1,uu____5249)
                                                                    ->
                                                                    let uu____5274
                                                                    =
                                                                    let uu____5275
                                                                    =
                                                                    FStar_Syntax_Subst.compress
                                                                    hd1  in
                                                                    uu____5275.FStar_Syntax_Syntax.n
                                                                     in
                                                                    (match uu____5274
                                                                    with
                                                                    | 
                                                                    FStar_Syntax_Syntax.Tm_uvar
                                                                    (ctx_uvar1,uu____5283)
                                                                    ->
                                                                    let goal1
                                                                    =
                                                                    bnorm_goal
                                                                    (let uu___380_5303
                                                                    = goal
                                                                     in
                                                                    {
                                                                    FStar_Tactics_Types.goal_main_env
                                                                    =
                                                                    (uu___380_5303.FStar_Tactics_Types.goal_main_env);
                                                                    FStar_Tactics_Types.goal_ctx_uvar
                                                                    =
                                                                    ctx_uvar1;
                                                                    FStar_Tactics_Types.opts
                                                                    =
                                                                    (uu___380_5303.FStar_Tactics_Types.opts);
                                                                    FStar_Tactics_Types.is_guard
                                                                    =
                                                                    (uu___380_5303.FStar_Tactics_Types.is_guard)
                                                                    })  in
                                                                    ret
                                                                    [goal1]
                                                                    | 
                                                                    uu____5306
                                                                    ->
                                                                    let env =
                                                                    let uu___381_5308
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    goal  in
                                                                    {
                                                                    FStar_TypeChecker_Env.solver
                                                                    =
                                                                    (uu___381_5308.FStar_TypeChecker_Env.solver);
                                                                    FStar_TypeChecker_Env.range
                                                                    =
                                                                    (uu___381_5308.FStar_TypeChecker_Env.range);
                                                                    FStar_TypeChecker_Env.curmodule
                                                                    =
                                                                    (uu___381_5308.FStar_TypeChecker_Env.curmodule);
                                                                    FStar_TypeChecker_Env.gamma
                                                                    =
                                                                    (ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_gamma);
                                                                    FStar_TypeChecker_Env.gamma_sig
                                                                    =
                                                                    (uu___381_5308.FStar_TypeChecker_Env.gamma_sig);
                                                                    FStar_TypeChecker_Env.gamma_cache
                                                                    =
                                                                    (uu___381_5308.FStar_TypeChecker_Env.gamma_cache);
                                                                    FStar_TypeChecker_Env.modules
                                                                    =
                                                                    (uu___381_5308.FStar_TypeChecker_Env.modules);
                                                                    FStar_TypeChecker_Env.expected_typ
                                                                    =
                                                                    (uu___381_5308.FStar_TypeChecker_Env.expected_typ);
                                                                    FStar_TypeChecker_Env.sigtab
                                                                    =
                                                                    (uu___381_5308.FStar_TypeChecker_Env.sigtab);
                                                                    FStar_TypeChecker_Env.attrtab
                                                                    =
                                                                    (uu___381_5308.FStar_TypeChecker_Env.attrtab);
                                                                    FStar_TypeChecker_Env.is_pattern
                                                                    =
                                                                    (uu___381_5308.FStar_TypeChecker_Env.is_pattern);
                                                                    FStar_TypeChecker_Env.instantiate_imp
                                                                    =
                                                                    (uu___381_5308.FStar_TypeChecker_Env.instantiate_imp);
                                                                    FStar_TypeChecker_Env.effects
                                                                    =
                                                                    (uu___381_5308.FStar_TypeChecker_Env.effects);
                                                                    FStar_TypeChecker_Env.generalize
                                                                    =
                                                                    (uu___381_5308.FStar_TypeChecker_Env.generalize);
                                                                    FStar_TypeChecker_Env.letrecs
                                                                    =
                                                                    (uu___381_5308.FStar_TypeChecker_Env.letrecs);
                                                                    FStar_TypeChecker_Env.top_level
                                                                    =
                                                                    (uu___381_5308.FStar_TypeChecker_Env.top_level);
                                                                    FStar_TypeChecker_Env.check_uvars
                                                                    =
                                                                    (uu___381_5308.FStar_TypeChecker_Env.check_uvars);
                                                                    FStar_TypeChecker_Env.use_eq
                                                                    =
                                                                    (uu___381_5308.FStar_TypeChecker_Env.use_eq);
                                                                    FStar_TypeChecker_Env.is_iface
                                                                    =
                                                                    (uu___381_5308.FStar_TypeChecker_Env.is_iface);
                                                                    FStar_TypeChecker_Env.admit
                                                                    =
                                                                    (uu___381_5308.FStar_TypeChecker_Env.admit);
                                                                    FStar_TypeChecker_Env.lax
                                                                    =
                                                                    (uu___381_5308.FStar_TypeChecker_Env.lax);
                                                                    FStar_TypeChecker_Env.lax_universes
                                                                    =
                                                                    (uu___381_5308.FStar_TypeChecker_Env.lax_universes);
                                                                    FStar_TypeChecker_Env.phase1
                                                                    =
                                                                    (uu___381_5308.FStar_TypeChecker_Env.phase1);
                                                                    FStar_TypeChecker_Env.failhard
                                                                    =
                                                                    (uu___381_5308.FStar_TypeChecker_Env.failhard);
                                                                    FStar_TypeChecker_Env.nosynth
                                                                    =
                                                                    (uu___381_5308.FStar_TypeChecker_Env.nosynth);
                                                                    FStar_TypeChecker_Env.uvar_subtyping
                                                                    =
                                                                    (uu___381_5308.FStar_TypeChecker_Env.uvar_subtyping);
                                                                    FStar_TypeChecker_Env.tc_term
                                                                    =
                                                                    (uu___381_5308.FStar_TypeChecker_Env.tc_term);
                                                                    FStar_TypeChecker_Env.type_of
                                                                    =
                                                                    (uu___381_5308.FStar_TypeChecker_Env.type_of);
                                                                    FStar_TypeChecker_Env.universe_of
                                                                    =
                                                                    (uu___381_5308.FStar_TypeChecker_Env.universe_of);
                                                                    FStar_TypeChecker_Env.check_type_of
                                                                    =
                                                                    (uu___381_5308.FStar_TypeChecker_Env.check_type_of);
                                                                    FStar_TypeChecker_Env.use_bv_sorts
                                                                    =
                                                                    (uu___381_5308.FStar_TypeChecker_Env.use_bv_sorts);
                                                                    FStar_TypeChecker_Env.qtbl_name_and_index
                                                                    =
                                                                    (uu___381_5308.FStar_TypeChecker_Env.qtbl_name_and_index);
                                                                    FStar_TypeChecker_Env.normalized_eff_names
                                                                    =
                                                                    (uu___381_5308.FStar_TypeChecker_Env.normalized_eff_names);
                                                                    FStar_TypeChecker_Env.proof_ns
                                                                    =
                                                                    (uu___381_5308.FStar_TypeChecker_Env.proof_ns);
                                                                    FStar_TypeChecker_Env.synth_hook
                                                                    =
                                                                    (uu___381_5308.FStar_TypeChecker_Env.synth_hook);
                                                                    FStar_TypeChecker_Env.splice
                                                                    =
                                                                    (uu___381_5308.FStar_TypeChecker_Env.splice);
                                                                    FStar_TypeChecker_Env.is_native_tactic
                                                                    =
                                                                    (uu___381_5308.FStar_TypeChecker_Env.is_native_tactic);
                                                                    FStar_TypeChecker_Env.identifier_info
                                                                    =
                                                                    (uu___381_5308.FStar_TypeChecker_Env.identifier_info);
                                                                    FStar_TypeChecker_Env.tc_hooks
                                                                    =
                                                                    (uu___381_5308.FStar_TypeChecker_Env.tc_hooks);
                                                                    FStar_TypeChecker_Env.dsenv
                                                                    =
                                                                    (uu___381_5308.FStar_TypeChecker_Env.dsenv);
                                                                    FStar_TypeChecker_Env.dep_graph
                                                                    =
                                                                    (uu___381_5308.FStar_TypeChecker_Env.dep_graph)
                                                                    }  in
                                                                    let g_typ
                                                                    =
                                                                    let uu____5310
                                                                    =
                                                                    FStar_Options.__temp_fast_implicits
                                                                    ()  in
                                                                    if
                                                                    uu____5310
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
                                                                    let uu____5313
                                                                    =
                                                                    let uu____5320
                                                                    =
                                                                    FStar_TypeChecker_Env.set_expected_typ
                                                                    env
                                                                    ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_typ
                                                                     in
                                                                    env.FStar_TypeChecker_Env.type_of
                                                                    uu____5320
                                                                    term1  in
                                                                    match uu____5313
                                                                    with
                                                                    | 
                                                                    (uu____5321,uu____5322,g_typ)
                                                                    -> g_typ)
                                                                     in
                                                                    let uu____5324
                                                                    =
                                                                    let uu____5327
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    goal  in
                                                                    proc_guard
                                                                    "apply_lemma solved arg"
                                                                    uu____5327
                                                                    g_typ  in
                                                                    bind
                                                                    uu____5324
                                                                    (fun
                                                                    uu____5331
                                                                     ->
                                                                    ret []))))
                                                               in
                                                            bind uu____5197
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
                                                                    let uu____5393
                                                                    = f x xs1
                                                                     in
                                                                    if
                                                                    uu____5393
                                                                    then
                                                                    let uu____5396
                                                                    =
                                                                    filter' f
                                                                    xs1  in x
                                                                    ::
                                                                    uu____5396
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
                                                                    let uu____5410
                                                                    =
                                                                    let uu____5411
                                                                    =
                                                                    FStar_Tactics_Types.goal_witness
                                                                    g  in
                                                                    checkone
                                                                    uu____5411
                                                                    goals  in
                                                                    Prims.op_Negation
                                                                    uu____5410)
                                                                    sub_goals1
                                                                    in
                                                                 let uu____5412
                                                                   =
                                                                   let uu____5415
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    goal  in
                                                                   proc_guard
                                                                    "apply_lemma guard"
                                                                    uu____5415
                                                                    guard
                                                                    in
                                                                 bind
                                                                   uu____5412
                                                                   (fun
                                                                    uu____5418
                                                                     ->
                                                                    let uu____5419
                                                                    =
                                                                    let uu____5422
                                                                    =
                                                                    let uu____5423
                                                                    =
                                                                    let uu____5424
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    goal  in
                                                                    let uu____5425
                                                                    =
                                                                    FStar_Syntax_Util.mk_squash
                                                                    FStar_Syntax_Syntax.U_zero
                                                                    pre1  in
                                                                    istrivial
                                                                    uu____5424
                                                                    uu____5425
                                                                     in
                                                                    Prims.op_Negation
                                                                    uu____5423
                                                                     in
                                                                    if
                                                                    uu____5422
                                                                    then
                                                                    let uu____5428
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    goal  in
                                                                    add_irrelevant_goal
                                                                    "apply_lemma precondition"
                                                                    uu____5428
                                                                    pre1
                                                                    goal.FStar_Tactics_Types.opts
                                                                    else
                                                                    ret ()
                                                                     in
                                                                    bind
                                                                    uu____5419
                                                                    (fun
                                                                    uu____5431
                                                                     ->
                                                                    add_goals
                                                                    sub_goals2)))))))))))))
         in
      focus uu____4575  in
    FStar_All.pipe_left (wrap_err "apply_lemma") uu____4572
  
let (destruct_eq' :
  FStar_Reflection_Data.typ ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun typ  ->
    let uu____5453 = FStar_Syntax_Util.destruct_typ_as_formula typ  in
    match uu____5453 with
    | FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn
        (l,uu____5463::(e1,uu____5465)::(e2,uu____5467)::[])) when
        FStar_Ident.lid_equals l FStar_Parser_Const.eq2_lid ->
        FStar_Pervasives_Native.Some (e1, e2)
    | uu____5528 -> FStar_Pervasives_Native.None
  
let (destruct_eq :
  FStar_Reflection_Data.typ ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun typ  ->
    let uu____5552 = destruct_eq' typ  in
    match uu____5552 with
    | FStar_Pervasives_Native.Some t -> FStar_Pervasives_Native.Some t
    | FStar_Pervasives_Native.None  ->
        let uu____5582 = FStar_Syntax_Util.un_squash typ  in
        (match uu____5582 with
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
        let uu____5644 = FStar_TypeChecker_Env.pop_bv e1  in
        match uu____5644 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (bv',e') ->
            if FStar_Syntax_Syntax.bv_eq bvar bv'
            then FStar_Pervasives_Native.Some (e', [])
            else
              (let uu____5692 = aux e'  in
               FStar_Util.map_opt uu____5692
                 (fun uu____5716  ->
                    match uu____5716 with | (e'',bvs) -> (e'', (bv' :: bvs))))
         in
      let uu____5737 = aux e  in
      FStar_Util.map_opt uu____5737
        (fun uu____5761  ->
           match uu____5761 with | (e',bvs) -> (e', (FStar_List.rev bvs)))
  
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
          let uu____5828 =
            let uu____5837 = FStar_Tactics_Types.goal_env g  in
            split_env b1 uu____5837  in
          FStar_Util.map_opt uu____5828
            (fun uu____5852  ->
               match uu____5852 with
               | (e0,bvs) ->
                   let s1 bv =
                     let uu___382_5871 = bv  in
                     let uu____5872 =
                       FStar_Syntax_Subst.subst s bv.FStar_Syntax_Syntax.sort
                        in
                     {
                       FStar_Syntax_Syntax.ppname =
                         (uu___382_5871.FStar_Syntax_Syntax.ppname);
                       FStar_Syntax_Syntax.index =
                         (uu___382_5871.FStar_Syntax_Syntax.index);
                       FStar_Syntax_Syntax.sort = uu____5872
                     }  in
                   let bvs1 = FStar_List.map s1 bvs  in
                   let new_env = push_bvs e0 (b2 :: bvs1)  in
                   let new_goal =
                     let uu___383_5880 = g.FStar_Tactics_Types.goal_ctx_uvar
                        in
                     let uu____5881 =
                       FStar_TypeChecker_Env.all_binders new_env  in
                     let uu____5890 =
                       let uu____5893 = FStar_Tactics_Types.goal_type g  in
                       FStar_Syntax_Subst.subst s uu____5893  in
                     {
                       FStar_Syntax_Syntax.ctx_uvar_head =
                         (uu___383_5880.FStar_Syntax_Syntax.ctx_uvar_head);
                       FStar_Syntax_Syntax.ctx_uvar_gamma =
                         (new_env.FStar_TypeChecker_Env.gamma);
                       FStar_Syntax_Syntax.ctx_uvar_binders = uu____5881;
                       FStar_Syntax_Syntax.ctx_uvar_typ = uu____5890;
                       FStar_Syntax_Syntax.ctx_uvar_reason =
                         (uu___383_5880.FStar_Syntax_Syntax.ctx_uvar_reason);
                       FStar_Syntax_Syntax.ctx_uvar_should_check =
                         (uu___383_5880.FStar_Syntax_Syntax.ctx_uvar_should_check);
                       FStar_Syntax_Syntax.ctx_uvar_range =
                         (uu___383_5880.FStar_Syntax_Syntax.ctx_uvar_range)
                     }  in
                   let uu___384_5894 = g  in
                   {
                     FStar_Tactics_Types.goal_main_env =
                       (uu___384_5894.FStar_Tactics_Types.goal_main_env);
                     FStar_Tactics_Types.goal_ctx_uvar = new_goal;
                     FStar_Tactics_Types.opts =
                       (uu___384_5894.FStar_Tactics_Types.opts);
                     FStar_Tactics_Types.is_guard =
                       (uu___384_5894.FStar_Tactics_Types.is_guard)
                   })
  
let (rewrite : FStar_Syntax_Syntax.binder -> unit tac) =
  fun h  ->
    let uu____5904 =
      let uu____5907 = cur_goal ()  in
      bind uu____5907
        (fun goal  ->
           let uu____5915 = h  in
           match uu____5915 with
           | (bv,uu____5919) ->
               mlog
                 (fun uu____5927  ->
                    let uu____5928 = FStar_Syntax_Print.bv_to_string bv  in
                    let uu____5929 =
                      FStar_Syntax_Print.term_to_string
                        bv.FStar_Syntax_Syntax.sort
                       in
                    FStar_Util.print2 "+++Rewrite %s : %s\n" uu____5928
                      uu____5929)
                 (fun uu____5932  ->
                    let uu____5933 =
                      let uu____5942 = FStar_Tactics_Types.goal_env goal  in
                      split_env bv uu____5942  in
                    match uu____5933 with
                    | FStar_Pervasives_Native.None  ->
                        fail "binder not found in environment"
                    | FStar_Pervasives_Native.Some (e0,bvs) ->
                        let uu____5963 =
                          destruct_eq bv.FStar_Syntax_Syntax.sort  in
                        (match uu____5963 with
                         | FStar_Pervasives_Native.Some (x,e) ->
                             let uu____5978 =
                               let uu____5979 = FStar_Syntax_Subst.compress x
                                  in
                               uu____5979.FStar_Syntax_Syntax.n  in
                             (match uu____5978 with
                              | FStar_Syntax_Syntax.Tm_name x1 ->
                                  let s = [FStar_Syntax_Syntax.NT (x1, e)]
                                     in
                                  let s1 bv1 =
                                    let uu___385_5996 = bv1  in
                                    let uu____5997 =
                                      FStar_Syntax_Subst.subst s
                                        bv1.FStar_Syntax_Syntax.sort
                                       in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___385_5996.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___385_5996.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = uu____5997
                                    }  in
                                  let bvs1 = FStar_List.map s1 bvs  in
                                  let new_env = push_bvs e0 (bv :: bvs1)  in
                                  let new_goal =
                                    let uu___386_6005 =
                                      goal.FStar_Tactics_Types.goal_ctx_uvar
                                       in
                                    let uu____6006 =
                                      FStar_TypeChecker_Env.all_binders
                                        new_env
                                       in
                                    let uu____6015 =
                                      let uu____6018 =
                                        FStar_Tactics_Types.goal_type goal
                                         in
                                      FStar_Syntax_Subst.subst s uu____6018
                                       in
                                    {
                                      FStar_Syntax_Syntax.ctx_uvar_head =
                                        (uu___386_6005.FStar_Syntax_Syntax.ctx_uvar_head);
                                      FStar_Syntax_Syntax.ctx_uvar_gamma =
                                        (new_env.FStar_TypeChecker_Env.gamma);
                                      FStar_Syntax_Syntax.ctx_uvar_binders =
                                        uu____6006;
                                      FStar_Syntax_Syntax.ctx_uvar_typ =
                                        uu____6015;
                                      FStar_Syntax_Syntax.ctx_uvar_reason =
                                        (uu___386_6005.FStar_Syntax_Syntax.ctx_uvar_reason);
                                      FStar_Syntax_Syntax.ctx_uvar_should_check
                                        =
                                        (uu___386_6005.FStar_Syntax_Syntax.ctx_uvar_should_check);
                                      FStar_Syntax_Syntax.ctx_uvar_range =
                                        (uu___386_6005.FStar_Syntax_Syntax.ctx_uvar_range)
                                    }  in
                                  replace_cur
                                    (let uu___387_6021 = goal  in
                                     {
                                       FStar_Tactics_Types.goal_main_env =
                                         (uu___387_6021.FStar_Tactics_Types.goal_main_env);
                                       FStar_Tactics_Types.goal_ctx_uvar =
                                         new_goal;
                                       FStar_Tactics_Types.opts =
                                         (uu___387_6021.FStar_Tactics_Types.opts);
                                       FStar_Tactics_Types.is_guard =
                                         (uu___387_6021.FStar_Tactics_Types.is_guard)
                                     })
                              | uu____6022 ->
                                  fail
                                    "Not an equality hypothesis with a variable on the LHS")
                         | uu____6023 -> fail "Not an equality hypothesis")))
       in
    FStar_All.pipe_left (wrap_err "rewrite") uu____5904
  
let (rename_to : FStar_Syntax_Syntax.binder -> Prims.string -> unit tac) =
  fun b  ->
    fun s  ->
      let uu____6048 =
        let uu____6051 = cur_goal ()  in
        bind uu____6051
          (fun goal  ->
             let uu____6062 = b  in
             match uu____6062 with
             | (bv,uu____6066) ->
                 let bv' =
                   let uu____6072 =
                     let uu___388_6073 = bv  in
                     let uu____6074 =
                       FStar_Ident.mk_ident
                         (s,
                           ((bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange))
                        in
                     {
                       FStar_Syntax_Syntax.ppname = uu____6074;
                       FStar_Syntax_Syntax.index =
                         (uu___388_6073.FStar_Syntax_Syntax.index);
                       FStar_Syntax_Syntax.sort =
                         (uu___388_6073.FStar_Syntax_Syntax.sort)
                     }  in
                   FStar_Syntax_Syntax.freshen_bv uu____6072  in
                 let s1 =
                   let uu____6078 =
                     let uu____6079 =
                       let uu____6086 = FStar_Syntax_Syntax.bv_to_name bv'
                          in
                       (bv, uu____6086)  in
                     FStar_Syntax_Syntax.NT uu____6079  in
                   [uu____6078]  in
                 let uu____6091 = subst_goal bv bv' s1 goal  in
                 (match uu____6091 with
                  | FStar_Pervasives_Native.None  ->
                      fail "binder not found in environment"
                  | FStar_Pervasives_Native.Some goal1 -> replace_cur goal1))
         in
      FStar_All.pipe_left (wrap_err "rename_to") uu____6048
  
let (binder_retype : FStar_Syntax_Syntax.binder -> unit tac) =
  fun b  ->
    let uu____6110 =
      let uu____6113 = cur_goal ()  in
      bind uu____6113
        (fun goal  ->
           let uu____6122 = b  in
           match uu____6122 with
           | (bv,uu____6126) ->
               let uu____6131 =
                 let uu____6140 = FStar_Tactics_Types.goal_env goal  in
                 split_env bv uu____6140  in
               (match uu____6131 with
                | FStar_Pervasives_Native.None  ->
                    fail "binder is not present in environment"
                | FStar_Pervasives_Native.Some (e0,bvs) ->
                    let uu____6161 = FStar_Syntax_Util.type_u ()  in
                    (match uu____6161 with
                     | (ty,u) ->
                         let uu____6170 = new_uvar "binder_retype" e0 ty  in
                         bind uu____6170
                           (fun uu____6188  ->
                              match uu____6188 with
                              | (t',u_t') ->
                                  let bv'' =
                                    let uu___389_6198 = bv  in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___389_6198.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___389_6198.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = t'
                                    }  in
                                  let s =
                                    let uu____6202 =
                                      let uu____6203 =
                                        let uu____6210 =
                                          FStar_Syntax_Syntax.bv_to_name bv''
                                           in
                                        (bv, uu____6210)  in
                                      FStar_Syntax_Syntax.NT uu____6203  in
                                    [uu____6202]  in
                                  let bvs1 =
                                    FStar_List.map
                                      (fun b1  ->
                                         let uu___390_6222 = b1  in
                                         let uu____6223 =
                                           FStar_Syntax_Subst.subst s
                                             b1.FStar_Syntax_Syntax.sort
                                            in
                                         {
                                           FStar_Syntax_Syntax.ppname =
                                             (uu___390_6222.FStar_Syntax_Syntax.ppname);
                                           FStar_Syntax_Syntax.index =
                                             (uu___390_6222.FStar_Syntax_Syntax.index);
                                           FStar_Syntax_Syntax.sort =
                                             uu____6223
                                         }) bvs
                                     in
                                  let env' = push_bvs e0 (bv'' :: bvs1)  in
                                  bind __dismiss
                                    (fun uu____6230  ->
                                       let new_goal =
                                         let uu____6232 =
                                           FStar_Tactics_Types.goal_with_env
                                             goal env'
                                            in
                                         let uu____6233 =
                                           let uu____6234 =
                                             FStar_Tactics_Types.goal_type
                                               goal
                                              in
                                           FStar_Syntax_Subst.subst s
                                             uu____6234
                                            in
                                         FStar_Tactics_Types.goal_with_type
                                           uu____6232 uu____6233
                                          in
                                       let uu____6235 = add_goals [new_goal]
                                          in
                                       bind uu____6235
                                         (fun uu____6240  ->
                                            let uu____6241 =
                                              FStar_Syntax_Util.mk_eq2
                                                (FStar_Syntax_Syntax.U_succ u)
                                                ty
                                                bv.FStar_Syntax_Syntax.sort
                                                t'
                                               in
                                            add_irrelevant_goal
                                              "binder_retype equation" e0
                                              uu____6241
                                              goal.FStar_Tactics_Types.opts))))))
       in
    FStar_All.pipe_left (wrap_err "binder_retype") uu____6110
  
let (norm_binder_type :
  FStar_Syntax_Embeddings.norm_step Prims.list ->
    FStar_Syntax_Syntax.binder -> unit tac)
  =
  fun s  ->
    fun b  ->
      let uu____6264 =
        let uu____6267 = cur_goal ()  in
        bind uu____6267
          (fun goal  ->
             let uu____6276 = b  in
             match uu____6276 with
             | (bv,uu____6280) ->
                 let uu____6285 =
                   let uu____6294 = FStar_Tactics_Types.goal_env goal  in
                   split_env bv uu____6294  in
                 (match uu____6285 with
                  | FStar_Pervasives_Native.None  ->
                      fail "binder is not present in environment"
                  | FStar_Pervasives_Native.Some (e0,bvs) ->
                      let steps =
                        let uu____6318 =
                          FStar_TypeChecker_Normalize.tr_norm_steps s  in
                        FStar_List.append
                          [FStar_TypeChecker_Normalize.Reify;
                          FStar_TypeChecker_Normalize.UnfoldTac] uu____6318
                         in
                      let sort' =
                        normalize steps e0 bv.FStar_Syntax_Syntax.sort  in
                      let bv' =
                        let uu___391_6323 = bv  in
                        {
                          FStar_Syntax_Syntax.ppname =
                            (uu___391_6323.FStar_Syntax_Syntax.ppname);
                          FStar_Syntax_Syntax.index =
                            (uu___391_6323.FStar_Syntax_Syntax.index);
                          FStar_Syntax_Syntax.sort = sort'
                        }  in
                      let env' = push_bvs e0 (bv' :: bvs)  in
                      let uu____6325 =
                        FStar_Tactics_Types.goal_with_env goal env'  in
                      replace_cur uu____6325))
         in
      FStar_All.pipe_left (wrap_err "norm_binder_type") uu____6264
  
let (revert : unit -> unit tac) =
  fun uu____6336  ->
    let uu____6339 = cur_goal ()  in
    bind uu____6339
      (fun goal  ->
         let uu____6345 =
           let uu____6352 = FStar_Tactics_Types.goal_env goal  in
           FStar_TypeChecker_Env.pop_bv uu____6352  in
         match uu____6345 with
         | FStar_Pervasives_Native.None  ->
             fail "Cannot revert; empty context"
         | FStar_Pervasives_Native.Some (x,env') ->
             let typ' =
               let uu____6368 =
                 let uu____6371 = FStar_Tactics_Types.goal_type goal  in
                 FStar_Syntax_Syntax.mk_Total uu____6371  in
               FStar_Syntax_Util.arrow [(x, FStar_Pervasives_Native.None)]
                 uu____6368
                in
             let uu____6386 = new_uvar "revert" env' typ'  in
             bind uu____6386
               (fun uu____6401  ->
                  match uu____6401 with
                  | (r,u_r) ->
                      let uu____6410 =
                        let uu____6413 =
                          let uu____6414 =
                            let uu____6415 =
                              FStar_Tactics_Types.goal_type goal  in
                            uu____6415.FStar_Syntax_Syntax.pos  in
                          let uu____6418 =
                            let uu____6423 =
                              let uu____6424 =
                                let uu____6433 =
                                  FStar_Syntax_Syntax.bv_to_name x  in
                                FStar_Syntax_Syntax.as_arg uu____6433  in
                              [uu____6424]  in
                            FStar_Syntax_Syntax.mk_Tm_app r uu____6423  in
                          uu____6418 FStar_Pervasives_Native.None uu____6414
                           in
                        set_solution goal uu____6413  in
                      bind uu____6410
                        (fun uu____6454  ->
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
      let uu____6466 = FStar_Syntax_Free.names t  in
      FStar_Util.set_mem bv uu____6466
  
let rec (clear : FStar_Syntax_Syntax.binder -> unit tac) =
  fun b  ->
    let bv = FStar_Pervasives_Native.fst b  in
    let uu____6481 = cur_goal ()  in
    bind uu____6481
      (fun goal  ->
         mlog
           (fun uu____6489  ->
              let uu____6490 = FStar_Syntax_Print.binder_to_string b  in
              let uu____6491 =
                let uu____6492 =
                  let uu____6493 =
                    let uu____6502 = FStar_Tactics_Types.goal_env goal  in
                    FStar_TypeChecker_Env.all_binders uu____6502  in
                  FStar_All.pipe_right uu____6493 FStar_List.length  in
                FStar_All.pipe_right uu____6492 FStar_Util.string_of_int  in
              FStar_Util.print2 "Clear of (%s), env has %s binders\n"
                uu____6490 uu____6491)
           (fun uu____6519  ->
              let uu____6520 =
                let uu____6529 = FStar_Tactics_Types.goal_env goal  in
                split_env bv uu____6529  in
              match uu____6520 with
              | FStar_Pervasives_Native.None  ->
                  fail "Cannot clear; binder not in environment"
              | FStar_Pervasives_Native.Some (e',bvs) ->
                  let rec check1 bvs1 =
                    match bvs1 with
                    | [] -> ret ()
                    | bv'::bvs2 ->
                        let uu____6568 =
                          free_in bv bv'.FStar_Syntax_Syntax.sort  in
                        if uu____6568
                        then
                          let uu____6571 =
                            let uu____6572 =
                              FStar_Syntax_Print.bv_to_string bv'  in
                            FStar_Util.format1
                              "Cannot clear; binder present in the type of %s"
                              uu____6572
                             in
                          fail uu____6571
                        else check1 bvs2
                     in
                  let uu____6574 =
                    let uu____6575 = FStar_Tactics_Types.goal_type goal  in
                    free_in bv uu____6575  in
                  if uu____6574
                  then fail "Cannot clear; binder present in goal"
                  else
                    (let uu____6579 = check1 bvs  in
                     bind uu____6579
                       (fun uu____6585  ->
                          let env' = push_bvs e' bvs  in
                          let uu____6587 =
                            let uu____6594 =
                              FStar_Tactics_Types.goal_type goal  in
                            new_uvar "clear.witness" env' uu____6594  in
                          bind uu____6587
                            (fun uu____6603  ->
                               match uu____6603 with
                               | (ut,uvar_ut) ->
                                   let uu____6612 = set_solution goal ut  in
                                   bind uu____6612
                                     (fun uu____6617  ->
                                        let uu____6618 =
                                          FStar_Tactics_Types.mk_goal env'
                                            uvar_ut
                                            goal.FStar_Tactics_Types.opts
                                            goal.FStar_Tactics_Types.is_guard
                                           in
                                        replace_cur uu____6618))))))
  
let (clear_top : unit -> unit tac) =
  fun uu____6625  ->
    let uu____6628 = cur_goal ()  in
    bind uu____6628
      (fun goal  ->
         let uu____6634 =
           let uu____6641 = FStar_Tactics_Types.goal_env goal  in
           FStar_TypeChecker_Env.pop_bv uu____6641  in
         match uu____6634 with
         | FStar_Pervasives_Native.None  ->
             fail "Cannot clear; empty context"
         | FStar_Pervasives_Native.Some (x,uu____6649) ->
             let uu____6654 = FStar_Syntax_Syntax.mk_binder x  in
             clear uu____6654)
  
let (prune : Prims.string -> unit tac) =
  fun s  ->
    let uu____6664 = cur_goal ()  in
    bind uu____6664
      (fun g  ->
         let ctx = FStar_Tactics_Types.goal_env g  in
         let ctx' =
           let uu____6674 = FStar_Ident.path_of_text s  in
           FStar_TypeChecker_Env.rem_proof_ns ctx uu____6674  in
         let g' = FStar_Tactics_Types.goal_with_env g ctx'  in
         bind __dismiss (fun uu____6677  -> add_goals [g']))
  
let (addns : Prims.string -> unit tac) =
  fun s  ->
    let uu____6687 = cur_goal ()  in
    bind uu____6687
      (fun g  ->
         let ctx = FStar_Tactics_Types.goal_env g  in
         let ctx' =
           let uu____6697 = FStar_Ident.path_of_text s  in
           FStar_TypeChecker_Env.add_proof_ns ctx uu____6697  in
         let g' = FStar_Tactics_Types.goal_with_env g ctx'  in
         bind __dismiss (fun uu____6700  -> add_goals [g']))
  
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
            let uu____6740 = FStar_Syntax_Subst.compress t  in
            uu____6740.FStar_Syntax_Syntax.n  in
          let uu____6743 =
            if d = FStar_Tactics_Types.TopDown
            then
              f env
                (let uu___395_6749 = t  in
                 {
                   FStar_Syntax_Syntax.n = tn;
                   FStar_Syntax_Syntax.pos =
                     (uu___395_6749.FStar_Syntax_Syntax.pos);
                   FStar_Syntax_Syntax.vars =
                     (uu___395_6749.FStar_Syntax_Syntax.vars)
                 })
            else ret t  in
          bind uu____6743
            (fun t1  ->
               let ff = tac_fold_env d f env  in
               let tn1 =
                 let uu____6765 =
                   let uu____6766 = FStar_Syntax_Subst.compress t1  in
                   uu____6766.FStar_Syntax_Syntax.n  in
                 match uu____6765 with
                 | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
                     let uu____6797 = ff hd1  in
                     bind uu____6797
                       (fun hd2  ->
                          let fa uu____6823 =
                            match uu____6823 with
                            | (a,q) ->
                                let uu____6844 = ff a  in
                                bind uu____6844 (fun a1  -> ret (a1, q))
                             in
                          let uu____6863 = mapM fa args  in
                          bind uu____6863
                            (fun args1  ->
                               ret (FStar_Syntax_Syntax.Tm_app (hd2, args1))))
                 | FStar_Syntax_Syntax.Tm_abs (bs,t2,k) ->
                     let uu____6945 = FStar_Syntax_Subst.open_term bs t2  in
                     (match uu____6945 with
                      | (bs1,t') ->
                          let uu____6954 =
                            let uu____6957 =
                              FStar_TypeChecker_Env.push_binders env bs1  in
                            tac_fold_env d f uu____6957 t'  in
                          bind uu____6954
                            (fun t''  ->
                               let uu____6961 =
                                 let uu____6962 =
                                   let uu____6981 =
                                     FStar_Syntax_Subst.close_binders bs1  in
                                   let uu____6990 =
                                     FStar_Syntax_Subst.close bs1 t''  in
                                   (uu____6981, uu____6990, k)  in
                                 FStar_Syntax_Syntax.Tm_abs uu____6962  in
                               ret uu____6961))
                 | FStar_Syntax_Syntax.Tm_arrow (bs,k) -> ret tn
                 | FStar_Syntax_Syntax.Tm_match (hd1,brs) ->
                     let uu____7065 = ff hd1  in
                     bind uu____7065
                       (fun hd2  ->
                          let ffb br =
                            let uu____7080 =
                              FStar_Syntax_Subst.open_branch br  in
                            match uu____7080 with
                            | (pat,w,e) ->
                                let bvs = FStar_Syntax_Syntax.pat_bvs pat  in
                                let ff1 =
                                  let uu____7112 =
                                    FStar_TypeChecker_Env.push_bvs env bvs
                                     in
                                  tac_fold_env d f uu____7112  in
                                let uu____7113 = ff1 e  in
                                bind uu____7113
                                  (fun e1  ->
                                     let br1 =
                                       FStar_Syntax_Subst.close_branch
                                         (pat, w, e1)
                                        in
                                     ret br1)
                             in
                          let uu____7128 = mapM ffb brs  in
                          bind uu____7128
                            (fun brs1  ->
                               ret (FStar_Syntax_Syntax.Tm_match (hd2, brs1))))
                 | FStar_Syntax_Syntax.Tm_let
                     ((false
                       ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inl bv;
                          FStar_Syntax_Syntax.lbunivs = uu____7172;
                          FStar_Syntax_Syntax.lbtyp = uu____7173;
                          FStar_Syntax_Syntax.lbeff = uu____7174;
                          FStar_Syntax_Syntax.lbdef = def;
                          FStar_Syntax_Syntax.lbattrs = uu____7176;
                          FStar_Syntax_Syntax.lbpos = uu____7177;_}::[]),e)
                     ->
                     let lb =
                       let uu____7202 =
                         let uu____7203 = FStar_Syntax_Subst.compress t1  in
                         uu____7203.FStar_Syntax_Syntax.n  in
                       match uu____7202 with
                       | FStar_Syntax_Syntax.Tm_let
                           ((false ,lb::[]),uu____7207) -> lb
                       | uu____7220 -> failwith "impossible"  in
                     let fflb lb1 =
                       let uu____7229 = ff lb1.FStar_Syntax_Syntax.lbdef  in
                       bind uu____7229
                         (fun def1  ->
                            ret
                              (let uu___392_7235 = lb1  in
                               {
                                 FStar_Syntax_Syntax.lbname =
                                   (uu___392_7235.FStar_Syntax_Syntax.lbname);
                                 FStar_Syntax_Syntax.lbunivs =
                                   (uu___392_7235.FStar_Syntax_Syntax.lbunivs);
                                 FStar_Syntax_Syntax.lbtyp =
                                   (uu___392_7235.FStar_Syntax_Syntax.lbtyp);
                                 FStar_Syntax_Syntax.lbeff =
                                   (uu___392_7235.FStar_Syntax_Syntax.lbeff);
                                 FStar_Syntax_Syntax.lbdef = def1;
                                 FStar_Syntax_Syntax.lbattrs =
                                   (uu___392_7235.FStar_Syntax_Syntax.lbattrs);
                                 FStar_Syntax_Syntax.lbpos =
                                   (uu___392_7235.FStar_Syntax_Syntax.lbpos)
                               }))
                        in
                     let uu____7236 = fflb lb  in
                     bind uu____7236
                       (fun lb1  ->
                          let uu____7246 =
                            let uu____7251 =
                              let uu____7252 =
                                FStar_Syntax_Syntax.mk_binder bv  in
                              [uu____7252]  in
                            FStar_Syntax_Subst.open_term uu____7251 e  in
                          match uu____7246 with
                          | (bs,e1) ->
                              let ff1 =
                                let uu____7282 =
                                  FStar_TypeChecker_Env.push_binders env bs
                                   in
                                tac_fold_env d f uu____7282  in
                              let uu____7283 = ff1 e1  in
                              bind uu____7283
                                (fun e2  ->
                                   let e3 = FStar_Syntax_Subst.close bs e2
                                      in
                                   ret
                                     (FStar_Syntax_Syntax.Tm_let
                                        ((false, [lb1]), e3))))
                 | FStar_Syntax_Syntax.Tm_let ((true ,lbs),e) ->
                     let fflb lb =
                       let uu____7324 = ff lb.FStar_Syntax_Syntax.lbdef  in
                       bind uu____7324
                         (fun def  ->
                            ret
                              (let uu___393_7330 = lb  in
                               {
                                 FStar_Syntax_Syntax.lbname =
                                   (uu___393_7330.FStar_Syntax_Syntax.lbname);
                                 FStar_Syntax_Syntax.lbunivs =
                                   (uu___393_7330.FStar_Syntax_Syntax.lbunivs);
                                 FStar_Syntax_Syntax.lbtyp =
                                   (uu___393_7330.FStar_Syntax_Syntax.lbtyp);
                                 FStar_Syntax_Syntax.lbeff =
                                   (uu___393_7330.FStar_Syntax_Syntax.lbeff);
                                 FStar_Syntax_Syntax.lbdef = def;
                                 FStar_Syntax_Syntax.lbattrs =
                                   (uu___393_7330.FStar_Syntax_Syntax.lbattrs);
                                 FStar_Syntax_Syntax.lbpos =
                                   (uu___393_7330.FStar_Syntax_Syntax.lbpos)
                               }))
                        in
                     let uu____7331 = FStar_Syntax_Subst.open_let_rec lbs e
                        in
                     (match uu____7331 with
                      | (lbs1,e1) ->
                          let uu____7346 = mapM fflb lbs1  in
                          bind uu____7346
                            (fun lbs2  ->
                               let uu____7358 = ff e1  in
                               bind uu____7358
                                 (fun e2  ->
                                    let uu____7366 =
                                      FStar_Syntax_Subst.close_let_rec lbs2
                                        e2
                                       in
                                    match uu____7366 with
                                    | (lbs3,e3) ->
                                        ret
                                          (FStar_Syntax_Syntax.Tm_let
                                             ((true, lbs3), e3)))))
                 | FStar_Syntax_Syntax.Tm_ascribed (t2,asc,eff) ->
                     let uu____7434 = ff t2  in
                     bind uu____7434
                       (fun t3  ->
                          ret
                            (FStar_Syntax_Syntax.Tm_ascribed (t3, asc, eff)))
                 | FStar_Syntax_Syntax.Tm_meta (t2,m) ->
                     let uu____7465 = ff t2  in
                     bind uu____7465
                       (fun t3  -> ret (FStar_Syntax_Syntax.Tm_meta (t3, m)))
                 | uu____7472 -> ret tn  in
               bind tn1
                 (fun tn2  ->
                    let t' =
                      let uu___394_7479 = t1  in
                      {
                        FStar_Syntax_Syntax.n = tn2;
                        FStar_Syntax_Syntax.pos =
                          (uu___394_7479.FStar_Syntax_Syntax.pos);
                        FStar_Syntax_Syntax.vars =
                          (uu___394_7479.FStar_Syntax_Syntax.vars)
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
            let uu____7516 =
              FStar_TypeChecker_TcTerm.tc_term
                (let uu___396_7525 = env  in
                 {
                   FStar_TypeChecker_Env.solver =
                     (uu___396_7525.FStar_TypeChecker_Env.solver);
                   FStar_TypeChecker_Env.range =
                     (uu___396_7525.FStar_TypeChecker_Env.range);
                   FStar_TypeChecker_Env.curmodule =
                     (uu___396_7525.FStar_TypeChecker_Env.curmodule);
                   FStar_TypeChecker_Env.gamma =
                     (uu___396_7525.FStar_TypeChecker_Env.gamma);
                   FStar_TypeChecker_Env.gamma_sig =
                     (uu___396_7525.FStar_TypeChecker_Env.gamma_sig);
                   FStar_TypeChecker_Env.gamma_cache =
                     (uu___396_7525.FStar_TypeChecker_Env.gamma_cache);
                   FStar_TypeChecker_Env.modules =
                     (uu___396_7525.FStar_TypeChecker_Env.modules);
                   FStar_TypeChecker_Env.expected_typ =
                     (uu___396_7525.FStar_TypeChecker_Env.expected_typ);
                   FStar_TypeChecker_Env.sigtab =
                     (uu___396_7525.FStar_TypeChecker_Env.sigtab);
                   FStar_TypeChecker_Env.attrtab =
                     (uu___396_7525.FStar_TypeChecker_Env.attrtab);
                   FStar_TypeChecker_Env.is_pattern =
                     (uu___396_7525.FStar_TypeChecker_Env.is_pattern);
                   FStar_TypeChecker_Env.instantiate_imp =
                     (uu___396_7525.FStar_TypeChecker_Env.instantiate_imp);
                   FStar_TypeChecker_Env.effects =
                     (uu___396_7525.FStar_TypeChecker_Env.effects);
                   FStar_TypeChecker_Env.generalize =
                     (uu___396_7525.FStar_TypeChecker_Env.generalize);
                   FStar_TypeChecker_Env.letrecs =
                     (uu___396_7525.FStar_TypeChecker_Env.letrecs);
                   FStar_TypeChecker_Env.top_level =
                     (uu___396_7525.FStar_TypeChecker_Env.top_level);
                   FStar_TypeChecker_Env.check_uvars =
                     (uu___396_7525.FStar_TypeChecker_Env.check_uvars);
                   FStar_TypeChecker_Env.use_eq =
                     (uu___396_7525.FStar_TypeChecker_Env.use_eq);
                   FStar_TypeChecker_Env.is_iface =
                     (uu___396_7525.FStar_TypeChecker_Env.is_iface);
                   FStar_TypeChecker_Env.admit =
                     (uu___396_7525.FStar_TypeChecker_Env.admit);
                   FStar_TypeChecker_Env.lax = true;
                   FStar_TypeChecker_Env.lax_universes =
                     (uu___396_7525.FStar_TypeChecker_Env.lax_universes);
                   FStar_TypeChecker_Env.phase1 =
                     (uu___396_7525.FStar_TypeChecker_Env.phase1);
                   FStar_TypeChecker_Env.failhard =
                     (uu___396_7525.FStar_TypeChecker_Env.failhard);
                   FStar_TypeChecker_Env.nosynth =
                     (uu___396_7525.FStar_TypeChecker_Env.nosynth);
                   FStar_TypeChecker_Env.uvar_subtyping =
                     (uu___396_7525.FStar_TypeChecker_Env.uvar_subtyping);
                   FStar_TypeChecker_Env.tc_term =
                     (uu___396_7525.FStar_TypeChecker_Env.tc_term);
                   FStar_TypeChecker_Env.type_of =
                     (uu___396_7525.FStar_TypeChecker_Env.type_of);
                   FStar_TypeChecker_Env.universe_of =
                     (uu___396_7525.FStar_TypeChecker_Env.universe_of);
                   FStar_TypeChecker_Env.check_type_of =
                     (uu___396_7525.FStar_TypeChecker_Env.check_type_of);
                   FStar_TypeChecker_Env.use_bv_sorts =
                     (uu___396_7525.FStar_TypeChecker_Env.use_bv_sorts);
                   FStar_TypeChecker_Env.qtbl_name_and_index =
                     (uu___396_7525.FStar_TypeChecker_Env.qtbl_name_and_index);
                   FStar_TypeChecker_Env.normalized_eff_names =
                     (uu___396_7525.FStar_TypeChecker_Env.normalized_eff_names);
                   FStar_TypeChecker_Env.proof_ns =
                     (uu___396_7525.FStar_TypeChecker_Env.proof_ns);
                   FStar_TypeChecker_Env.synth_hook =
                     (uu___396_7525.FStar_TypeChecker_Env.synth_hook);
                   FStar_TypeChecker_Env.splice =
                     (uu___396_7525.FStar_TypeChecker_Env.splice);
                   FStar_TypeChecker_Env.is_native_tactic =
                     (uu___396_7525.FStar_TypeChecker_Env.is_native_tactic);
                   FStar_TypeChecker_Env.identifier_info =
                     (uu___396_7525.FStar_TypeChecker_Env.identifier_info);
                   FStar_TypeChecker_Env.tc_hooks =
                     (uu___396_7525.FStar_TypeChecker_Env.tc_hooks);
                   FStar_TypeChecker_Env.dsenv =
                     (uu___396_7525.FStar_TypeChecker_Env.dsenv);
                   FStar_TypeChecker_Env.dep_graph =
                     (uu___396_7525.FStar_TypeChecker_Env.dep_graph)
                 }) t
               in
            match uu____7516 with
            | (t1,lcomp,g) ->
                let uu____7531 =
                  (let uu____7534 =
                     FStar_Syntax_Util.is_pure_or_ghost_lcomp lcomp  in
                   Prims.op_Negation uu____7534) ||
                    (let uu____7536 = FStar_TypeChecker_Env.is_trivial g  in
                     Prims.op_Negation uu____7536)
                   in
                if uu____7531
                then ret t1
                else
                  (let rewrite_eq =
                     let typ = lcomp.FStar_Syntax_Syntax.res_typ  in
                     let uu____7544 = new_uvar "pointwise_rec" env typ  in
                     bind uu____7544
                       (fun uu____7560  ->
                          match uu____7560 with
                          | (ut,uvar_ut) ->
                              (log ps
                                 (fun uu____7573  ->
                                    let uu____7574 =
                                      FStar_Syntax_Print.term_to_string t1
                                       in
                                    let uu____7575 =
                                      FStar_Syntax_Print.term_to_string ut
                                       in
                                    FStar_Util.print2
                                      "Pointwise_rec: making equality\n\t%s ==\n\t%s\n"
                                      uu____7574 uu____7575);
                               (let uu____7576 =
                                  let uu____7579 =
                                    let uu____7580 =
                                      FStar_TypeChecker_TcTerm.universe_of
                                        env typ
                                       in
                                    FStar_Syntax_Util.mk_eq2 uu____7580 typ
                                      t1 ut
                                     in
                                  add_irrelevant_goal
                                    "pointwise_rec equation" env uu____7579
                                    opts
                                   in
                                bind uu____7576
                                  (fun uu____7583  ->
                                     let uu____7584 =
                                       bind tau
                                         (fun uu____7590  ->
                                            let ut1 =
                                              FStar_TypeChecker_Normalize.reduce_uvar_solutions
                                                env ut
                                               in
                                            log ps
                                              (fun uu____7596  ->
                                                 let uu____7597 =
                                                   FStar_Syntax_Print.term_to_string
                                                     t1
                                                    in
                                                 let uu____7598 =
                                                   FStar_Syntax_Print.term_to_string
                                                     ut1
                                                    in
                                                 FStar_Util.print2
                                                   "Pointwise_rec: succeeded rewriting\n\t%s to\n\t%s\n"
                                                   uu____7597 uu____7598);
                                            ret ut1)
                                        in
                                     focus uu____7584))))
                      in
                   let uu____7599 = trytac' rewrite_eq  in
                   bind uu____7599
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
          let uu____7797 = FStar_Syntax_Subst.compress t  in
          maybe_continue ctrl uu____7797
            (fun t1  ->
               let uu____7805 =
                 f env
                   (let uu___399_7814 = t1  in
                    {
                      FStar_Syntax_Syntax.n = (t1.FStar_Syntax_Syntax.n);
                      FStar_Syntax_Syntax.pos =
                        (uu___399_7814.FStar_Syntax_Syntax.pos);
                      FStar_Syntax_Syntax.vars =
                        (uu___399_7814.FStar_Syntax_Syntax.vars)
                    })
                  in
               bind uu____7805
                 (fun uu____7830  ->
                    match uu____7830 with
                    | (t2,ctrl1) ->
                        maybe_continue ctrl1 t2
                          (fun t3  ->
                             let uu____7853 =
                               let uu____7854 =
                                 FStar_Syntax_Subst.compress t3  in
                               uu____7854.FStar_Syntax_Syntax.n  in
                             match uu____7853 with
                             | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
                                 let uu____7891 =
                                   ctrl_tac_fold f env ctrl1 hd1  in
                                 bind uu____7891
                                   (fun uu____7916  ->
                                      match uu____7916 with
                                      | (hd2,ctrl2) ->
                                          let ctrl3 = keep_going ctrl2  in
                                          let uu____7932 =
                                            ctrl_tac_fold_args f env ctrl3
                                              args
                                             in
                                          bind uu____7932
                                            (fun uu____7959  ->
                                               match uu____7959 with
                                               | (args1,ctrl4) ->
                                                   ret
                                                     ((let uu___397_7989 = t3
                                                          in
                                                       {
                                                         FStar_Syntax_Syntax.n
                                                           =
                                                           (FStar_Syntax_Syntax.Tm_app
                                                              (hd2, args1));
                                                         FStar_Syntax_Syntax.pos
                                                           =
                                                           (uu___397_7989.FStar_Syntax_Syntax.pos);
                                                         FStar_Syntax_Syntax.vars
                                                           =
                                                           (uu___397_7989.FStar_Syntax_Syntax.vars)
                                                       }), ctrl4)))
                             | FStar_Syntax_Syntax.Tm_abs (bs,t4,k) ->
                                 let uu____8031 =
                                   FStar_Syntax_Subst.open_term bs t4  in
                                 (match uu____8031 with
                                  | (bs1,t') ->
                                      let uu____8046 =
                                        let uu____8053 =
                                          FStar_TypeChecker_Env.push_binders
                                            env bs1
                                           in
                                        ctrl_tac_fold f uu____8053 ctrl1 t'
                                         in
                                      bind uu____8046
                                        (fun uu____8071  ->
                                           match uu____8071 with
                                           | (t'',ctrl2) ->
                                               let uu____8086 =
                                                 let uu____8093 =
                                                   let uu___398_8096 = t4  in
                                                   let uu____8099 =
                                                     let uu____8100 =
                                                       let uu____8119 =
                                                         FStar_Syntax_Subst.close_binders
                                                           bs1
                                                          in
                                                       let uu____8128 =
                                                         FStar_Syntax_Subst.close
                                                           bs1 t''
                                                          in
                                                       (uu____8119,
                                                         uu____8128, k)
                                                        in
                                                     FStar_Syntax_Syntax.Tm_abs
                                                       uu____8100
                                                      in
                                                   {
                                                     FStar_Syntax_Syntax.n =
                                                       uu____8099;
                                                     FStar_Syntax_Syntax.pos
                                                       =
                                                       (uu___398_8096.FStar_Syntax_Syntax.pos);
                                                     FStar_Syntax_Syntax.vars
                                                       =
                                                       (uu___398_8096.FStar_Syntax_Syntax.vars)
                                                   }  in
                                                 (uu____8093, ctrl2)  in
                                               ret uu____8086))
                             | FStar_Syntax_Syntax.Tm_arrow (bs,k) ->
                                 ret (t3, ctrl1)
                             | uu____8181 -> ret (t3, ctrl1))))

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
              let uu____8228 = ctrl_tac_fold f env ctrl t  in
              bind uu____8228
                (fun uu____8252  ->
                   match uu____8252 with
                   | (t1,ctrl1) ->
                       let uu____8267 = ctrl_tac_fold_args f env ctrl1 ts1
                          in
                       bind uu____8267
                         (fun uu____8294  ->
                            match uu____8294 with
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
              let uu____8378 =
                let uu____8385 =
                  add_irrelevant_goal "dummy" env FStar_Syntax_Util.t_true
                    opts
                   in
                bind uu____8385
                  (fun uu____8394  ->
                     let uu____8395 = ctrl t1  in
                     bind uu____8395
                       (fun res  ->
                          let uu____8418 = trivial ()  in
                          bind uu____8418 (fun uu____8426  -> ret res)))
                 in
              bind uu____8378
                (fun uu____8442  ->
                   match uu____8442 with
                   | (should_rewrite,ctrl1) ->
                       if Prims.op_Negation should_rewrite
                       then ret (t1, ctrl1)
                       else
                         (let uu____8466 =
                            FStar_TypeChecker_TcTerm.tc_term
                              (let uu___400_8475 = env  in
                               {
                                 FStar_TypeChecker_Env.solver =
                                   (uu___400_8475.FStar_TypeChecker_Env.solver);
                                 FStar_TypeChecker_Env.range =
                                   (uu___400_8475.FStar_TypeChecker_Env.range);
                                 FStar_TypeChecker_Env.curmodule =
                                   (uu___400_8475.FStar_TypeChecker_Env.curmodule);
                                 FStar_TypeChecker_Env.gamma =
                                   (uu___400_8475.FStar_TypeChecker_Env.gamma);
                                 FStar_TypeChecker_Env.gamma_sig =
                                   (uu___400_8475.FStar_TypeChecker_Env.gamma_sig);
                                 FStar_TypeChecker_Env.gamma_cache =
                                   (uu___400_8475.FStar_TypeChecker_Env.gamma_cache);
                                 FStar_TypeChecker_Env.modules =
                                   (uu___400_8475.FStar_TypeChecker_Env.modules);
                                 FStar_TypeChecker_Env.expected_typ =
                                   (uu___400_8475.FStar_TypeChecker_Env.expected_typ);
                                 FStar_TypeChecker_Env.sigtab =
                                   (uu___400_8475.FStar_TypeChecker_Env.sigtab);
                                 FStar_TypeChecker_Env.attrtab =
                                   (uu___400_8475.FStar_TypeChecker_Env.attrtab);
                                 FStar_TypeChecker_Env.is_pattern =
                                   (uu___400_8475.FStar_TypeChecker_Env.is_pattern);
                                 FStar_TypeChecker_Env.instantiate_imp =
                                   (uu___400_8475.FStar_TypeChecker_Env.instantiate_imp);
                                 FStar_TypeChecker_Env.effects =
                                   (uu___400_8475.FStar_TypeChecker_Env.effects);
                                 FStar_TypeChecker_Env.generalize =
                                   (uu___400_8475.FStar_TypeChecker_Env.generalize);
                                 FStar_TypeChecker_Env.letrecs =
                                   (uu___400_8475.FStar_TypeChecker_Env.letrecs);
                                 FStar_TypeChecker_Env.top_level =
                                   (uu___400_8475.FStar_TypeChecker_Env.top_level);
                                 FStar_TypeChecker_Env.check_uvars =
                                   (uu___400_8475.FStar_TypeChecker_Env.check_uvars);
                                 FStar_TypeChecker_Env.use_eq =
                                   (uu___400_8475.FStar_TypeChecker_Env.use_eq);
                                 FStar_TypeChecker_Env.is_iface =
                                   (uu___400_8475.FStar_TypeChecker_Env.is_iface);
                                 FStar_TypeChecker_Env.admit =
                                   (uu___400_8475.FStar_TypeChecker_Env.admit);
                                 FStar_TypeChecker_Env.lax = true;
                                 FStar_TypeChecker_Env.lax_universes =
                                   (uu___400_8475.FStar_TypeChecker_Env.lax_universes);
                                 FStar_TypeChecker_Env.phase1 =
                                   (uu___400_8475.FStar_TypeChecker_Env.phase1);
                                 FStar_TypeChecker_Env.failhard =
                                   (uu___400_8475.FStar_TypeChecker_Env.failhard);
                                 FStar_TypeChecker_Env.nosynth =
                                   (uu___400_8475.FStar_TypeChecker_Env.nosynth);
                                 FStar_TypeChecker_Env.uvar_subtyping =
                                   (uu___400_8475.FStar_TypeChecker_Env.uvar_subtyping);
                                 FStar_TypeChecker_Env.tc_term =
                                   (uu___400_8475.FStar_TypeChecker_Env.tc_term);
                                 FStar_TypeChecker_Env.type_of =
                                   (uu___400_8475.FStar_TypeChecker_Env.type_of);
                                 FStar_TypeChecker_Env.universe_of =
                                   (uu___400_8475.FStar_TypeChecker_Env.universe_of);
                                 FStar_TypeChecker_Env.check_type_of =
                                   (uu___400_8475.FStar_TypeChecker_Env.check_type_of);
                                 FStar_TypeChecker_Env.use_bv_sorts =
                                   (uu___400_8475.FStar_TypeChecker_Env.use_bv_sorts);
                                 FStar_TypeChecker_Env.qtbl_name_and_index =
                                   (uu___400_8475.FStar_TypeChecker_Env.qtbl_name_and_index);
                                 FStar_TypeChecker_Env.normalized_eff_names =
                                   (uu___400_8475.FStar_TypeChecker_Env.normalized_eff_names);
                                 FStar_TypeChecker_Env.proof_ns =
                                   (uu___400_8475.FStar_TypeChecker_Env.proof_ns);
                                 FStar_TypeChecker_Env.synth_hook =
                                   (uu___400_8475.FStar_TypeChecker_Env.synth_hook);
                                 FStar_TypeChecker_Env.splice =
                                   (uu___400_8475.FStar_TypeChecker_Env.splice);
                                 FStar_TypeChecker_Env.is_native_tactic =
                                   (uu___400_8475.FStar_TypeChecker_Env.is_native_tactic);
                                 FStar_TypeChecker_Env.identifier_info =
                                   (uu___400_8475.FStar_TypeChecker_Env.identifier_info);
                                 FStar_TypeChecker_Env.tc_hooks =
                                   (uu___400_8475.FStar_TypeChecker_Env.tc_hooks);
                                 FStar_TypeChecker_Env.dsenv =
                                   (uu___400_8475.FStar_TypeChecker_Env.dsenv);
                                 FStar_TypeChecker_Env.dep_graph =
                                   (uu___400_8475.FStar_TypeChecker_Env.dep_graph)
                               }) t1
                             in
                          match uu____8466 with
                          | (t2,lcomp,g) ->
                              let uu____8485 =
                                (let uu____8488 =
                                   FStar_Syntax_Util.is_pure_or_ghost_lcomp
                                     lcomp
                                    in
                                 Prims.op_Negation uu____8488) ||
                                  (let uu____8490 =
                                     FStar_TypeChecker_Env.is_trivial g  in
                                   Prims.op_Negation uu____8490)
                                 in
                              if uu____8485
                              then ret (t2, globalStop)
                              else
                                (let typ = lcomp.FStar_Syntax_Syntax.res_typ
                                    in
                                 let uu____8503 =
                                   new_uvar "pointwise_rec" env typ  in
                                 bind uu____8503
                                   (fun uu____8523  ->
                                      match uu____8523 with
                                      | (ut,uvar_ut) ->
                                          (log ps
                                             (fun uu____8540  ->
                                                let uu____8541 =
                                                  FStar_Syntax_Print.term_to_string
                                                    t2
                                                   in
                                                let uu____8542 =
                                                  FStar_Syntax_Print.term_to_string
                                                    ut
                                                   in
                                                FStar_Util.print2
                                                  "Pointwise_rec: making equality\n\t%s ==\n\t%s\n"
                                                  uu____8541 uu____8542);
                                           (let uu____8543 =
                                              let uu____8546 =
                                                let uu____8547 =
                                                  FStar_TypeChecker_TcTerm.universe_of
                                                    env typ
                                                   in
                                                FStar_Syntax_Util.mk_eq2
                                                  uu____8547 typ t2 ut
                                                 in
                                              add_irrelevant_goal
                                                "rewrite_rec equation" env
                                                uu____8546 opts
                                               in
                                            bind uu____8543
                                              (fun uu____8554  ->
                                                 let uu____8555 =
                                                   bind rewriter
                                                     (fun uu____8569  ->
                                                        let ut1 =
                                                          FStar_TypeChecker_Normalize.reduce_uvar_solutions
                                                            env ut
                                                           in
                                                        log ps
                                                          (fun uu____8575  ->
                                                             let uu____8576 =
                                                               FStar_Syntax_Print.term_to_string
                                                                 t2
                                                                in
                                                             let uu____8577 =
                                                               FStar_Syntax_Print.term_to_string
                                                                 ut1
                                                                in
                                                             FStar_Util.print2
                                                               "rewrite_rec: succeeded rewriting\n\t%s to\n\t%s\n"
                                                               uu____8576
                                                               uu____8577);
                                                        ret (ut1, ctrl1))
                                                    in
                                                 focus uu____8555)))))))
  
let (topdown_rewrite :
  (FStar_Syntax_Syntax.term ->
     (Prims.bool,FStar_BigInt.t) FStar_Pervasives_Native.tuple2 tac)
    -> unit tac -> unit tac)
  =
  fun ctrl  ->
    fun rewriter  ->
      let uu____8618 =
        bind get
          (fun ps  ->
             let uu____8628 =
               match ps.FStar_Tactics_Types.goals with
               | g::gs -> (g, gs)
               | [] -> failwith "no goals"  in
             match uu____8628 with
             | (g,gs) ->
                 let gt1 = FStar_Tactics_Types.goal_type g  in
                 (log ps
                    (fun uu____8665  ->
                       let uu____8666 = FStar_Syntax_Print.term_to_string gt1
                          in
                       FStar_Util.print1 "Topdown_rewrite starting with %s\n"
                         uu____8666);
                  bind dismiss_all
                    (fun uu____8669  ->
                       let uu____8670 =
                         let uu____8677 = FStar_Tactics_Types.goal_env g  in
                         ctrl_tac_fold
                           (rewrite_rec ps ctrl rewriter
                              g.FStar_Tactics_Types.opts) uu____8677
                           keepGoing gt1
                          in
                       bind uu____8670
                         (fun uu____8689  ->
                            match uu____8689 with
                            | (gt',uu____8697) ->
                                (log ps
                                   (fun uu____8701  ->
                                      let uu____8702 =
                                        FStar_Syntax_Print.term_to_string gt'
                                         in
                                      FStar_Util.print1
                                        "Topdown_rewrite seems to have succeded with %s\n"
                                        uu____8702);
                                 (let uu____8703 = push_goals gs  in
                                  bind uu____8703
                                    (fun uu____8708  ->
                                       let uu____8709 =
                                         let uu____8712 =
                                           FStar_Tactics_Types.goal_with_type
                                             g gt'
                                            in
                                         [uu____8712]  in
                                       add_goals uu____8709)))))))
         in
      FStar_All.pipe_left (wrap_err "topdown_rewrite") uu____8618
  
let (pointwise : FStar_Tactics_Types.direction -> unit tac -> unit tac) =
  fun d  ->
    fun tau  ->
      let uu____8735 =
        bind get
          (fun ps  ->
             let uu____8745 =
               match ps.FStar_Tactics_Types.goals with
               | g::gs -> (g, gs)
               | [] -> failwith "no goals"  in
             match uu____8745 with
             | (g,gs) ->
                 let gt1 = FStar_Tactics_Types.goal_type g  in
                 (log ps
                    (fun uu____8782  ->
                       let uu____8783 = FStar_Syntax_Print.term_to_string gt1
                          in
                       FStar_Util.print1 "Pointwise starting with %s\n"
                         uu____8783);
                  bind dismiss_all
                    (fun uu____8786  ->
                       let uu____8787 =
                         let uu____8790 = FStar_Tactics_Types.goal_env g  in
                         tac_fold_env d
                           (pointwise_rec ps tau g.FStar_Tactics_Types.opts)
                           uu____8790 gt1
                          in
                       bind uu____8787
                         (fun gt'  ->
                            log ps
                              (fun uu____8798  ->
                                 let uu____8799 =
                                   FStar_Syntax_Print.term_to_string gt'  in
                                 FStar_Util.print1
                                   "Pointwise seems to have succeded with %s\n"
                                   uu____8799);
                            (let uu____8800 = push_goals gs  in
                             bind uu____8800
                               (fun uu____8805  ->
                                  let uu____8806 =
                                    let uu____8809 =
                                      FStar_Tactics_Types.goal_with_type g
                                        gt'
                                       in
                                    [uu____8809]  in
                                  add_goals uu____8806))))))
         in
      FStar_All.pipe_left (wrap_err "pointwise") uu____8735
  
let (trefl : unit -> unit tac) =
  fun uu____8820  ->
    let uu____8823 =
      let uu____8826 = cur_goal ()  in
      bind uu____8826
        (fun g  ->
           let uu____8844 =
             let uu____8849 = FStar_Tactics_Types.goal_type g  in
             FStar_Syntax_Util.un_squash uu____8849  in
           match uu____8844 with
           | FStar_Pervasives_Native.Some t ->
               let uu____8857 = FStar_Syntax_Util.head_and_args' t  in
               (match uu____8857 with
                | (hd1,args) ->
                    let uu____8896 =
                      let uu____8909 =
                        let uu____8910 = FStar_Syntax_Util.un_uinst hd1  in
                        uu____8910.FStar_Syntax_Syntax.n  in
                      (uu____8909, args)  in
                    (match uu____8896 with
                     | (FStar_Syntax_Syntax.Tm_fvar
                        fv,uu____8924::(l,uu____8926)::(r,uu____8928)::[])
                         when
                         FStar_Syntax_Syntax.fv_eq_lid fv
                           FStar_Parser_Const.eq2_lid
                         ->
                         let uu____8975 =
                           let uu____8978 = FStar_Tactics_Types.goal_env g
                              in
                           do_unify uu____8978 l r  in
                         bind uu____8975
                           (fun b  ->
                              if b
                              then solve' g FStar_Syntax_Util.exp_unit
                              else
                                (let l1 =
                                   let uu____8985 =
                                     FStar_Tactics_Types.goal_env g  in
                                   FStar_TypeChecker_Normalize.normalize
                                     [FStar_TypeChecker_Normalize.UnfoldUntil
                                        FStar_Syntax_Syntax.delta_constant;
                                     FStar_TypeChecker_Normalize.Primops;
                                     FStar_TypeChecker_Normalize.UnfoldTac]
                                     uu____8985 l
                                    in
                                 let r1 =
                                   let uu____8987 =
                                     FStar_Tactics_Types.goal_env g  in
                                   FStar_TypeChecker_Normalize.normalize
                                     [FStar_TypeChecker_Normalize.UnfoldUntil
                                        FStar_Syntax_Syntax.delta_constant;
                                     FStar_TypeChecker_Normalize.Primops;
                                     FStar_TypeChecker_Normalize.UnfoldTac]
                                     uu____8987 r
                                    in
                                 let uu____8988 =
                                   let uu____8991 =
                                     FStar_Tactics_Types.goal_env g  in
                                   do_unify uu____8991 l1 r1  in
                                 bind uu____8988
                                   (fun b1  ->
                                      if b1
                                      then
                                        solve' g FStar_Syntax_Util.exp_unit
                                      else
                                        (let uu____8997 =
                                           let uu____8998 =
                                             FStar_Tactics_Types.goal_env g
                                              in
                                           tts uu____8998 l1  in
                                         let uu____8999 =
                                           let uu____9000 =
                                             FStar_Tactics_Types.goal_env g
                                              in
                                           tts uu____9000 r1  in
                                         fail2
                                           "not a trivial equality ((%s) vs (%s))"
                                           uu____8997 uu____8999))))
                     | (hd2,uu____9002) ->
                         let uu____9019 =
                           let uu____9020 = FStar_Tactics_Types.goal_env g
                              in
                           tts uu____9020 t  in
                         fail1 "trefl: not an equality (%s)" uu____9019))
           | FStar_Pervasives_Native.None  -> fail "not an irrelevant goal")
       in
    FStar_All.pipe_left (wrap_err "trefl") uu____8823
  
let (dup : unit -> unit tac) =
  fun uu____9033  ->
    let uu____9036 = cur_goal ()  in
    bind uu____9036
      (fun g  ->
         let uu____9042 =
           let uu____9049 = FStar_Tactics_Types.goal_env g  in
           let uu____9050 = FStar_Tactics_Types.goal_type g  in
           new_uvar "dup" uu____9049 uu____9050  in
         bind uu____9042
           (fun uu____9059  ->
              match uu____9059 with
              | (u,u_uvar) ->
                  let g' =
                    let uu___401_9069 = g  in
                    {
                      FStar_Tactics_Types.goal_main_env =
                        (uu___401_9069.FStar_Tactics_Types.goal_main_env);
                      FStar_Tactics_Types.goal_ctx_uvar = u_uvar;
                      FStar_Tactics_Types.opts =
                        (uu___401_9069.FStar_Tactics_Types.opts);
                      FStar_Tactics_Types.is_guard =
                        (uu___401_9069.FStar_Tactics_Types.is_guard)
                    }  in
                  bind __dismiss
                    (fun uu____9072  ->
                       let uu____9073 =
                         let uu____9076 = FStar_Tactics_Types.goal_env g  in
                         let uu____9077 =
                           let uu____9078 =
                             let uu____9079 = FStar_Tactics_Types.goal_env g
                                in
                             let uu____9080 = FStar_Tactics_Types.goal_type g
                                in
                             FStar_TypeChecker_TcTerm.universe_of uu____9079
                               uu____9080
                              in
                           let uu____9081 = FStar_Tactics_Types.goal_type g
                              in
                           let uu____9082 =
                             FStar_Tactics_Types.goal_witness g  in
                           FStar_Syntax_Util.mk_eq2 uu____9078 uu____9081 u
                             uu____9082
                            in
                         add_irrelevant_goal "dup equation" uu____9076
                           uu____9077 g.FStar_Tactics_Types.opts
                          in
                       bind uu____9073
                         (fun uu____9085  ->
                            let uu____9086 = add_goals [g']  in
                            bind uu____9086 (fun uu____9090  -> ret ())))))
  
let (flip : unit -> unit tac) =
  fun uu____9097  ->
    bind get
      (fun ps  ->
         match ps.FStar_Tactics_Types.goals with
         | g1::g2::gs ->
             set
               (let uu___402_9114 = ps  in
                {
                  FStar_Tactics_Types.main_context =
                    (uu___402_9114.FStar_Tactics_Types.main_context);
                  FStar_Tactics_Types.main_goal =
                    (uu___402_9114.FStar_Tactics_Types.main_goal);
                  FStar_Tactics_Types.all_implicits =
                    (uu___402_9114.FStar_Tactics_Types.all_implicits);
                  FStar_Tactics_Types.goals = (g2 :: g1 :: gs);
                  FStar_Tactics_Types.smt_goals =
                    (uu___402_9114.FStar_Tactics_Types.smt_goals);
                  FStar_Tactics_Types.depth =
                    (uu___402_9114.FStar_Tactics_Types.depth);
                  FStar_Tactics_Types.__dump =
                    (uu___402_9114.FStar_Tactics_Types.__dump);
                  FStar_Tactics_Types.psc =
                    (uu___402_9114.FStar_Tactics_Types.psc);
                  FStar_Tactics_Types.entry_range =
                    (uu___402_9114.FStar_Tactics_Types.entry_range);
                  FStar_Tactics_Types.guard_policy =
                    (uu___402_9114.FStar_Tactics_Types.guard_policy);
                  FStar_Tactics_Types.freshness =
                    (uu___402_9114.FStar_Tactics_Types.freshness);
                  FStar_Tactics_Types.tac_verb_dbg =
                    (uu___402_9114.FStar_Tactics_Types.tac_verb_dbg)
                })
         | uu____9115 -> fail "flip: less than 2 goals")
  
let (later : unit -> unit tac) =
  fun uu____9124  ->
    bind get
      (fun ps  ->
         match ps.FStar_Tactics_Types.goals with
         | [] -> ret ()
         | g::gs ->
             set
               (let uu___403_9137 = ps  in
                {
                  FStar_Tactics_Types.main_context =
                    (uu___403_9137.FStar_Tactics_Types.main_context);
                  FStar_Tactics_Types.main_goal =
                    (uu___403_9137.FStar_Tactics_Types.main_goal);
                  FStar_Tactics_Types.all_implicits =
                    (uu___403_9137.FStar_Tactics_Types.all_implicits);
                  FStar_Tactics_Types.goals = (FStar_List.append gs [g]);
                  FStar_Tactics_Types.smt_goals =
                    (uu___403_9137.FStar_Tactics_Types.smt_goals);
                  FStar_Tactics_Types.depth =
                    (uu___403_9137.FStar_Tactics_Types.depth);
                  FStar_Tactics_Types.__dump =
                    (uu___403_9137.FStar_Tactics_Types.__dump);
                  FStar_Tactics_Types.psc =
                    (uu___403_9137.FStar_Tactics_Types.psc);
                  FStar_Tactics_Types.entry_range =
                    (uu___403_9137.FStar_Tactics_Types.entry_range);
                  FStar_Tactics_Types.guard_policy =
                    (uu___403_9137.FStar_Tactics_Types.guard_policy);
                  FStar_Tactics_Types.freshness =
                    (uu___403_9137.FStar_Tactics_Types.freshness);
                  FStar_Tactics_Types.tac_verb_dbg =
                    (uu___403_9137.FStar_Tactics_Types.tac_verb_dbg)
                }))
  
let (qed : unit -> unit tac) =
  fun uu____9144  ->
    bind get
      (fun ps  ->
         match ps.FStar_Tactics_Types.goals with
         | [] -> ret ()
         | uu____9151 -> fail "Not done!")
  
let (cases :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 tac)
  =
  fun t  ->
    let uu____9171 =
      let uu____9178 = cur_goal ()  in
      bind uu____9178
        (fun g  ->
           let uu____9188 =
             let uu____9197 = FStar_Tactics_Types.goal_env g  in
             __tc uu____9197 t  in
           bind uu____9188
             (fun uu____9225  ->
                match uu____9225 with
                | (t1,typ,guard) ->
                    let uu____9241 = FStar_Syntax_Util.head_and_args typ  in
                    (match uu____9241 with
                     | (hd1,args) ->
                         let uu____9290 =
                           let uu____9305 =
                             let uu____9306 = FStar_Syntax_Util.un_uinst hd1
                                in
                             uu____9306.FStar_Syntax_Syntax.n  in
                           (uu____9305, args)  in
                         (match uu____9290 with
                          | (FStar_Syntax_Syntax.Tm_fvar
                             fv,(p,uu____9327)::(q,uu____9329)::[]) when
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
                                let uu____9383 =
                                  let uu____9384 =
                                    FStar_Tactics_Types.goal_env g  in
                                  FStar_TypeChecker_Env.push_bv uu____9384
                                    v_p
                                   in
                                FStar_Tactics_Types.goal_with_env g
                                  uu____9383
                                 in
                              let g2 =
                                let uu____9386 =
                                  let uu____9387 =
                                    FStar_Tactics_Types.goal_env g  in
                                  FStar_TypeChecker_Env.push_bv uu____9387
                                    v_q
                                   in
                                FStar_Tactics_Types.goal_with_env g
                                  uu____9386
                                 in
                              bind __dismiss
                                (fun uu____9394  ->
                                   let uu____9395 = add_goals [g1; g2]  in
                                   bind uu____9395
                                     (fun uu____9404  ->
                                        let uu____9405 =
                                          let uu____9410 =
                                            FStar_Syntax_Syntax.bv_to_name
                                              v_p
                                             in
                                          let uu____9411 =
                                            FStar_Syntax_Syntax.bv_to_name
                                              v_q
                                             in
                                          (uu____9410, uu____9411)  in
                                        ret uu____9405))
                          | uu____9416 ->
                              let uu____9431 =
                                let uu____9432 =
                                  FStar_Tactics_Types.goal_env g  in
                                tts uu____9432 typ  in
                              fail1 "Not a disjunction: %s" uu____9431))))
       in
    FStar_All.pipe_left (wrap_err "cases") uu____9171
  
let (set_options : Prims.string -> unit tac) =
  fun s  ->
    let uu____9462 =
      let uu____9465 = cur_goal ()  in
      bind uu____9465
        (fun g  ->
           FStar_Options.push ();
           (let uu____9478 = FStar_Util.smap_copy g.FStar_Tactics_Types.opts
               in
            FStar_Options.set uu____9478);
           (let res = FStar_Options.set_options FStar_Options.Set s  in
            let opts' = FStar_Options.peek ()  in
            FStar_Options.pop ();
            (match res with
             | FStar_Getopt.Success  ->
                 let g' =
                   let uu___404_9485 = g  in
                   {
                     FStar_Tactics_Types.goal_main_env =
                       (uu___404_9485.FStar_Tactics_Types.goal_main_env);
                     FStar_Tactics_Types.goal_ctx_uvar =
                       (uu___404_9485.FStar_Tactics_Types.goal_ctx_uvar);
                     FStar_Tactics_Types.opts = opts';
                     FStar_Tactics_Types.is_guard =
                       (uu___404_9485.FStar_Tactics_Types.is_guard)
                   }  in
                 replace_cur g'
             | FStar_Getopt.Error err ->
                 fail2 "Setting options `%s` failed: %s" s err
             | FStar_Getopt.Help  ->
                 fail1 "Setting options `%s` failed (got `Help`?)" s)))
       in
    FStar_All.pipe_left (wrap_err "set_options") uu____9462
  
let (top_env : unit -> env tac) =
  fun uu____9497  ->
    bind get
      (fun ps  -> FStar_All.pipe_left ret ps.FStar_Tactics_Types.main_context)
  
let (cur_env : unit -> env tac) =
  fun uu____9510  ->
    let uu____9513 = cur_goal ()  in
    bind uu____9513
      (fun g  ->
         let uu____9519 = FStar_Tactics_Types.goal_env g  in
         FStar_All.pipe_left ret uu____9519)
  
let (cur_goal' : unit -> FStar_Syntax_Syntax.term tac) =
  fun uu____9528  ->
    let uu____9531 = cur_goal ()  in
    bind uu____9531
      (fun g  ->
         let uu____9537 = FStar_Tactics_Types.goal_type g  in
         FStar_All.pipe_left ret uu____9537)
  
let (cur_witness : unit -> FStar_Syntax_Syntax.term tac) =
  fun uu____9546  ->
    let uu____9549 = cur_goal ()  in
    bind uu____9549
      (fun g  ->
         let uu____9555 = FStar_Tactics_Types.goal_witness g  in
         FStar_All.pipe_left ret uu____9555)
  
let (lax_on : unit -> Prims.bool tac) =
  fun uu____9564  ->
    let uu____9567 = cur_env ()  in
    bind uu____9567
      (fun e  ->
         let uu____9573 =
           (FStar_Options.lax ()) || e.FStar_TypeChecker_Env.lax  in
         ret uu____9573)
  
let (unquote :
  FStar_Reflection_Data.typ ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term tac)
  =
  fun ty  ->
    fun tm  ->
      let uu____9588 =
        mlog
          (fun uu____9593  ->
             let uu____9594 = FStar_Syntax_Print.term_to_string tm  in
             FStar_Util.print1 "unquote: tm = %s\n" uu____9594)
          (fun uu____9597  ->
             let uu____9598 = cur_goal ()  in
             bind uu____9598
               (fun goal  ->
                  let env =
                    let uu____9606 = FStar_Tactics_Types.goal_env goal  in
                    FStar_TypeChecker_Env.set_expected_typ uu____9606 ty  in
                  let uu____9607 = __tc env tm  in
                  bind uu____9607
                    (fun uu____9626  ->
                       match uu____9626 with
                       | (tm1,typ,guard) ->
                           mlog
                             (fun uu____9640  ->
                                let uu____9641 =
                                  FStar_Syntax_Print.term_to_string tm1  in
                                FStar_Util.print1 "unquote: tm' = %s\n"
                                  uu____9641)
                             (fun uu____9643  ->
                                mlog
                                  (fun uu____9646  ->
                                     let uu____9647 =
                                       FStar_Syntax_Print.term_to_string typ
                                        in
                                     FStar_Util.print1 "unquote: typ = %s\n"
                                       uu____9647)
                                  (fun uu____9650  ->
                                     let uu____9651 =
                                       proc_guard "unquote" env guard  in
                                     bind uu____9651
                                       (fun uu____9655  -> ret tm1))))))
         in
      FStar_All.pipe_left (wrap_err "unquote") uu____9588
  
let (uvar_env :
  env ->
    FStar_Reflection_Data.typ FStar_Pervasives_Native.option ->
      FStar_Syntax_Syntax.term tac)
  =
  fun env  ->
    fun ty  ->
      let uu____9678 =
        match ty with
        | FStar_Pervasives_Native.Some ty1 -> ret ty1
        | FStar_Pervasives_Native.None  ->
            let uu____9684 =
              let uu____9691 =
                let uu____9692 = FStar_Syntax_Util.type_u ()  in
                FStar_All.pipe_left FStar_Pervasives_Native.fst uu____9692
                 in
              new_uvar "uvar_env.2" env uu____9691  in
            bind uu____9684
              (fun uu____9708  ->
                 match uu____9708 with | (typ,uvar_typ) -> ret typ)
         in
      bind uu____9678
        (fun typ  ->
           let uu____9720 = new_uvar "uvar_env" env typ  in
           bind uu____9720
             (fun uu____9734  -> match uu____9734 with | (t,uvar_t) -> ret t))
  
let (unshelve : FStar_Syntax_Syntax.term -> unit tac) =
  fun t  ->
    let uu____9752 =
      bind get
        (fun ps  ->
           let env = ps.FStar_Tactics_Types.main_context  in
           let opts =
             match ps.FStar_Tactics_Types.goals with
             | g::uu____9771 -> g.FStar_Tactics_Types.opts
             | uu____9774 -> FStar_Options.peek ()  in
           let uu____9777 = FStar_Syntax_Util.head_and_args t  in
           match uu____9777 with
           | ({
                FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                  (ctx_uvar,uu____9797);
                FStar_Syntax_Syntax.pos = uu____9798;
                FStar_Syntax_Syntax.vars = uu____9799;_},uu____9800)
               ->
               let env1 =
                 let uu___405_9842 = env  in
                 {
                   FStar_TypeChecker_Env.solver =
                     (uu___405_9842.FStar_TypeChecker_Env.solver);
                   FStar_TypeChecker_Env.range =
                     (uu___405_9842.FStar_TypeChecker_Env.range);
                   FStar_TypeChecker_Env.curmodule =
                     (uu___405_9842.FStar_TypeChecker_Env.curmodule);
                   FStar_TypeChecker_Env.gamma =
                     (ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_gamma);
                   FStar_TypeChecker_Env.gamma_sig =
                     (uu___405_9842.FStar_TypeChecker_Env.gamma_sig);
                   FStar_TypeChecker_Env.gamma_cache =
                     (uu___405_9842.FStar_TypeChecker_Env.gamma_cache);
                   FStar_TypeChecker_Env.modules =
                     (uu___405_9842.FStar_TypeChecker_Env.modules);
                   FStar_TypeChecker_Env.expected_typ =
                     (uu___405_9842.FStar_TypeChecker_Env.expected_typ);
                   FStar_TypeChecker_Env.sigtab =
                     (uu___405_9842.FStar_TypeChecker_Env.sigtab);
                   FStar_TypeChecker_Env.attrtab =
                     (uu___405_9842.FStar_TypeChecker_Env.attrtab);
                   FStar_TypeChecker_Env.is_pattern =
                     (uu___405_9842.FStar_TypeChecker_Env.is_pattern);
                   FStar_TypeChecker_Env.instantiate_imp =
                     (uu___405_9842.FStar_TypeChecker_Env.instantiate_imp);
                   FStar_TypeChecker_Env.effects =
                     (uu___405_9842.FStar_TypeChecker_Env.effects);
                   FStar_TypeChecker_Env.generalize =
                     (uu___405_9842.FStar_TypeChecker_Env.generalize);
                   FStar_TypeChecker_Env.letrecs =
                     (uu___405_9842.FStar_TypeChecker_Env.letrecs);
                   FStar_TypeChecker_Env.top_level =
                     (uu___405_9842.FStar_TypeChecker_Env.top_level);
                   FStar_TypeChecker_Env.check_uvars =
                     (uu___405_9842.FStar_TypeChecker_Env.check_uvars);
                   FStar_TypeChecker_Env.use_eq =
                     (uu___405_9842.FStar_TypeChecker_Env.use_eq);
                   FStar_TypeChecker_Env.is_iface =
                     (uu___405_9842.FStar_TypeChecker_Env.is_iface);
                   FStar_TypeChecker_Env.admit =
                     (uu___405_9842.FStar_TypeChecker_Env.admit);
                   FStar_TypeChecker_Env.lax =
                     (uu___405_9842.FStar_TypeChecker_Env.lax);
                   FStar_TypeChecker_Env.lax_universes =
                     (uu___405_9842.FStar_TypeChecker_Env.lax_universes);
                   FStar_TypeChecker_Env.phase1 =
                     (uu___405_9842.FStar_TypeChecker_Env.phase1);
                   FStar_TypeChecker_Env.failhard =
                     (uu___405_9842.FStar_TypeChecker_Env.failhard);
                   FStar_TypeChecker_Env.nosynth =
                     (uu___405_9842.FStar_TypeChecker_Env.nosynth);
                   FStar_TypeChecker_Env.uvar_subtyping =
                     (uu___405_9842.FStar_TypeChecker_Env.uvar_subtyping);
                   FStar_TypeChecker_Env.tc_term =
                     (uu___405_9842.FStar_TypeChecker_Env.tc_term);
                   FStar_TypeChecker_Env.type_of =
                     (uu___405_9842.FStar_TypeChecker_Env.type_of);
                   FStar_TypeChecker_Env.universe_of =
                     (uu___405_9842.FStar_TypeChecker_Env.universe_of);
                   FStar_TypeChecker_Env.check_type_of =
                     (uu___405_9842.FStar_TypeChecker_Env.check_type_of);
                   FStar_TypeChecker_Env.use_bv_sorts =
                     (uu___405_9842.FStar_TypeChecker_Env.use_bv_sorts);
                   FStar_TypeChecker_Env.qtbl_name_and_index =
                     (uu___405_9842.FStar_TypeChecker_Env.qtbl_name_and_index);
                   FStar_TypeChecker_Env.normalized_eff_names =
                     (uu___405_9842.FStar_TypeChecker_Env.normalized_eff_names);
                   FStar_TypeChecker_Env.proof_ns =
                     (uu___405_9842.FStar_TypeChecker_Env.proof_ns);
                   FStar_TypeChecker_Env.synth_hook =
                     (uu___405_9842.FStar_TypeChecker_Env.synth_hook);
                   FStar_TypeChecker_Env.splice =
                     (uu___405_9842.FStar_TypeChecker_Env.splice);
                   FStar_TypeChecker_Env.is_native_tactic =
                     (uu___405_9842.FStar_TypeChecker_Env.is_native_tactic);
                   FStar_TypeChecker_Env.identifier_info =
                     (uu___405_9842.FStar_TypeChecker_Env.identifier_info);
                   FStar_TypeChecker_Env.tc_hooks =
                     (uu___405_9842.FStar_TypeChecker_Env.tc_hooks);
                   FStar_TypeChecker_Env.dsenv =
                     (uu___405_9842.FStar_TypeChecker_Env.dsenv);
                   FStar_TypeChecker_Env.dep_graph =
                     (uu___405_9842.FStar_TypeChecker_Env.dep_graph)
                 }  in
               let g = FStar_Tactics_Types.mk_goal env1 ctx_uvar opts false
                  in
               let uu____9844 =
                 let uu____9847 = bnorm_goal g  in [uu____9847]  in
               add_goals uu____9844
           | uu____9848 -> fail "not a uvar")
       in
    FStar_All.pipe_left (wrap_err "unshelve") uu____9752
  
let (tac_and : Prims.bool tac -> Prims.bool tac -> Prims.bool tac) =
  fun t1  ->
    fun t2  ->
      let comp =
        bind t1
          (fun b  ->
             let uu____9897 = if b then t2 else ret false  in
             bind uu____9897 (fun b'  -> if b' then ret b' else fail ""))
         in
      let uu____9908 = trytac comp  in
      bind uu____9908
        (fun uu___342_9916  ->
           match uu___342_9916 with
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
        let uu____9942 =
          bind get
            (fun ps  ->
               let uu____9948 = __tc e t1  in
               bind uu____9948
                 (fun uu____9968  ->
                    match uu____9968 with
                    | (t11,ty1,g1) ->
                        let uu____9980 = __tc e t2  in
                        bind uu____9980
                          (fun uu____10000  ->
                             match uu____10000 with
                             | (t21,ty2,g2) ->
                                 let uu____10012 =
                                   proc_guard "unify_env g1" e g1  in
                                 bind uu____10012
                                   (fun uu____10017  ->
                                      let uu____10018 =
                                        proc_guard "unify_env g2" e g2  in
                                      bind uu____10018
                                        (fun uu____10024  ->
                                           let uu____10025 =
                                             do_unify e ty1 ty2  in
                                           let uu____10028 =
                                             do_unify e t11 t21  in
                                           tac_and uu____10025 uu____10028)))))
           in
        FStar_All.pipe_left (wrap_err "unify_env") uu____9942
  
let (launch_process :
  Prims.string -> Prims.string Prims.list -> Prims.string -> Prims.string tac)
  =
  fun prog  ->
    fun args  ->
      fun input  ->
        bind idtac
          (fun uu____10061  ->
             let uu____10062 = FStar_Options.unsafe_tactic_exec ()  in
             if uu____10062
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
        (fun uu____10083  ->
           let uu____10084 =
             FStar_Syntax_Syntax.gen_bv nm FStar_Pervasives_Native.None t  in
           ret uu____10084)
  
let (change : FStar_Reflection_Data.typ -> unit tac) =
  fun ty  ->
    let uu____10094 =
      mlog
        (fun uu____10099  ->
           let uu____10100 = FStar_Syntax_Print.term_to_string ty  in
           FStar_Util.print1 "change: ty = %s\n" uu____10100)
        (fun uu____10103  ->
           let uu____10104 = cur_goal ()  in
           bind uu____10104
             (fun g  ->
                let uu____10110 =
                  let uu____10119 = FStar_Tactics_Types.goal_env g  in
                  __tc uu____10119 ty  in
                bind uu____10110
                  (fun uu____10131  ->
                     match uu____10131 with
                     | (ty1,uu____10141,guard) ->
                         let uu____10143 =
                           let uu____10146 = FStar_Tactics_Types.goal_env g
                              in
                           proc_guard "change" uu____10146 guard  in
                         bind uu____10143
                           (fun uu____10149  ->
                              let uu____10150 =
                                let uu____10153 =
                                  FStar_Tactics_Types.goal_env g  in
                                let uu____10154 =
                                  FStar_Tactics_Types.goal_type g  in
                                do_unify uu____10153 uu____10154 ty1  in
                              bind uu____10150
                                (fun bb  ->
                                   if bb
                                   then
                                     let uu____10160 =
                                       FStar_Tactics_Types.goal_with_type g
                                         ty1
                                        in
                                     replace_cur uu____10160
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
                                        let uu____10166 =
                                          FStar_Tactics_Types.goal_env g  in
                                        let uu____10167 =
                                          FStar_Tactics_Types.goal_type g  in
                                        normalize steps uu____10166
                                          uu____10167
                                         in
                                      let nty =
                                        let uu____10169 =
                                          FStar_Tactics_Types.goal_env g  in
                                        normalize steps uu____10169 ty1  in
                                      let uu____10170 =
                                        let uu____10173 =
                                          FStar_Tactics_Types.goal_env g  in
                                        do_unify uu____10173 ng nty  in
                                      bind uu____10170
                                        (fun b  ->
                                           if b
                                           then
                                             let uu____10179 =
                                               FStar_Tactics_Types.goal_with_type
                                                 g ty1
                                                in
                                             replace_cur uu____10179
                                           else fail "not convertible")))))))
       in
    FStar_All.pipe_left (wrap_err "change") uu____10094
  
let failwhen : 'a . Prims.bool -> Prims.string -> (unit -> 'a tac) -> 'a tac
  = fun b  -> fun msg  -> fun k  -> if b then fail msg else k () 
let (t_destruct :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.fv,FStar_BigInt.t) FStar_Pervasives_Native.tuple2
      Prims.list tac)
  =
  fun s_tm  ->
    let uu____10242 =
      let uu____10251 = cur_goal ()  in
      bind uu____10251
        (fun g  ->
           let uu____10263 =
             let uu____10272 = FStar_Tactics_Types.goal_env g  in
             __tc uu____10272 s_tm  in
           bind uu____10263
             (fun uu____10290  ->
                match uu____10290 with
                | (s_tm1,s_ty,guard) ->
                    let uu____10308 =
                      let uu____10311 = FStar_Tactics_Types.goal_env g  in
                      proc_guard "destruct" uu____10311 guard  in
                    bind uu____10308
                      (fun uu____10323  ->
                         let uu____10324 =
                           FStar_Syntax_Util.head_and_args' s_ty  in
                         match uu____10324 with
                         | (h,args) ->
                             let uu____10369 =
                               let uu____10376 =
                                 let uu____10377 =
                                   FStar_Syntax_Subst.compress h  in
                                 uu____10377.FStar_Syntax_Syntax.n  in
                               match uu____10376 with
                               | FStar_Syntax_Syntax.Tm_fvar fv ->
                                   ret (fv, [])
                               | FStar_Syntax_Syntax.Tm_uinst
                                   ({
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.Tm_fvar fv;
                                      FStar_Syntax_Syntax.pos = uu____10392;
                                      FStar_Syntax_Syntax.vars = uu____10393;_},us)
                                   -> ret (fv, us)
                               | uu____10403 -> fail "type is not an fv"  in
                             bind uu____10369
                               (fun uu____10423  ->
                                  match uu____10423 with
                                  | (fv,a_us) ->
                                      let t_lid =
                                        FStar_Syntax_Syntax.lid_of_fv fv  in
                                      let uu____10439 =
                                        let uu____10442 =
                                          FStar_Tactics_Types.goal_env g  in
                                        FStar_TypeChecker_Env.lookup_sigelt
                                          uu____10442 t_lid
                                         in
                                      (match uu____10439 with
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
                                                  (fun uu____10491  ->
                                                     let uu____10492 =
                                                       FStar_Syntax_Subst.open_term
                                                         t_ps t_ty
                                                        in
                                                     match uu____10492 with
                                                     | (t_ps1,t_ty1) ->
                                                         let uu____10507 =
                                                           mapM
                                                             (fun c_lid  ->
                                                                let uu____10535
                                                                  =
                                                                  let uu____10538
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    g  in
                                                                  FStar_TypeChecker_Env.lookup_sigelt
                                                                    uu____10538
                                                                    c_lid
                                                                   in
                                                                match uu____10535
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
                                                                    uu____10608
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
                                                                    let uu____10613
                                                                    =
                                                                    FStar_TypeChecker_Env.inst_tscheme
                                                                    (c_us,
                                                                    c_ty1)
                                                                     in
                                                                    match uu____10613
                                                                    with
                                                                    | 
                                                                    (c_us1,c_ty2)
                                                                    ->
                                                                    let uu____10636
                                                                    =
                                                                    FStar_Syntax_Util.arrow_formals_comp
                                                                    c_ty2  in
                                                                    (match uu____10636
                                                                    with
                                                                    | 
                                                                    (bs,comp)
                                                                    ->
                                                                    let uu____10679
                                                                    =
                                                                    FStar_List.splitAt
                                                                    nparam bs
                                                                     in
                                                                    (match uu____10679
                                                                    with
                                                                    | 
                                                                    (d_ps,bs1)
                                                                    ->
                                                                    let uu____10752
                                                                    =
                                                                    let uu____10753
                                                                    =
                                                                    FStar_Syntax_Util.is_total_comp
                                                                    comp  in
                                                                    Prims.op_Negation
                                                                    uu____10753
                                                                     in
                                                                    failwhen
                                                                    uu____10752
                                                                    "not total?"
                                                                    (fun
                                                                    uu____10770
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
                                                                    uu___343_10786
                                                                    =
                                                                    match uu___343_10786
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    (FStar_Syntax_Syntax.Implicit
                                                                    uu____10789)
                                                                    -> true
                                                                    | 
                                                                    uu____10790
                                                                    -> false
                                                                     in
                                                                    let uu____10793
                                                                    =
                                                                    FStar_List.splitAt
                                                                    nparam
                                                                    args  in
                                                                    match uu____10793
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
                                                                    uu____10926
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
                                                                    uu____10988
                                                                     ->
                                                                    match uu____10988
                                                                    with
                                                                    | 
                                                                    ((bv,uu____11008),
                                                                    (t,uu____11010))
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
                                                                    uu____11078
                                                                     ->
                                                                    match uu____11078
                                                                    with
                                                                    | 
                                                                    ((bv,uu____11104),
                                                                    (t,uu____11106))
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
                                                                    uu____11161
                                                                     ->
                                                                    match uu____11161
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
                                                                    let uu____11211
                                                                    =
                                                                    FStar_TypeChecker_TcTerm.tc_pat
                                                                    (let uu___406_11228
                                                                    = env  in
                                                                    {
                                                                    FStar_TypeChecker_Env.solver
                                                                    =
                                                                    (uu___406_11228.FStar_TypeChecker_Env.solver);
                                                                    FStar_TypeChecker_Env.range
                                                                    =
                                                                    (uu___406_11228.FStar_TypeChecker_Env.range);
                                                                    FStar_TypeChecker_Env.curmodule
                                                                    =
                                                                    (uu___406_11228.FStar_TypeChecker_Env.curmodule);
                                                                    FStar_TypeChecker_Env.gamma
                                                                    =
                                                                    (uu___406_11228.FStar_TypeChecker_Env.gamma);
                                                                    FStar_TypeChecker_Env.gamma_sig
                                                                    =
                                                                    (uu___406_11228.FStar_TypeChecker_Env.gamma_sig);
                                                                    FStar_TypeChecker_Env.gamma_cache
                                                                    =
                                                                    (uu___406_11228.FStar_TypeChecker_Env.gamma_cache);
                                                                    FStar_TypeChecker_Env.modules
                                                                    =
                                                                    (uu___406_11228.FStar_TypeChecker_Env.modules);
                                                                    FStar_TypeChecker_Env.expected_typ
                                                                    =
                                                                    (uu___406_11228.FStar_TypeChecker_Env.expected_typ);
                                                                    FStar_TypeChecker_Env.sigtab
                                                                    =
                                                                    (uu___406_11228.FStar_TypeChecker_Env.sigtab);
                                                                    FStar_TypeChecker_Env.attrtab
                                                                    =
                                                                    (uu___406_11228.FStar_TypeChecker_Env.attrtab);
                                                                    FStar_TypeChecker_Env.is_pattern
                                                                    =
                                                                    (uu___406_11228.FStar_TypeChecker_Env.is_pattern);
                                                                    FStar_TypeChecker_Env.instantiate_imp
                                                                    =
                                                                    (uu___406_11228.FStar_TypeChecker_Env.instantiate_imp);
                                                                    FStar_TypeChecker_Env.effects
                                                                    =
                                                                    (uu___406_11228.FStar_TypeChecker_Env.effects);
                                                                    FStar_TypeChecker_Env.generalize
                                                                    =
                                                                    (uu___406_11228.FStar_TypeChecker_Env.generalize);
                                                                    FStar_TypeChecker_Env.letrecs
                                                                    =
                                                                    (uu___406_11228.FStar_TypeChecker_Env.letrecs);
                                                                    FStar_TypeChecker_Env.top_level
                                                                    =
                                                                    (uu___406_11228.FStar_TypeChecker_Env.top_level);
                                                                    FStar_TypeChecker_Env.check_uvars
                                                                    =
                                                                    (uu___406_11228.FStar_TypeChecker_Env.check_uvars);
                                                                    FStar_TypeChecker_Env.use_eq
                                                                    =
                                                                    (uu___406_11228.FStar_TypeChecker_Env.use_eq);
                                                                    FStar_TypeChecker_Env.is_iface
                                                                    =
                                                                    (uu___406_11228.FStar_TypeChecker_Env.is_iface);
                                                                    FStar_TypeChecker_Env.admit
                                                                    =
                                                                    (uu___406_11228.FStar_TypeChecker_Env.admit);
                                                                    FStar_TypeChecker_Env.lax
                                                                    = true;
                                                                    FStar_TypeChecker_Env.lax_universes
                                                                    =
                                                                    (uu___406_11228.FStar_TypeChecker_Env.lax_universes);
                                                                    FStar_TypeChecker_Env.phase1
                                                                    =
                                                                    (uu___406_11228.FStar_TypeChecker_Env.phase1);
                                                                    FStar_TypeChecker_Env.failhard
                                                                    =
                                                                    (uu___406_11228.FStar_TypeChecker_Env.failhard);
                                                                    FStar_TypeChecker_Env.nosynth
                                                                    =
                                                                    (uu___406_11228.FStar_TypeChecker_Env.nosynth);
                                                                    FStar_TypeChecker_Env.uvar_subtyping
                                                                    =
                                                                    (uu___406_11228.FStar_TypeChecker_Env.uvar_subtyping);
                                                                    FStar_TypeChecker_Env.tc_term
                                                                    =
                                                                    (uu___406_11228.FStar_TypeChecker_Env.tc_term);
                                                                    FStar_TypeChecker_Env.type_of
                                                                    =
                                                                    (uu___406_11228.FStar_TypeChecker_Env.type_of);
                                                                    FStar_TypeChecker_Env.universe_of
                                                                    =
                                                                    (uu___406_11228.FStar_TypeChecker_Env.universe_of);
                                                                    FStar_TypeChecker_Env.check_type_of
                                                                    =
                                                                    (uu___406_11228.FStar_TypeChecker_Env.check_type_of);
                                                                    FStar_TypeChecker_Env.use_bv_sorts
                                                                    =
                                                                    (uu___406_11228.FStar_TypeChecker_Env.use_bv_sorts);
                                                                    FStar_TypeChecker_Env.qtbl_name_and_index
                                                                    =
                                                                    (uu___406_11228.FStar_TypeChecker_Env.qtbl_name_and_index);
                                                                    FStar_TypeChecker_Env.normalized_eff_names
                                                                    =
                                                                    (uu___406_11228.FStar_TypeChecker_Env.normalized_eff_names);
                                                                    FStar_TypeChecker_Env.proof_ns
                                                                    =
                                                                    (uu___406_11228.FStar_TypeChecker_Env.proof_ns);
                                                                    FStar_TypeChecker_Env.synth_hook
                                                                    =
                                                                    (uu___406_11228.FStar_TypeChecker_Env.synth_hook);
                                                                    FStar_TypeChecker_Env.splice
                                                                    =
                                                                    (uu___406_11228.FStar_TypeChecker_Env.splice);
                                                                    FStar_TypeChecker_Env.is_native_tactic
                                                                    =
                                                                    (uu___406_11228.FStar_TypeChecker_Env.is_native_tactic);
                                                                    FStar_TypeChecker_Env.identifier_info
                                                                    =
                                                                    (uu___406_11228.FStar_TypeChecker_Env.identifier_info);
                                                                    FStar_TypeChecker_Env.tc_hooks
                                                                    =
                                                                    (uu___406_11228.FStar_TypeChecker_Env.tc_hooks);
                                                                    FStar_TypeChecker_Env.dsenv
                                                                    =
                                                                    (uu___406_11228.FStar_TypeChecker_Env.dsenv);
                                                                    FStar_TypeChecker_Env.dep_graph
                                                                    =
                                                                    (uu___406_11228.FStar_TypeChecker_Env.dep_graph)
                                                                    }) true
                                                                    s_ty pat
                                                                     in
                                                                    match uu____11211
                                                                    with
                                                                    | 
                                                                    (uu____11241,uu____11242,uu____11243,pat_t,uu____11245,uu____11246)
                                                                    ->
                                                                    let eq_b
                                                                    =
                                                                    let uu____11252
                                                                    =
                                                                    let uu____11253
                                                                    =
                                                                    FStar_Syntax_Util.mk_eq2
                                                                    equ s_ty
                                                                    s_tm1
                                                                    pat_t  in
                                                                    FStar_Syntax_Util.mk_squash
                                                                    equ
                                                                    uu____11253
                                                                     in
                                                                    FStar_Syntax_Syntax.gen_bv
                                                                    "breq"
                                                                    FStar_Pervasives_Native.None
                                                                    uu____11252
                                                                     in
                                                                    let cod1
                                                                    =
                                                                    let uu____11257
                                                                    =
                                                                    let uu____11266
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_binder
                                                                    eq_b  in
                                                                    [uu____11266]
                                                                     in
                                                                    let uu____11285
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Total
                                                                    cod  in
                                                                    FStar_Syntax_Util.arrow
                                                                    uu____11257
                                                                    uu____11285
                                                                     in
                                                                    let nty =
                                                                    let uu____11291
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Total
                                                                    cod1  in
                                                                    FStar_Syntax_Util.arrow
                                                                    bs2
                                                                    uu____11291
                                                                     in
                                                                    let uu____11294
                                                                    =
                                                                    new_uvar
                                                                    "destruct branch"
                                                                    env nty
                                                                     in
                                                                    bind
                                                                    uu____11294
                                                                    (fun
                                                                    uu____11323
                                                                     ->
                                                                    match uu____11323
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
                                                                    let uu____11349
                                                                    =
                                                                    let uu____11360
                                                                    =
                                                                    FStar_Syntax_Syntax.as_arg
                                                                    FStar_Syntax_Util.exp_unit
                                                                     in
                                                                    [uu____11360]
                                                                     in
                                                                    FStar_Syntax_Util.mk_app
                                                                    brt
                                                                    uu____11349
                                                                     in
                                                                    let br =
                                                                    FStar_Syntax_Subst.close_branch
                                                                    (pat,
                                                                    FStar_Pervasives_Native.None,
                                                                    brt1)  in
                                                                    let uu____11396
                                                                    =
                                                                    let uu____11407
                                                                    =
                                                                    let uu____11412
                                                                    =
                                                                    FStar_BigInt.of_int_fs
                                                                    (FStar_List.length
                                                                    bs2)  in
                                                                    (fv1,
                                                                    uu____11412)
                                                                     in
                                                                    (g', br,
                                                                    uu____11407)
                                                                     in
                                                                    ret
                                                                    uu____11396))))))
                                                                    | 
                                                                    uu____11433
                                                                    ->
                                                                    fail
                                                                    "impossible: not a ctor"))
                                                             c_lids
                                                            in
                                                         bind uu____10507
                                                           (fun goal_brs  ->
                                                              let uu____11482
                                                                =
                                                                FStar_List.unzip3
                                                                  goal_brs
                                                                 in
                                                              match uu____11482
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
                                                                  let uu____11555
                                                                    =
                                                                    solve' g
                                                                    w  in
                                                                  bind
                                                                    uu____11555
                                                                    (
                                                                    fun
                                                                    uu____11566
                                                                     ->
                                                                    let uu____11567
                                                                    =
                                                                    add_goals
                                                                    goals  in
                                                                    bind
                                                                    uu____11567
                                                                    (fun
                                                                    uu____11577
                                                                     ->
                                                                    ret infos))))
                                            | uu____11584 ->
                                                fail "not an inductive type"))))))
       in
    FStar_All.pipe_left (wrap_err "destruct") uu____10242
  
let rec last : 'a . 'a Prims.list -> 'a =
  fun l  ->
    match l with
    | [] -> failwith "last: empty list"
    | x::[] -> x
    | uu____11629::xs -> last xs
  
let rec init : 'a . 'a Prims.list -> 'a Prims.list =
  fun l  ->
    match l with
    | [] -> failwith "init: empty list"
    | x::[] -> []
    | x::xs -> let uu____11657 = init xs  in x :: uu____11657
  
let rec (inspect :
  FStar_Syntax_Syntax.term -> FStar_Reflection_Data.term_view tac) =
  fun t  ->
    let uu____11669 =
      let t1 = FStar_Syntax_Util.unascribe t  in
      let t2 = FStar_Syntax_Util.un_uinst t1  in
      match t2.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_meta (t3,uu____11677) -> inspect t3
      | FStar_Syntax_Syntax.Tm_name bv ->
          FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_Var bv)
      | FStar_Syntax_Syntax.Tm_bvar bv ->
          FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_BVar bv)
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_FVar fv)
      | FStar_Syntax_Syntax.Tm_app (hd1,[]) ->
          failwith "empty arguments on Tm_app"
      | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
          let uu____11742 = last args  in
          (match uu____11742 with
           | (a,q) ->
               let q' = FStar_Reflection_Basic.inspect_aqual q  in
               let uu____11772 =
                 let uu____11773 =
                   let uu____11778 =
                     let uu____11779 =
                       let uu____11784 = init args  in
                       FStar_Syntax_Syntax.mk_Tm_app hd1 uu____11784  in
                     uu____11779 FStar_Pervasives_Native.None
                       t2.FStar_Syntax_Syntax.pos
                      in
                   (uu____11778, (a, q'))  in
                 FStar_Reflection_Data.Tv_App uu____11773  in
               FStar_All.pipe_left ret uu____11772)
      | FStar_Syntax_Syntax.Tm_abs ([],uu____11797,uu____11798) ->
          failwith "empty arguments on Tm_abs"
      | FStar_Syntax_Syntax.Tm_abs (bs,t3,k) ->
          let uu____11850 = FStar_Syntax_Subst.open_term bs t3  in
          (match uu____11850 with
           | (bs1,t4) ->
               (match bs1 with
                | [] -> failwith "impossible"
                | b::bs2 ->
                    let uu____11891 =
                      let uu____11892 =
                        let uu____11897 = FStar_Syntax_Util.abs bs2 t4 k  in
                        (b, uu____11897)  in
                      FStar_Reflection_Data.Tv_Abs uu____11892  in
                    FStar_All.pipe_left ret uu____11891))
      | FStar_Syntax_Syntax.Tm_type uu____11900 ->
          FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_Type ())
      | FStar_Syntax_Syntax.Tm_arrow ([],k) ->
          failwith "empty binders on arrow"
      | FStar_Syntax_Syntax.Tm_arrow uu____11924 ->
          let uu____11939 = FStar_Syntax_Util.arrow_one t2  in
          (match uu____11939 with
           | FStar_Pervasives_Native.Some (b,c) ->
               FStar_All.pipe_left ret
                 (FStar_Reflection_Data.Tv_Arrow (b, c))
           | FStar_Pervasives_Native.None  -> failwith "impossible")
      | FStar_Syntax_Syntax.Tm_refine (bv,t3) ->
          let b = FStar_Syntax_Syntax.mk_binder bv  in
          let uu____11969 = FStar_Syntax_Subst.open_term [b] t3  in
          (match uu____11969 with
           | (b',t4) ->
               let b1 =
                 match b' with
                 | b'1::[] -> b'1
                 | uu____12022 -> failwith "impossible"  in
               FStar_All.pipe_left ret
                 (FStar_Reflection_Data.Tv_Refine
                    ((FStar_Pervasives_Native.fst b1), t4)))
      | FStar_Syntax_Syntax.Tm_constant c ->
          let uu____12034 =
            let uu____12035 = FStar_Reflection_Basic.inspect_const c  in
            FStar_Reflection_Data.Tv_Const uu____12035  in
          FStar_All.pipe_left ret uu____12034
      | FStar_Syntax_Syntax.Tm_uvar (ctx_u,s) ->
          let uu____12056 =
            let uu____12057 =
              let uu____12062 =
                let uu____12063 =
                  FStar_Syntax_Unionfind.uvar_id
                    ctx_u.FStar_Syntax_Syntax.ctx_uvar_head
                   in
                FStar_BigInt.of_int_fs uu____12063  in
              (uu____12062, (ctx_u, s))  in
            FStar_Reflection_Data.Tv_Uvar uu____12057  in
          FStar_All.pipe_left ret uu____12056
      | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),t21) ->
          if lb.FStar_Syntax_Syntax.lbunivs <> []
          then FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown
          else
            (match lb.FStar_Syntax_Syntax.lbname with
             | FStar_Util.Inr uu____12097 ->
                 FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown
             | FStar_Util.Inl bv ->
                 let b = FStar_Syntax_Syntax.mk_binder bv  in
                 let uu____12102 = FStar_Syntax_Subst.open_term [b] t21  in
                 (match uu____12102 with
                  | (bs,t22) ->
                      let b1 =
                        match bs with
                        | b1::[] -> b1
                        | uu____12155 ->
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
             | FStar_Util.Inr uu____12189 ->
                 FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown
             | FStar_Util.Inl bv ->
                 let uu____12193 = FStar_Syntax_Subst.open_let_rec [lb] t21
                    in
                 (match uu____12193 with
                  | (lbs,t22) ->
                      (match lbs with
                       | lb1::[] ->
                           (match lb1.FStar_Syntax_Syntax.lbname with
                            | FStar_Util.Inr uu____12213 ->
                                ret FStar_Reflection_Data.Tv_Unknown
                            | FStar_Util.Inl bv1 ->
                                FStar_All.pipe_left ret
                                  (FStar_Reflection_Data.Tv_Let
                                     (true, bv1,
                                       (lb1.FStar_Syntax_Syntax.lbdef), t22)))
                       | uu____12217 ->
                           failwith
                             "impossible: open_term returned different amount of binders")))
      | FStar_Syntax_Syntax.Tm_match (t3,brs) ->
          let rec inspect_pat p =
            match p.FStar_Syntax_Syntax.v with
            | FStar_Syntax_Syntax.Pat_constant c ->
                let uu____12271 = FStar_Reflection_Basic.inspect_const c  in
                FStar_Reflection_Data.Pat_Constant uu____12271
            | FStar_Syntax_Syntax.Pat_cons (fv,ps) ->
                let uu____12290 =
                  let uu____12297 =
                    FStar_List.map
                      (fun uu____12309  ->
                         match uu____12309 with
                         | (p1,uu____12317) -> inspect_pat p1) ps
                     in
                  (fv, uu____12297)  in
                FStar_Reflection_Data.Pat_Cons uu____12290
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
              (fun uu___344_12411  ->
                 match uu___344_12411 with
                 | (pat,uu____12433,t4) ->
                     let uu____12451 = inspect_pat pat  in (uu____12451, t4))
              brs1
             in
          FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_Match (t3, brs2))
      | FStar_Syntax_Syntax.Tm_unknown  ->
          FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown
      | uu____12460 ->
          ((let uu____12462 =
              let uu____12467 =
                let uu____12468 = FStar_Syntax_Print.tag_of_term t2  in
                let uu____12469 = FStar_Syntax_Print.term_to_string t2  in
                FStar_Util.format2
                  "inspect: outside of expected syntax (%s, %s)\n"
                  uu____12468 uu____12469
                 in
              (FStar_Errors.Warning_CantInspect, uu____12467)  in
            FStar_Errors.log_issue t2.FStar_Syntax_Syntax.pos uu____12462);
           FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown)
       in
    wrap_err "inspect" uu____11669
  
let (pack : FStar_Reflection_Data.term_view -> FStar_Syntax_Syntax.term tac)
  =
  fun tv  ->
    match tv with
    | FStar_Reflection_Data.Tv_Var bv ->
        let uu____12482 = FStar_Syntax_Syntax.bv_to_name bv  in
        FStar_All.pipe_left ret uu____12482
    | FStar_Reflection_Data.Tv_BVar bv ->
        let uu____12486 = FStar_Syntax_Syntax.bv_to_tm bv  in
        FStar_All.pipe_left ret uu____12486
    | FStar_Reflection_Data.Tv_FVar fv ->
        let uu____12490 = FStar_Syntax_Syntax.fv_to_tm fv  in
        FStar_All.pipe_left ret uu____12490
    | FStar_Reflection_Data.Tv_App (l,(r,q)) ->
        let q' = FStar_Reflection_Basic.pack_aqual q  in
        let uu____12497 = FStar_Syntax_Util.mk_app l [(r, q')]  in
        FStar_All.pipe_left ret uu____12497
    | FStar_Reflection_Data.Tv_Abs (b,t) ->
        let uu____12522 =
          FStar_Syntax_Util.abs [b] t FStar_Pervasives_Native.None  in
        FStar_All.pipe_left ret uu____12522
    | FStar_Reflection_Data.Tv_Arrow (b,c) ->
        let uu____12539 = FStar_Syntax_Util.arrow [b] c  in
        FStar_All.pipe_left ret uu____12539
    | FStar_Reflection_Data.Tv_Type () ->
        FStar_All.pipe_left ret FStar_Syntax_Util.ktype
    | FStar_Reflection_Data.Tv_Refine (bv,t) ->
        let uu____12558 = FStar_Syntax_Util.refine bv t  in
        FStar_All.pipe_left ret uu____12558
    | FStar_Reflection_Data.Tv_Const c ->
        let uu____12562 =
          let uu____12563 =
            let uu____12570 =
              let uu____12571 = FStar_Reflection_Basic.pack_const c  in
              FStar_Syntax_Syntax.Tm_constant uu____12571  in
            FStar_Syntax_Syntax.mk uu____12570  in
          uu____12563 FStar_Pervasives_Native.None FStar_Range.dummyRange  in
        FStar_All.pipe_left ret uu____12562
    | FStar_Reflection_Data.Tv_Uvar (_u,ctx_u_s) ->
        let uu____12579 =
          FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_uvar ctx_u_s)
            FStar_Pervasives_Native.None FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____12579
    | FStar_Reflection_Data.Tv_Let (false ,bv,t1,t2) ->
        let lb =
          FStar_Syntax_Util.mk_letbinding (FStar_Util.Inl bv) []
            bv.FStar_Syntax_Syntax.sort FStar_Parser_Const.effect_Tot_lid t1
            [] FStar_Range.dummyRange
           in
        let uu____12588 =
          let uu____12589 =
            let uu____12596 =
              let uu____12597 =
                let uu____12610 =
                  let uu____12613 =
                    let uu____12614 = FStar_Syntax_Syntax.mk_binder bv  in
                    [uu____12614]  in
                  FStar_Syntax_Subst.close uu____12613 t2  in
                ((false, [lb]), uu____12610)  in
              FStar_Syntax_Syntax.Tm_let uu____12597  in
            FStar_Syntax_Syntax.mk uu____12596  in
          uu____12589 FStar_Pervasives_Native.None FStar_Range.dummyRange  in
        FStar_All.pipe_left ret uu____12588
    | FStar_Reflection_Data.Tv_Let (true ,bv,t1,t2) ->
        let lb =
          FStar_Syntax_Util.mk_letbinding (FStar_Util.Inl bv) []
            bv.FStar_Syntax_Syntax.sort FStar_Parser_Const.effect_Tot_lid t1
            [] FStar_Range.dummyRange
           in
        let uu____12654 = FStar_Syntax_Subst.close_let_rec [lb] t2  in
        (match uu____12654 with
         | (lbs,body) ->
             let uu____12669 =
               FStar_Syntax_Syntax.mk
                 (FStar_Syntax_Syntax.Tm_let ((true, lbs), body))
                 FStar_Pervasives_Native.None FStar_Range.dummyRange
                in
             FStar_All.pipe_left ret uu____12669)
    | FStar_Reflection_Data.Tv_Match (t,brs) ->
        let wrap v1 =
          {
            FStar_Syntax_Syntax.v = v1;
            FStar_Syntax_Syntax.p = FStar_Range.dummyRange
          }  in
        let rec pack_pat p =
          match p with
          | FStar_Reflection_Data.Pat_Constant c ->
              let uu____12703 =
                let uu____12704 = FStar_Reflection_Basic.pack_const c  in
                FStar_Syntax_Syntax.Pat_constant uu____12704  in
              FStar_All.pipe_left wrap uu____12703
          | FStar_Reflection_Data.Pat_Cons (fv,ps) ->
              let uu____12711 =
                let uu____12712 =
                  let uu____12725 =
                    FStar_List.map
                      (fun p1  ->
                         let uu____12741 = pack_pat p1  in
                         (uu____12741, false)) ps
                     in
                  (fv, uu____12725)  in
                FStar_Syntax_Syntax.Pat_cons uu____12712  in
              FStar_All.pipe_left wrap uu____12711
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
            (fun uu___345_12787  ->
               match uu___345_12787 with
               | (pat,t1) ->
                   let uu____12804 = pack_pat pat  in
                   (uu____12804, FStar_Pervasives_Native.None, t1)) brs
           in
        let brs2 = FStar_List.map FStar_Syntax_Subst.close_branch brs1  in
        let uu____12852 =
          FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_match (t, brs2))
            FStar_Pervasives_Native.None FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____12852
    | FStar_Reflection_Data.Tv_AscribedT (e,t,tacopt) ->
        let uu____12880 =
          FStar_Syntax_Syntax.mk
            (FStar_Syntax_Syntax.Tm_ascribed
               (e, ((FStar_Util.Inl t), tacopt),
                 FStar_Pervasives_Native.None)) FStar_Pervasives_Native.None
            FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____12880
    | FStar_Reflection_Data.Tv_AscribedC (e,c,tacopt) ->
        let uu____12926 =
          FStar_Syntax_Syntax.mk
            (FStar_Syntax_Syntax.Tm_ascribed
               (e, ((FStar_Util.Inr c), tacopt),
                 FStar_Pervasives_Native.None)) FStar_Pervasives_Native.None
            FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____12926
    | FStar_Reflection_Data.Tv_Unknown  ->
        let uu____12965 =
          FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown
            FStar_Pervasives_Native.None FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____12965
  
let (goal_of_goal_ty :
  env ->
    FStar_Reflection_Data.typ ->
      (FStar_Tactics_Types.goal,FStar_TypeChecker_Env.guard_t)
        FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun typ  ->
      let uu____12986 =
        FStar_TypeChecker_Util.new_implicit_var "proofstate_of_goal_ty"
          typ.FStar_Syntax_Syntax.pos env typ
         in
      match uu____12986 with
      | (u,ctx_uvars,g_u) ->
          let uu____13018 = FStar_List.hd ctx_uvars  in
          (match uu____13018 with
           | (ctx_uvar,uu____13032) ->
               let g =
                 let uu____13034 = FStar_Options.peek ()  in
                 FStar_Tactics_Types.mk_goal env ctx_uvar uu____13034 false
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
        let uu____13054 = goal_of_goal_ty env typ  in
        match uu____13054 with
        | (g,g_u) ->
            let ps =
              let uu____13066 =
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
                FStar_Tactics_Types.tac_verb_dbg = uu____13066
              }  in
            let uu____13071 = FStar_Tactics_Types.goal_witness g  in
            (ps, uu____13071)
  