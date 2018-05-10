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
      | e ->
          let uu____168 =
            let uu____173 = FStar_Util.message_of_exn e  in (uu____173, p)
             in
          FStar_Tactics_Result.Failed uu____168
  
let (tac_verb_dbg : Prims.bool FStar_Pervasives_Native.option FStar_ST.ref) =
  FStar_Util.mk_ref FStar_Pervasives_Native.None 
let rec (log : FStar_Tactics_Types.proofstate -> (unit -> unit) -> unit) =
  fun ps  ->
    fun f  ->
      let uu____206 = FStar_ST.op_Bang tac_verb_dbg  in
      match uu____206 with
      | FStar_Pervasives_Native.None  ->
          ((let uu____237 =
              let uu____240 =
                FStar_TypeChecker_Env.debug
                  ps.FStar_Tactics_Types.main_context
                  (FStar_Options.Other "TacVerbose")
                 in
              FStar_Pervasives_Native.Some uu____240  in
            FStar_ST.op_Colon_Equals tac_verb_dbg uu____237);
           log ps f)
      | FStar_Pervasives_Native.Some (true ) -> f ()
      | FStar_Pervasives_Native.Some (false ) -> ()
  
let ret : 'a . 'a -> 'a tac =
  fun x  -> mk_tac (fun p  -> FStar_Tactics_Result.Success (x, p)) 
let bind : 'a 'b . 'a tac -> ('a -> 'b tac) -> 'b tac =
  fun t1  ->
    fun t2  ->
      mk_tac
        (fun p  ->
           let uu____323 = run t1 p  in
           match uu____323 with
           | FStar_Tactics_Result.Success (a,q) ->
               let uu____330 = t2 a  in run uu____330 q
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
    let uu____350 =
      FStar_Syntax_Unionfind.find uv.FStar_Syntax_Syntax.ctx_uvar_head  in
    match uu____350 with
    | FStar_Pervasives_Native.Some t -> FStar_Pervasives_Native.Some t
    | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
  
let (check_goal_solved :
  FStar_Tactics_Types.goal ->
    FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  = fun goal  -> get_uvar_solved goal.FStar_Tactics_Types.goal_ctx_uvar 
let (goal_to_string_verbose : FStar_Tactics_Types.goal -> Prims.string) =
  fun g  ->
    let uu____368 =
      FStar_Syntax_Print.ctx_uvar_to_string
        g.FStar_Tactics_Types.goal_ctx_uvar
       in
    let uu____369 =
      let uu____370 = check_goal_solved g  in
      match uu____370 with
      | FStar_Pervasives_Native.None  -> ""
      | FStar_Pervasives_Native.Some t ->
          let uu____374 = FStar_Syntax_Print.term_to_string t  in
          FStar_Util.format1 "\tGOAL ALREADY SOLVED!: %s" uu____374
       in
    FStar_Util.format2 "%s%s" uu____368 uu____369
  
let (goal_to_string : FStar_Tactics_Types.goal -> Prims.string) =
  fun g  ->
    let uu____380 =
      (FStar_Options.print_implicits ()) ||
        (let uu____382 = FStar_ST.op_Bang tac_verb_dbg  in
         uu____382 = (FStar_Pervasives_Native.Some true))
       in
    if uu____380
    then goal_to_string_verbose g
    else
      (let w =
         let uu____416 = get_uvar_solved g.FStar_Tactics_Types.goal_ctx_uvar
            in
         match uu____416 with
         | FStar_Pervasives_Native.None  -> "_"
         | FStar_Pervasives_Native.Some t ->
             FStar_Syntax_Print.term_to_string t
          in
       let uu____420 =
         FStar_Syntax_Print.binders_to_string ", "
           (g.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_binders
          in
       let uu____421 =
         FStar_Syntax_Print.term_to_string
           (g.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_typ
          in
       FStar_Util.format3 "%s |- %s : %s" uu____420 w uu____421)
  
let (tacprint : Prims.string -> unit) =
  fun s  -> FStar_Util.print1 "TAC>> %s\n" s 
let (tacprint1 : Prims.string -> Prims.string -> unit) =
  fun s  ->
    fun x  ->
      let uu____437 = FStar_Util.format1 s x  in
      FStar_Util.print1 "TAC>> %s\n" uu____437
  
let (tacprint2 : Prims.string -> Prims.string -> Prims.string -> unit) =
  fun s  ->
    fun x  ->
      fun y  ->
        let uu____453 = FStar_Util.format2 s x y  in
        FStar_Util.print1 "TAC>> %s\n" uu____453
  
let (tacprint3 :
  Prims.string -> Prims.string -> Prims.string -> Prims.string -> unit) =
  fun s  ->
    fun x  ->
      fun y  ->
        fun z  ->
          let uu____474 = FStar_Util.format3 s x y z  in
          FStar_Util.print1 "TAC>> %s\n" uu____474
  
let (comp_to_typ : FStar_Syntax_Syntax.comp -> FStar_Reflection_Data.typ) =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Total (t,uu____481) -> t
    | FStar_Syntax_Syntax.GTotal (t,uu____491) -> t
    | FStar_Syntax_Syntax.Comp ct -> ct.FStar_Syntax_Syntax.result_typ
  
let (is_irrelevant : FStar_Tactics_Types.goal -> Prims.bool) =
  fun g  ->
    let uu____506 =
      let uu____511 =
        let uu____512 = FStar_Tactics_Types.goal_env g  in
        let uu____513 = FStar_Tactics_Types.goal_type g  in
        FStar_TypeChecker_Normalize.unfold_whnf uu____512 uu____513  in
      FStar_Syntax_Util.un_squash uu____511  in
    match uu____506 with
    | FStar_Pervasives_Native.Some t -> true
    | uu____519 -> false
  
let (print : Prims.string -> unit tac) = fun msg  -> tacprint msg; ret () 
let (debug : Prims.string -> unit tac) =
  fun msg  ->
    bind get
      (fun ps  ->
         (let uu____547 =
            let uu____548 =
              FStar_Ident.string_of_lid
                (ps.FStar_Tactics_Types.main_context).FStar_TypeChecker_Env.curmodule
               in
            FStar_Options.debug_module uu____548  in
          if uu____547 then tacprint msg else ());
         ret ())
  
let dump_goal : 'Auu____556 . 'Auu____556 -> FStar_Tactics_Types.goal -> unit
  =
  fun ps  ->
    fun goal  -> let uu____568 = goal_to_string goal  in tacprint uu____568
  
let (dump_cur : FStar_Tactics_Types.proofstate -> Prims.string -> unit) =
  fun ps  ->
    fun msg  ->
      match ps.FStar_Tactics_Types.goals with
      | [] -> tacprint1 "No more goals (%s)" msg
      | h::uu____580 ->
          (tacprint1 "Current goal (%s):" msg;
           (let uu____584 = FStar_List.hd ps.FStar_Tactics_Types.goals  in
            dump_goal ps uu____584))
  
let (ps_to_string :
  (Prims.string,FStar_Tactics_Types.proofstate)
    FStar_Pervasives_Native.tuple2 -> Prims.string)
  =
  fun uu____593  ->
    match uu____593 with
    | (msg,ps) ->
        let uu____600 =
          let uu____603 =
            let uu____604 =
              FStar_Util.string_of_int ps.FStar_Tactics_Types.depth  in
            FStar_Util.format2 "State dump @ depth %s (%s):\n" uu____604 msg
             in
          let uu____605 =
            let uu____608 =
              if ps.FStar_Tactics_Types.entry_range <> FStar_Range.dummyRange
              then
                let uu____609 =
                  FStar_Range.string_of_def_range
                    ps.FStar_Tactics_Types.entry_range
                   in
                FStar_Util.format1 "Location: %s\n" uu____609
              else ""  in
            let uu____611 =
              let uu____614 =
                let uu____615 =
                  FStar_Util.string_of_int
                    (FStar_List.length ps.FStar_Tactics_Types.goals)
                   in
                let uu____616 =
                  let uu____617 =
                    FStar_List.map goal_to_string
                      ps.FStar_Tactics_Types.goals
                     in
                  FStar_String.concat "\n" uu____617  in
                FStar_Util.format2 "ACTIVE goals (%s):\n%s\n" uu____615
                  uu____616
                 in
              let uu____620 =
                let uu____623 =
                  let uu____624 =
                    FStar_Util.string_of_int
                      (FStar_List.length ps.FStar_Tactics_Types.smt_goals)
                     in
                  let uu____625 =
                    let uu____626 =
                      FStar_List.map goal_to_string
                        ps.FStar_Tactics_Types.smt_goals
                       in
                    FStar_String.concat "\n" uu____626  in
                  FStar_Util.format2 "SMT goals (%s):\n%s\n" uu____624
                    uu____625
                   in
                [uu____623]  in
              uu____614 :: uu____620  in
            uu____608 :: uu____611  in
          uu____603 :: uu____605  in
        FStar_String.concat "" uu____600
  
let (goal_to_json : FStar_Tactics_Types.goal -> FStar_Util.json) =
  fun g  ->
    let g_binders =
      let uu____635 =
        let uu____636 = FStar_Tactics_Types.goal_env g  in
        FStar_TypeChecker_Env.all_binders uu____636  in
      let uu____637 =
        let uu____642 =
          let uu____643 = FStar_Tactics_Types.goal_env g  in
          FStar_TypeChecker_Env.dsenv uu____643  in
        FStar_Syntax_Print.binders_to_json uu____642  in
      FStar_All.pipe_right uu____635 uu____637  in
    let uu____644 =
      let uu____651 =
        let uu____658 =
          let uu____663 =
            let uu____664 =
              let uu____671 =
                let uu____676 =
                  let uu____677 =
                    let uu____678 = FStar_Tactics_Types.goal_env g  in
                    let uu____679 = FStar_Tactics_Types.goal_witness g  in
                    tts uu____678 uu____679  in
                  FStar_Util.JsonStr uu____677  in
                ("witness", uu____676)  in
              let uu____680 =
                let uu____687 =
                  let uu____692 =
                    let uu____693 =
                      let uu____694 = FStar_Tactics_Types.goal_env g  in
                      let uu____695 = FStar_Tactics_Types.goal_type g  in
                      tts uu____694 uu____695  in
                    FStar_Util.JsonStr uu____693  in
                  ("type", uu____692)  in
                [uu____687]  in
              uu____671 :: uu____680  in
            FStar_Util.JsonAssoc uu____664  in
          ("goal", uu____663)  in
        [uu____658]  in
      ("hyps", g_binders) :: uu____651  in
    FStar_Util.JsonAssoc uu____644
  
let (ps_to_json :
  (Prims.string,FStar_Tactics_Types.proofstate)
    FStar_Pervasives_Native.tuple2 -> FStar_Util.json)
  =
  fun uu____728  ->
    match uu____728 with
    | (msg,ps) ->
        let uu____735 =
          let uu____742 =
            let uu____749 =
              let uu____756 =
                let uu____763 =
                  let uu____768 =
                    let uu____769 =
                      FStar_List.map goal_to_json
                        ps.FStar_Tactics_Types.goals
                       in
                    FStar_Util.JsonList uu____769  in
                  ("goals", uu____768)  in
                let uu____772 =
                  let uu____779 =
                    let uu____784 =
                      let uu____785 =
                        FStar_List.map goal_to_json
                          ps.FStar_Tactics_Types.smt_goals
                         in
                      FStar_Util.JsonList uu____785  in
                    ("smt-goals", uu____784)  in
                  [uu____779]  in
                uu____763 :: uu____772  in
              ("depth", (FStar_Util.JsonInt (ps.FStar_Tactics_Types.depth)))
                :: uu____756
               in
            ("label", (FStar_Util.JsonStr msg)) :: uu____749  in
          let uu____808 =
            if ps.FStar_Tactics_Types.entry_range <> FStar_Range.dummyRange
            then
              let uu____821 =
                let uu____826 =
                  FStar_Range.json_of_def_range
                    ps.FStar_Tactics_Types.entry_range
                   in
                ("location", uu____826)  in
              [uu____821]
            else []  in
          FStar_List.append uu____742 uu____808  in
        FStar_Util.JsonAssoc uu____735
  
let (dump_proofstate :
  FStar_Tactics_Types.proofstate -> Prims.string -> unit) =
  fun ps  ->
    fun msg  ->
      FStar_Options.with_saved_options
        (fun uu____856  ->
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
         (let uu____879 = FStar_Tactics_Types.subst_proof_state subst1 ps  in
          dump_cur uu____879 msg);
         FStar_Tactics_Result.Success ((), ps))
  
let (print_proof_state : Prims.string -> unit tac) =
  fun msg  ->
    mk_tac
      (fun ps  ->
         let psc = ps.FStar_Tactics_Types.psc  in
         let subst1 = FStar_TypeChecker_Normalize.psc_subst psc  in
         (let uu____897 = FStar_Tactics_Types.subst_proof_state subst1 ps  in
          dump_proofstate uu____897 msg);
         FStar_Tactics_Result.Success ((), ps))
  
let mlog : 'a . (unit -> unit) -> (unit -> 'a tac) -> 'a tac =
  fun f  -> fun cont  -> bind get (fun ps  -> log ps f; cont ()) 
let fail : 'a . Prims.string -> 'a tac =
  fun msg  ->
    mk_tac
      (fun ps  ->
         (let uu____951 =
            FStar_TypeChecker_Env.debug ps.FStar_Tactics_Types.main_context
              (FStar_Options.Other "TacFail")
             in
          if uu____951
          then dump_proofstate ps (Prims.strcat "TACTIC FAILING: " msg)
          else ());
         FStar_Tactics_Result.Failed (msg, ps))
  
let fail1 : 'Auu____959 . Prims.string -> Prims.string -> 'Auu____959 tac =
  fun msg  ->
    fun x  -> let uu____972 = FStar_Util.format1 msg x  in fail uu____972
  
let fail2 :
  'Auu____981 .
    Prims.string -> Prims.string -> Prims.string -> 'Auu____981 tac
  =
  fun msg  ->
    fun x  ->
      fun y  -> let uu____999 = FStar_Util.format2 msg x y  in fail uu____999
  
let fail3 :
  'Auu____1010 .
    Prims.string ->
      Prims.string -> Prims.string -> Prims.string -> 'Auu____1010 tac
  =
  fun msg  ->
    fun x  ->
      fun y  ->
        fun z  ->
          let uu____1033 = FStar_Util.format3 msg x y z  in fail uu____1033
  
let fail4 :
  'Auu____1046 .
    Prims.string ->
      Prims.string ->
        Prims.string -> Prims.string -> Prims.string -> 'Auu____1046 tac
  =
  fun msg  ->
    fun x  ->
      fun y  ->
        fun z  ->
          fun w  ->
            let uu____1074 = FStar_Util.format4 msg x y z w  in
            fail uu____1074
  
let trytac' : 'a . 'a tac -> (Prims.string,'a) FStar_Util.either tac =
  fun t  ->
    mk_tac
      (fun ps  ->
         let tx = FStar_Syntax_Unionfind.new_transaction ()  in
         let uu____1107 = run t ps  in
         match uu____1107 with
         | FStar_Tactics_Result.Success (a,q) ->
             (FStar_Syntax_Unionfind.commit tx;
              FStar_Tactics_Result.Success ((FStar_Util.Inr a), q))
         | FStar_Tactics_Result.Failed (m,q) ->
             (FStar_Syntax_Unionfind.rollback tx;
              (let ps1 =
                 let uu___96_1131 = ps  in
                 {
                   FStar_Tactics_Types.main_context =
                     (uu___96_1131.FStar_Tactics_Types.main_context);
                   FStar_Tactics_Types.main_goal =
                     (uu___96_1131.FStar_Tactics_Types.main_goal);
                   FStar_Tactics_Types.all_implicits =
                     (uu___96_1131.FStar_Tactics_Types.all_implicits);
                   FStar_Tactics_Types.goals =
                     (uu___96_1131.FStar_Tactics_Types.goals);
                   FStar_Tactics_Types.smt_goals =
                     (uu___96_1131.FStar_Tactics_Types.smt_goals);
                   FStar_Tactics_Types.depth =
                     (uu___96_1131.FStar_Tactics_Types.depth);
                   FStar_Tactics_Types.__dump =
                     (uu___96_1131.FStar_Tactics_Types.__dump);
                   FStar_Tactics_Types.psc =
                     (uu___96_1131.FStar_Tactics_Types.psc);
                   FStar_Tactics_Types.entry_range =
                     (uu___96_1131.FStar_Tactics_Types.entry_range);
                   FStar_Tactics_Types.guard_policy =
                     (uu___96_1131.FStar_Tactics_Types.guard_policy);
                   FStar_Tactics_Types.freshness =
                     (q.FStar_Tactics_Types.freshness)
                 }  in
               FStar_Tactics_Result.Success ((FStar_Util.Inl m), ps1))))
  
let trytac : 'a . 'a tac -> 'a FStar_Pervasives_Native.option tac =
  fun t  ->
    let uu____1158 = trytac' t  in
    bind uu____1158
      (fun r  ->
         match r with
         | FStar_Util.Inr v1 -> ret (FStar_Pervasives_Native.Some v1)
         | FStar_Util.Inl uu____1185 -> ret FStar_Pervasives_Native.None)
  
let trytac_exn : 'a . 'a tac -> 'a FStar_Pervasives_Native.option tac =
  fun t  ->
    mk_tac
      (fun ps  ->
         try let uu____1221 = trytac t  in run uu____1221 ps
         with
         | FStar_Errors.Err (uu____1237,msg) ->
             (log ps
                (fun uu____1241  ->
                   FStar_Util.print1 "trytac_exn error: (%s)" msg);
              FStar_Tactics_Result.Success (FStar_Pervasives_Native.None, ps))
         | FStar_Errors.Error (uu____1246,msg,uu____1248) ->
             (log ps
                (fun uu____1251  ->
                   FStar_Util.print1 "trytac_exn error: (%s)" msg);
              FStar_Tactics_Result.Success (FStar_Pervasives_Native.None, ps)))
  
let wrap_err : 'a . Prims.string -> 'a tac -> 'a tac =
  fun pref  ->
    fun t  ->
      mk_tac
        (fun ps  ->
           let uu____1284 = run t ps  in
           match uu____1284 with
           | FStar_Tactics_Result.Success (a,q) ->
               FStar_Tactics_Result.Success (a, q)
           | FStar_Tactics_Result.Failed (msg,q) ->
               FStar_Tactics_Result.Failed
                 ((Prims.strcat pref (Prims.strcat ": " msg)), q))
  
let (set : FStar_Tactics_Types.proofstate -> unit tac) =
  fun p  -> mk_tac (fun uu____1303  -> FStar_Tactics_Result.Success ((), p)) 
let (__do_unify :
  env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.bool tac)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        (let uu____1324 =
           FStar_TypeChecker_Env.debug env (FStar_Options.Other "1346")  in
         if uu____1324
         then
           let uu____1325 = FStar_Syntax_Print.term_to_string t1  in
           let uu____1326 = FStar_Syntax_Print.term_to_string t2  in
           FStar_Util.print2 "%%%%%%%%do_unify %s =? %s\n" uu____1325
             uu____1326
         else ());
        (try
           let res = FStar_TypeChecker_Rel.teq_nosmt env t1 t2  in
           (let uu____1338 =
              FStar_TypeChecker_Env.debug env (FStar_Options.Other "1346")
               in
            if uu____1338
            then
              let uu____1339 = FStar_Util.string_of_bool res  in
              let uu____1340 = FStar_Syntax_Print.term_to_string t1  in
              let uu____1341 = FStar_Syntax_Print.term_to_string t2  in
              FStar_Util.print3 "%%%%%%%%do_unify (RESULT %s) %s =? %s\n"
                uu____1339 uu____1340 uu____1341
            else ());
           ret res
         with
         | FStar_Errors.Err (uu____1349,msg) ->
             mlog
               (fun uu____1352  ->
                  FStar_Util.print1 ">> do_unify error, (%s)\n" msg)
               (fun uu____1354  -> ret false)
         | FStar_Errors.Error (uu____1355,msg,r) ->
             mlog
               (fun uu____1360  ->
                  let uu____1361 = FStar_Range.string_of_range r  in
                  FStar_Util.print2 ">> do_unify error, (%s) at (%s)\n" msg
                    uu____1361) (fun uu____1363  -> ret false))
  
let (do_unify :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.bool tac)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        bind idtac
          (fun uu____1386  ->
             (let uu____1388 =
                FStar_TypeChecker_Env.debug env (FStar_Options.Other "1346")
                 in
              if uu____1388
              then
                (FStar_Options.push ();
                 (let uu____1390 =
                    FStar_Options.set_options FStar_Options.Set
                      "--debug_level Rel --debug_level RelCheck"
                     in
                  ()))
              else ());
             (let uu____1392 =
                let uu____1395 = __do_unify env t1 t2  in
                bind uu____1395
                  (fun b  ->
                     if Prims.op_Negation b
                     then
                       let t11 =
                         FStar_TypeChecker_Normalize.normalize [] env t1  in
                       let t21 =
                         FStar_TypeChecker_Normalize.normalize [] env t2  in
                       __do_unify env t11 t21
                     else ret b)
                 in
              bind uu____1392
                (fun r  ->
                   (let uu____1411 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "1346")
                       in
                    if uu____1411 then FStar_Options.pop () else ());
                   ret r)))
  
let (remove_solved_goals : unit tac) =
  bind get
    (fun ps  ->
       let ps' =
         let uu___101_1419 = ps  in
         let uu____1420 =
           FStar_List.filter
             (fun g  ->
                let uu____1426 = check_goal_solved g  in
                FStar_Option.isNone uu____1426) ps.FStar_Tactics_Types.goals
            in
         {
           FStar_Tactics_Types.main_context =
             (uu___101_1419.FStar_Tactics_Types.main_context);
           FStar_Tactics_Types.main_goal =
             (uu___101_1419.FStar_Tactics_Types.main_goal);
           FStar_Tactics_Types.all_implicits =
             (uu___101_1419.FStar_Tactics_Types.all_implicits);
           FStar_Tactics_Types.goals = uu____1420;
           FStar_Tactics_Types.smt_goals =
             (uu___101_1419.FStar_Tactics_Types.smt_goals);
           FStar_Tactics_Types.depth =
             (uu___101_1419.FStar_Tactics_Types.depth);
           FStar_Tactics_Types.__dump =
             (uu___101_1419.FStar_Tactics_Types.__dump);
           FStar_Tactics_Types.psc = (uu___101_1419.FStar_Tactics_Types.psc);
           FStar_Tactics_Types.entry_range =
             (uu___101_1419.FStar_Tactics_Types.entry_range);
           FStar_Tactics_Types.guard_policy =
             (uu___101_1419.FStar_Tactics_Types.guard_policy);
           FStar_Tactics_Types.freshness =
             (uu___101_1419.FStar_Tactics_Types.freshness)
         }  in
       set ps')
  
let (set_solution :
  FStar_Tactics_Types.goal -> FStar_Syntax_Syntax.term -> unit tac) =
  fun goal  ->
    fun solution  ->
      let uu____1443 =
        FStar_Syntax_Unionfind.find
          (goal.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_head
         in
      match uu____1443 with
      | FStar_Pervasives_Native.Some uu____1448 ->
          let uu____1449 =
            let uu____1450 = goal_to_string_verbose goal  in
            FStar_Util.format1 "Goal %s is already solved" uu____1450  in
          fail uu____1449
      | FStar_Pervasives_Native.None  ->
          (FStar_Syntax_Unionfind.change
             (goal.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_head
             solution;
           ret ())
  
let (trysolve :
  FStar_Tactics_Types.goal -> FStar_Syntax_Syntax.term -> Prims.bool tac) =
  fun goal  ->
    fun solution  ->
      let uu____1466 = FStar_Tactics_Types.goal_env goal  in
      let uu____1467 = FStar_Tactics_Types.goal_witness goal  in
      do_unify uu____1466 solution uu____1467
  
let (__dismiss : unit tac) =
  bind get
    (fun p  ->
       let uu____1473 =
         let uu___102_1474 = p  in
         let uu____1475 = FStar_List.tl p.FStar_Tactics_Types.goals  in
         {
           FStar_Tactics_Types.main_context =
             (uu___102_1474.FStar_Tactics_Types.main_context);
           FStar_Tactics_Types.main_goal =
             (uu___102_1474.FStar_Tactics_Types.main_goal);
           FStar_Tactics_Types.all_implicits =
             (uu___102_1474.FStar_Tactics_Types.all_implicits);
           FStar_Tactics_Types.goals = uu____1475;
           FStar_Tactics_Types.smt_goals =
             (uu___102_1474.FStar_Tactics_Types.smt_goals);
           FStar_Tactics_Types.depth =
             (uu___102_1474.FStar_Tactics_Types.depth);
           FStar_Tactics_Types.__dump =
             (uu___102_1474.FStar_Tactics_Types.__dump);
           FStar_Tactics_Types.psc = (uu___102_1474.FStar_Tactics_Types.psc);
           FStar_Tactics_Types.entry_range =
             (uu___102_1474.FStar_Tactics_Types.entry_range);
           FStar_Tactics_Types.guard_policy =
             (uu___102_1474.FStar_Tactics_Types.guard_policy);
           FStar_Tactics_Types.freshness =
             (uu___102_1474.FStar_Tactics_Types.freshness)
         }  in
       set uu____1473)
  
let (dismiss : unit -> unit tac) =
  fun uu____1484  ->
    bind get
      (fun p  ->
         match p.FStar_Tactics_Types.goals with
         | [] -> fail "dismiss: no more goals"
         | uu____1491 -> __dismiss)
  
let (solve :
  FStar_Tactics_Types.goal -> FStar_Syntax_Syntax.term -> unit tac) =
  fun goal  ->
    fun solution  ->
      let e = FStar_Tactics_Types.goal_env goal  in
      mlog
        (fun uu____1512  ->
           let uu____1513 =
             let uu____1514 = FStar_Tactics_Types.goal_witness goal  in
             tts e uu____1514  in
           let uu____1515 = tts e solution  in
           FStar_Util.print2 "solve %s := %s\n" uu____1513 uu____1515)
        (fun uu____1518  ->
           let uu____1519 = trysolve goal solution  in
           bind uu____1519
             (fun b  ->
                if b
                then bind __dismiss (fun uu____1527  -> remove_solved_goals)
                else
                  (let uu____1529 =
                     let uu____1530 =
                       let uu____1531 = FStar_Tactics_Types.goal_env goal  in
                       tts uu____1531 solution  in
                     let uu____1532 =
                       let uu____1533 = FStar_Tactics_Types.goal_env goal  in
                       let uu____1534 = FStar_Tactics_Types.goal_witness goal
                          in
                       tts uu____1533 uu____1534  in
                     let uu____1535 =
                       let uu____1536 = FStar_Tactics_Types.goal_env goal  in
                       let uu____1537 = FStar_Tactics_Types.goal_type goal
                          in
                       tts uu____1536 uu____1537  in
                     FStar_Util.format3 "%s does not solve %s : %s"
                       uu____1530 uu____1532 uu____1535
                      in
                   fail uu____1529)))
  
let (solve' :
  FStar_Tactics_Types.goal -> FStar_Syntax_Syntax.term -> unit tac) =
  fun goal  ->
    fun solution  ->
      let uu____1552 = set_solution goal solution  in
      bind uu____1552
        (fun uu____1556  ->
           bind __dismiss (fun uu____1558  -> remove_solved_goals))
  
let (dismiss_all : unit tac) =
  bind get
    (fun p  ->
       set
         (let uu___103_1565 = p  in
          {
            FStar_Tactics_Types.main_context =
              (uu___103_1565.FStar_Tactics_Types.main_context);
            FStar_Tactics_Types.main_goal =
              (uu___103_1565.FStar_Tactics_Types.main_goal);
            FStar_Tactics_Types.all_implicits =
              (uu___103_1565.FStar_Tactics_Types.all_implicits);
            FStar_Tactics_Types.goals = [];
            FStar_Tactics_Types.smt_goals =
              (uu___103_1565.FStar_Tactics_Types.smt_goals);
            FStar_Tactics_Types.depth =
              (uu___103_1565.FStar_Tactics_Types.depth);
            FStar_Tactics_Types.__dump =
              (uu___103_1565.FStar_Tactics_Types.__dump);
            FStar_Tactics_Types.psc = (uu___103_1565.FStar_Tactics_Types.psc);
            FStar_Tactics_Types.entry_range =
              (uu___103_1565.FStar_Tactics_Types.entry_range);
            FStar_Tactics_Types.guard_policy =
              (uu___103_1565.FStar_Tactics_Types.guard_policy);
            FStar_Tactics_Types.freshness =
              (uu___103_1565.FStar_Tactics_Types.freshness)
          }))
  
let (nwarn : Prims.int FStar_ST.ref) =
  FStar_Util.mk_ref (Prims.parse_int "0") 
let (check_valid_goal : FStar_Tactics_Types.goal -> unit) =
  fun g  ->
    let uu____1584 = FStar_Options.defensive ()  in
    if uu____1584
    then
      let b = true  in
      let env = FStar_Tactics_Types.goal_env g  in
      let b1 =
        b &&
          (let uu____1589 = FStar_Tactics_Types.goal_witness g  in
           FStar_TypeChecker_Env.closed env uu____1589)
         in
      let b2 =
        b1 &&
          (let uu____1592 = FStar_Tactics_Types.goal_type g  in
           FStar_TypeChecker_Env.closed env uu____1592)
         in
      let rec aux b3 e =
        let uu____1604 = FStar_TypeChecker_Env.pop_bv e  in
        match uu____1604 with
        | FStar_Pervasives_Native.None  -> b3
        | FStar_Pervasives_Native.Some (bv,e1) ->
            let b4 =
              b3 &&
                (FStar_TypeChecker_Env.closed e1 bv.FStar_Syntax_Syntax.sort)
               in
            aux b4 e1
         in
      let uu____1622 =
        (let uu____1625 = aux b2 env  in Prims.op_Negation uu____1625) &&
          (let uu____1627 = FStar_ST.op_Bang nwarn  in
           uu____1627 < (Prims.parse_int "5"))
         in
      (if uu____1622
       then
         ((let uu____1652 =
             let uu____1653 = FStar_Tactics_Types.goal_type g  in
             uu____1653.FStar_Syntax_Syntax.pos  in
           let uu____1656 =
             let uu____1661 =
               let uu____1662 = goal_to_string_verbose g  in
               FStar_Util.format1
                 "The following goal is ill-formed. Keeping calm and carrying on...\n<%s>\n\n"
                 uu____1662
                in
             (FStar_Errors.Warning_IllFormedGoal, uu____1661)  in
           FStar_Errors.log_issue uu____1652 uu____1656);
          (let uu____1663 =
             let uu____1664 = FStar_ST.op_Bang nwarn  in
             uu____1664 + (Prims.parse_int "1")  in
           FStar_ST.op_Colon_Equals nwarn uu____1663))
       else ())
    else ()
  
let (add_goals : FStar_Tactics_Types.goal Prims.list -> unit tac) =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___104_1732 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___104_1732.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___104_1732.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___104_1732.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (FStar_List.append gs p.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (uu___104_1732.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___104_1732.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___104_1732.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___104_1732.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___104_1732.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___104_1732.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___104_1732.FStar_Tactics_Types.freshness)
            }))
  
let (add_smt_goals : FStar_Tactics_Types.goal Prims.list -> unit tac) =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___105_1752 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___105_1752.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___105_1752.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___105_1752.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___105_1752.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (FStar_List.append gs p.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___105_1752.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___105_1752.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___105_1752.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___105_1752.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___105_1752.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___105_1752.FStar_Tactics_Types.freshness)
            }))
  
let (push_goals : FStar_Tactics_Types.goal Prims.list -> unit tac) =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___106_1772 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___106_1772.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___106_1772.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___106_1772.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (FStar_List.append p.FStar_Tactics_Types.goals gs);
              FStar_Tactics_Types.smt_goals =
                (uu___106_1772.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___106_1772.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___106_1772.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___106_1772.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___106_1772.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___106_1772.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___106_1772.FStar_Tactics_Types.freshness)
            }))
  
let (push_smt_goals : FStar_Tactics_Types.goal Prims.list -> unit tac) =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___107_1792 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___107_1792.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___107_1792.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___107_1792.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___107_1792.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (FStar_List.append p.FStar_Tactics_Types.smt_goals gs);
              FStar_Tactics_Types.depth =
                (uu___107_1792.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___107_1792.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___107_1792.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___107_1792.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___107_1792.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___107_1792.FStar_Tactics_Types.freshness)
            }))
  
let (replace_cur : FStar_Tactics_Types.goal -> unit tac) =
  fun g  -> bind __dismiss (fun uu____1803  -> add_goals [g]) 
let (add_implicits : implicits -> unit tac) =
  fun i  ->
    bind get
      (fun p  ->
         set
           (let uu___108_1817 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___108_1817.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___108_1817.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (FStar_List.append i p.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___108_1817.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (uu___108_1817.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___108_1817.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___108_1817.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___108_1817.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___108_1817.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___108_1817.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___108_1817.FStar_Tactics_Types.freshness)
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
        let uu____1853 =
          FStar_TypeChecker_Util.new_implicit_var reason
            typ.FStar_Syntax_Syntax.pos env typ
           in
        match uu____1853 with
        | (u,ctx_uvar,g_u) ->
            let uu____1887 =
              add_implicits g_u.FStar_TypeChecker_Env.implicits  in
            bind uu____1887
              (fun uu____1896  ->
                 let uu____1897 =
                   let uu____1902 =
                     let uu____1903 = FStar_List.hd ctx_uvar  in
                     FStar_Pervasives_Native.fst uu____1903  in
                   (u, uu____1902)  in
                 ret uu____1897)
  
let (is_true : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____1921 = FStar_Syntax_Util.un_squash t  in
    match uu____1921 with
    | FStar_Pervasives_Native.Some t' ->
        let uu____1931 =
          let uu____1932 = FStar_Syntax_Subst.compress t'  in
          uu____1932.FStar_Syntax_Syntax.n  in
        (match uu____1931 with
         | FStar_Syntax_Syntax.Tm_fvar fv ->
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.true_lid
         | uu____1936 -> false)
    | uu____1937 -> false
  
let (is_false : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____1947 = FStar_Syntax_Util.un_squash t  in
    match uu____1947 with
    | FStar_Pervasives_Native.Some t' ->
        let uu____1957 =
          let uu____1958 = FStar_Syntax_Subst.compress t'  in
          uu____1958.FStar_Syntax_Syntax.n  in
        (match uu____1957 with
         | FStar_Syntax_Syntax.Tm_fvar fv ->
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.false_lid
         | uu____1962 -> false)
    | uu____1963 -> false
  
let (cur_goal : unit -> FStar_Tactics_Types.goal tac) =
  fun uu____1974  ->
    bind get
      (fun p  ->
         match p.FStar_Tactics_Types.goals with
         | [] -> fail "No more goals (1)"
         | hd1::tl1 ->
             let uu____1985 =
               FStar_Syntax_Unionfind.find
                 (hd1.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_head
                in
             (match uu____1985 with
              | FStar_Pervasives_Native.None  -> ret hd1
              | FStar_Pervasives_Native.Some t ->
                  ((let uu____1992 = goal_to_string_verbose hd1  in
                    let uu____1993 = FStar_Syntax_Print.term_to_string t  in
                    FStar_Util.print2
                      "!!!!!!!!!!!! GOAL IS ALREADY SOLVED! %s\nsol is %s\n"
                      uu____1992 uu____1993);
                   ret hd1)))
  
let (tadmit : unit -> unit tac) =
  fun uu____2000  ->
    let uu____2003 =
      let uu____2006 = cur_goal ()  in
      bind uu____2006
        (fun g  ->
           (let uu____2013 =
              let uu____2014 = FStar_Tactics_Types.goal_type g  in
              uu____2014.FStar_Syntax_Syntax.pos  in
            let uu____2017 =
              let uu____2022 =
                let uu____2023 = goal_to_string g  in
                FStar_Util.format1 "Tactics admitted goal <%s>\n\n"
                  uu____2023
                 in
              (FStar_Errors.Warning_TacAdmit, uu____2022)  in
            FStar_Errors.log_issue uu____2013 uu____2017);
           solve' g FStar_Syntax_Util.exp_unit)
       in
    FStar_All.pipe_left (wrap_err "tadmit") uu____2003
  
let (fresh : unit -> FStar_BigInt.t tac) =
  fun uu____2034  ->
    bind get
      (fun ps  ->
         let n1 = ps.FStar_Tactics_Types.freshness  in
         let ps1 =
           let uu___109_2044 = ps  in
           {
             FStar_Tactics_Types.main_context =
               (uu___109_2044.FStar_Tactics_Types.main_context);
             FStar_Tactics_Types.main_goal =
               (uu___109_2044.FStar_Tactics_Types.main_goal);
             FStar_Tactics_Types.all_implicits =
               (uu___109_2044.FStar_Tactics_Types.all_implicits);
             FStar_Tactics_Types.goals =
               (uu___109_2044.FStar_Tactics_Types.goals);
             FStar_Tactics_Types.smt_goals =
               (uu___109_2044.FStar_Tactics_Types.smt_goals);
             FStar_Tactics_Types.depth =
               (uu___109_2044.FStar_Tactics_Types.depth);
             FStar_Tactics_Types.__dump =
               (uu___109_2044.FStar_Tactics_Types.__dump);
             FStar_Tactics_Types.psc =
               (uu___109_2044.FStar_Tactics_Types.psc);
             FStar_Tactics_Types.entry_range =
               (uu___109_2044.FStar_Tactics_Types.entry_range);
             FStar_Tactics_Types.guard_policy =
               (uu___109_2044.FStar_Tactics_Types.guard_policy);
             FStar_Tactics_Types.freshness = (n1 + (Prims.parse_int "1"))
           }  in
         let uu____2045 = set ps1  in
         bind uu____2045
           (fun uu____2050  ->
              let uu____2051 = FStar_BigInt.of_int_fs n1  in ret uu____2051))
  
let (ngoals : unit -> FStar_BigInt.t tac) =
  fun uu____2058  ->
    bind get
      (fun ps  ->
         let n1 = FStar_List.length ps.FStar_Tactics_Types.goals  in
         let uu____2066 = FStar_BigInt.of_int_fs n1  in ret uu____2066)
  
let (ngoals_smt : unit -> FStar_BigInt.t tac) =
  fun uu____2079  ->
    bind get
      (fun ps  ->
         let n1 = FStar_List.length ps.FStar_Tactics_Types.smt_goals  in
         let uu____2087 = FStar_BigInt.of_int_fs n1  in ret uu____2087)
  
let (is_guard : unit -> Prims.bool tac) =
  fun uu____2100  ->
    let uu____2103 = cur_goal ()  in
    bind uu____2103 (fun g  -> ret g.FStar_Tactics_Types.is_guard)
  
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
            let uu____2135 = env.FStar_TypeChecker_Env.universe_of env phi
               in
            FStar_Syntax_Util.mk_squash uu____2135 phi  in
          let uu____2136 = new_uvar reason env typ  in
          bind uu____2136
            (fun uu____2151  ->
               match uu____2151 with
               | (uu____2158,ctx_uvar) ->
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
             (fun uu____2203  ->
                let uu____2204 = tts e t  in
                FStar_Util.print1 "Tac> __tc(%s)\n" uu____2204)
             (fun uu____2207  ->
                let e1 =
                  let uu___110_2209 = e  in
                  {
                    FStar_TypeChecker_Env.solver =
                      (uu___110_2209.FStar_TypeChecker_Env.solver);
                    FStar_TypeChecker_Env.range =
                      (uu___110_2209.FStar_TypeChecker_Env.range);
                    FStar_TypeChecker_Env.curmodule =
                      (uu___110_2209.FStar_TypeChecker_Env.curmodule);
                    FStar_TypeChecker_Env.gamma =
                      (uu___110_2209.FStar_TypeChecker_Env.gamma);
                    FStar_TypeChecker_Env.gamma_sig =
                      (uu___110_2209.FStar_TypeChecker_Env.gamma_sig);
                    FStar_TypeChecker_Env.gamma_cache =
                      (uu___110_2209.FStar_TypeChecker_Env.gamma_cache);
                    FStar_TypeChecker_Env.modules =
                      (uu___110_2209.FStar_TypeChecker_Env.modules);
                    FStar_TypeChecker_Env.expected_typ =
                      (uu___110_2209.FStar_TypeChecker_Env.expected_typ);
                    FStar_TypeChecker_Env.sigtab =
                      (uu___110_2209.FStar_TypeChecker_Env.sigtab);
                    FStar_TypeChecker_Env.is_pattern =
                      (uu___110_2209.FStar_TypeChecker_Env.is_pattern);
                    FStar_TypeChecker_Env.instantiate_imp =
                      (uu___110_2209.FStar_TypeChecker_Env.instantiate_imp);
                    FStar_TypeChecker_Env.effects =
                      (uu___110_2209.FStar_TypeChecker_Env.effects);
                    FStar_TypeChecker_Env.generalize =
                      (uu___110_2209.FStar_TypeChecker_Env.generalize);
                    FStar_TypeChecker_Env.letrecs =
                      (uu___110_2209.FStar_TypeChecker_Env.letrecs);
                    FStar_TypeChecker_Env.top_level =
                      (uu___110_2209.FStar_TypeChecker_Env.top_level);
                    FStar_TypeChecker_Env.check_uvars =
                      (uu___110_2209.FStar_TypeChecker_Env.check_uvars);
                    FStar_TypeChecker_Env.use_eq =
                      (uu___110_2209.FStar_TypeChecker_Env.use_eq);
                    FStar_TypeChecker_Env.is_iface =
                      (uu___110_2209.FStar_TypeChecker_Env.is_iface);
                    FStar_TypeChecker_Env.admit =
                      (uu___110_2209.FStar_TypeChecker_Env.admit);
                    FStar_TypeChecker_Env.lax =
                      (uu___110_2209.FStar_TypeChecker_Env.lax);
                    FStar_TypeChecker_Env.lax_universes =
                      (uu___110_2209.FStar_TypeChecker_Env.lax_universes);
                    FStar_TypeChecker_Env.failhard =
                      (uu___110_2209.FStar_TypeChecker_Env.failhard);
                    FStar_TypeChecker_Env.nosynth =
                      (uu___110_2209.FStar_TypeChecker_Env.nosynth);
                    FStar_TypeChecker_Env.uvar_subtyping = false;
                    FStar_TypeChecker_Env.tc_term =
                      (uu___110_2209.FStar_TypeChecker_Env.tc_term);
                    FStar_TypeChecker_Env.type_of =
                      (uu___110_2209.FStar_TypeChecker_Env.type_of);
                    FStar_TypeChecker_Env.universe_of =
                      (uu___110_2209.FStar_TypeChecker_Env.universe_of);
                    FStar_TypeChecker_Env.check_type_of =
                      (uu___110_2209.FStar_TypeChecker_Env.check_type_of);
                    FStar_TypeChecker_Env.use_bv_sorts =
                      (uu___110_2209.FStar_TypeChecker_Env.use_bv_sorts);
                    FStar_TypeChecker_Env.qtbl_name_and_index =
                      (uu___110_2209.FStar_TypeChecker_Env.qtbl_name_and_index);
                    FStar_TypeChecker_Env.normalized_eff_names =
                      (uu___110_2209.FStar_TypeChecker_Env.normalized_eff_names);
                    FStar_TypeChecker_Env.proof_ns =
                      (uu___110_2209.FStar_TypeChecker_Env.proof_ns);
                    FStar_TypeChecker_Env.synth_hook =
                      (uu___110_2209.FStar_TypeChecker_Env.synth_hook);
                    FStar_TypeChecker_Env.splice =
                      (uu___110_2209.FStar_TypeChecker_Env.splice);
                    FStar_TypeChecker_Env.is_native_tactic =
                      (uu___110_2209.FStar_TypeChecker_Env.is_native_tactic);
                    FStar_TypeChecker_Env.identifier_info =
                      (uu___110_2209.FStar_TypeChecker_Env.identifier_info);
                    FStar_TypeChecker_Env.tc_hooks =
                      (uu___110_2209.FStar_TypeChecker_Env.tc_hooks);
                    FStar_TypeChecker_Env.dsenv =
                      (uu___110_2209.FStar_TypeChecker_Env.dsenv);
                    FStar_TypeChecker_Env.dep_graph =
                      (uu___110_2209.FStar_TypeChecker_Env.dep_graph)
                  }  in
                try
                  let uu____2229 =
                    (ps.FStar_Tactics_Types.main_context).FStar_TypeChecker_Env.type_of
                      e1 t
                     in
                  ret uu____2229
                with
                | FStar_Errors.Err (uu____2256,msg) ->
                    let uu____2258 = tts e1 t  in
                    let uu____2259 =
                      let uu____2260 = FStar_TypeChecker_Env.all_binders e1
                         in
                      FStar_All.pipe_right uu____2260
                        (FStar_Syntax_Print.binders_to_string ", ")
                       in
                    fail3 "Cannot type %s in context (%s). Error = (%s)"
                      uu____2258 uu____2259 msg
                | FStar_Errors.Error (uu____2267,msg,uu____2269) ->
                    let uu____2270 = tts e1 t  in
                    let uu____2271 =
                      let uu____2272 = FStar_TypeChecker_Env.all_binders e1
                         in
                      FStar_All.pipe_right uu____2272
                        (FStar_Syntax_Print.binders_to_string ", ")
                       in
                    fail3 "Cannot type %s in context (%s). Error = (%s)"
                      uu____2270 uu____2271 msg))
  
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
  fun uu____2299  ->
    bind get (fun ps  -> ret ps.FStar_Tactics_Types.guard_policy)
  
let (set_guard_policy : FStar_Tactics_Types.guard_policy -> unit tac) =
  fun pol  ->
    bind get
      (fun ps  ->
         set
           (let uu___113_2317 = ps  in
            {
              FStar_Tactics_Types.main_context =
                (uu___113_2317.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___113_2317.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___113_2317.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___113_2317.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (uu___113_2317.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___113_2317.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___113_2317.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___113_2317.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___113_2317.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy = pol;
              FStar_Tactics_Types.freshness =
                (uu___113_2317.FStar_Tactics_Types.freshness)
            }))
  
let with_policy : 'a . FStar_Tactics_Types.guard_policy -> 'a tac -> 'a tac =
  fun pol  ->
    fun t  ->
      let uu____2341 = get_guard_policy ()  in
      bind uu____2341
        (fun old_pol  ->
           let uu____2347 = set_guard_policy pol  in
           bind uu____2347
             (fun uu____2351  ->
                bind t
                  (fun r  ->
                     let uu____2355 = set_guard_policy old_pol  in
                     bind uu____2355 (fun uu____2359  -> ret r))))
  
let (proc_guard :
  Prims.string ->
    env ->
      FStar_TypeChecker_Env.guard_t -> FStar_Options.optionstate -> unit tac)
  =
  fun reason  ->
    fun e  ->
      fun g  ->
        fun opts  ->
          let uu____2384 =
            let uu____2385 = FStar_TypeChecker_Rel.simplify_guard e g  in
            uu____2385.FStar_TypeChecker_Env.guard_f  in
          match uu____2384 with
          | FStar_TypeChecker_Common.Trivial  -> ret ()
          | FStar_TypeChecker_Common.NonTrivial f ->
              let uu____2389 = istrivial e f  in
              if uu____2389
              then ret ()
              else
                bind get
                  (fun ps  ->
                     match ps.FStar_Tactics_Types.guard_policy with
                     | FStar_Tactics_Types.Drop  -> ret ()
                     | FStar_Tactics_Types.Goal  ->
                         let uu____2397 = mk_irrelevant_goal reason e f opts
                            in
                         bind uu____2397
                           (fun goal  ->
                              let goal1 =
                                let uu___114_2404 = goal  in
                                {
                                  FStar_Tactics_Types.goal_main_env =
                                    (uu___114_2404.FStar_Tactics_Types.goal_main_env);
                                  FStar_Tactics_Types.goal_ctx_uvar =
                                    (uu___114_2404.FStar_Tactics_Types.goal_ctx_uvar);
                                  FStar_Tactics_Types.opts =
                                    (uu___114_2404.FStar_Tactics_Types.opts);
                                  FStar_Tactics_Types.is_guard = true
                                }  in
                              push_goals [goal1])
                     | FStar_Tactics_Types.SMT  ->
                         let uu____2405 = mk_irrelevant_goal reason e f opts
                            in
                         bind uu____2405
                           (fun goal  ->
                              let goal1 =
                                let uu___115_2412 = goal  in
                                {
                                  FStar_Tactics_Types.goal_main_env =
                                    (uu___115_2412.FStar_Tactics_Types.goal_main_env);
                                  FStar_Tactics_Types.goal_ctx_uvar =
                                    (uu___115_2412.FStar_Tactics_Types.goal_ctx_uvar);
                                  FStar_Tactics_Types.opts =
                                    (uu___115_2412.FStar_Tactics_Types.opts);
                                  FStar_Tactics_Types.is_guard = true
                                }  in
                              push_smt_goals [goal1])
                     | FStar_Tactics_Types.Force  ->
                         (try
                            let uu____2420 =
                              let uu____2421 =
                                let uu____2422 =
                                  FStar_TypeChecker_Rel.discharge_guard_no_smt
                                    e g
                                   in
                                FStar_All.pipe_left
                                  FStar_TypeChecker_Rel.is_trivial uu____2422
                                 in
                              Prims.op_Negation uu____2421  in
                            if uu____2420
                            then
                              mlog
                                (fun uu____2427  ->
                                   let uu____2428 =
                                     FStar_TypeChecker_Rel.guard_to_string e
                                       g
                                      in
                                   FStar_Util.print1 "guard = %s\n"
                                     uu____2428)
                                (fun uu____2430  ->
                                   fail1 "Forcing the guard failed %s)"
                                     reason)
                            else ret ()
                          with
                          | uu____2437 ->
                              mlog
                                (fun uu____2440  ->
                                   let uu____2441 =
                                     FStar_TypeChecker_Rel.guard_to_string e
                                       g
                                      in
                                   FStar_Util.print1 "guard = %s\n"
                                     uu____2441)
                                (fun uu____2443  ->
                                   fail1 "Forcing the guard failed (%s)"
                                     reason)))
  
let (tc : FStar_Syntax_Syntax.term -> FStar_Reflection_Data.typ tac) =
  fun t  ->
    let uu____2453 =
      let uu____2456 = cur_goal ()  in
      bind uu____2456
        (fun goal  ->
           let uu____2462 =
             let uu____2471 = FStar_Tactics_Types.goal_env goal  in
             __tc uu____2471 t  in
           bind uu____2462
             (fun uu____2483  ->
                match uu____2483 with
                | (t1,typ,guard) ->
                    let uu____2495 =
                      let uu____2498 = FStar_Tactics_Types.goal_env goal  in
                      proc_guard "tc" uu____2498 guard
                        goal.FStar_Tactics_Types.opts
                       in
                    bind uu____2495 (fun uu____2500  -> ret typ)))
       in
    FStar_All.pipe_left (wrap_err "tc") uu____2453
  
let (add_irrelevant_goal :
  Prims.string ->
    env -> FStar_Reflection_Data.typ -> FStar_Options.optionstate -> unit tac)
  =
  fun reason  ->
    fun env  ->
      fun phi  ->
        fun opts  ->
          let uu____2529 = mk_irrelevant_goal reason env phi opts  in
          bind uu____2529 (fun goal  -> add_goals [goal])
  
let (trivial : unit -> unit tac) =
  fun uu____2540  ->
    let uu____2543 = cur_goal ()  in
    bind uu____2543
      (fun goal  ->
         let uu____2549 =
           let uu____2550 = FStar_Tactics_Types.goal_env goal  in
           let uu____2551 = FStar_Tactics_Types.goal_type goal  in
           istrivial uu____2550 uu____2551  in
         if uu____2549
         then solve' goal FStar_Syntax_Util.exp_unit
         else
           (let uu____2555 =
              let uu____2556 = FStar_Tactics_Types.goal_env goal  in
              let uu____2557 = FStar_Tactics_Types.goal_type goal  in
              tts uu____2556 uu____2557  in
            fail1 "Not a trivial goal: %s" uu____2555))
  
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
          let uu____2586 =
            let uu____2587 = FStar_TypeChecker_Rel.simplify_guard e g  in
            uu____2587.FStar_TypeChecker_Env.guard_f  in
          match uu____2586 with
          | FStar_TypeChecker_Common.Trivial  ->
              ret FStar_Pervasives_Native.None
          | FStar_TypeChecker_Common.NonTrivial f ->
              let uu____2595 = istrivial e f  in
              if uu____2595
              then ret FStar_Pervasives_Native.None
              else
                (let uu____2603 = mk_irrelevant_goal reason e f opts  in
                 bind uu____2603
                   (fun goal  ->
                      ret
                        (FStar_Pervasives_Native.Some
                           (let uu___118_2613 = goal  in
                            {
                              FStar_Tactics_Types.goal_main_env =
                                (uu___118_2613.FStar_Tactics_Types.goal_main_env);
                              FStar_Tactics_Types.goal_ctx_uvar =
                                (uu___118_2613.FStar_Tactics_Types.goal_ctx_uvar);
                              FStar_Tactics_Types.opts =
                                (uu___118_2613.FStar_Tactics_Types.opts);
                              FStar_Tactics_Types.is_guard = true
                            }))))
  
let (smt : unit -> unit tac) =
  fun uu____2620  ->
    let uu____2623 = cur_goal ()  in
    bind uu____2623
      (fun g  ->
         let uu____2629 = is_irrelevant g  in
         if uu____2629
         then bind __dismiss (fun uu____2633  -> add_smt_goals [g])
         else
           (let uu____2635 =
              let uu____2636 = FStar_Tactics_Types.goal_env g  in
              let uu____2637 = FStar_Tactics_Types.goal_type g  in
              tts uu____2636 uu____2637  in
            fail1 "goal is not irrelevant: cannot dispatch to smt (%s)"
              uu____2635))
  
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
             let uu____2686 =
               try
                 let uu____2720 =
                   let uu____2729 = FStar_BigInt.to_int_fs n1  in
                   FStar_List.splitAt uu____2729 p.FStar_Tactics_Types.goals
                    in
                 ret uu____2720
               with | uu____2751 -> fail "divide: not enough goals"  in
             bind uu____2686
               (fun uu____2778  ->
                  match uu____2778 with
                  | (lgs,rgs) ->
                      let lp =
                        let uu___119_2804 = p  in
                        {
                          FStar_Tactics_Types.main_context =
                            (uu___119_2804.FStar_Tactics_Types.main_context);
                          FStar_Tactics_Types.main_goal =
                            (uu___119_2804.FStar_Tactics_Types.main_goal);
                          FStar_Tactics_Types.all_implicits =
                            (uu___119_2804.FStar_Tactics_Types.all_implicits);
                          FStar_Tactics_Types.goals = lgs;
                          FStar_Tactics_Types.smt_goals = [];
                          FStar_Tactics_Types.depth =
                            (uu___119_2804.FStar_Tactics_Types.depth);
                          FStar_Tactics_Types.__dump =
                            (uu___119_2804.FStar_Tactics_Types.__dump);
                          FStar_Tactics_Types.psc =
                            (uu___119_2804.FStar_Tactics_Types.psc);
                          FStar_Tactics_Types.entry_range =
                            (uu___119_2804.FStar_Tactics_Types.entry_range);
                          FStar_Tactics_Types.guard_policy =
                            (uu___119_2804.FStar_Tactics_Types.guard_policy);
                          FStar_Tactics_Types.freshness =
                            (uu___119_2804.FStar_Tactics_Types.freshness)
                        }  in
                      let rp =
                        let uu___120_2806 = p  in
                        {
                          FStar_Tactics_Types.main_context =
                            (uu___120_2806.FStar_Tactics_Types.main_context);
                          FStar_Tactics_Types.main_goal =
                            (uu___120_2806.FStar_Tactics_Types.main_goal);
                          FStar_Tactics_Types.all_implicits =
                            (uu___120_2806.FStar_Tactics_Types.all_implicits);
                          FStar_Tactics_Types.goals = rgs;
                          FStar_Tactics_Types.smt_goals = [];
                          FStar_Tactics_Types.depth =
                            (uu___120_2806.FStar_Tactics_Types.depth);
                          FStar_Tactics_Types.__dump =
                            (uu___120_2806.FStar_Tactics_Types.__dump);
                          FStar_Tactics_Types.psc =
                            (uu___120_2806.FStar_Tactics_Types.psc);
                          FStar_Tactics_Types.entry_range =
                            (uu___120_2806.FStar_Tactics_Types.entry_range);
                          FStar_Tactics_Types.guard_policy =
                            (uu___120_2806.FStar_Tactics_Types.guard_policy);
                          FStar_Tactics_Types.freshness =
                            (uu___120_2806.FStar_Tactics_Types.freshness)
                        }  in
                      let uu____2807 = set lp  in
                      bind uu____2807
                        (fun uu____2815  ->
                           bind l
                             (fun a  ->
                                bind get
                                  (fun lp'  ->
                                     let uu____2829 = set rp  in
                                     bind uu____2829
                                       (fun uu____2837  ->
                                          bind r
                                            (fun b  ->
                                               bind get
                                                 (fun rp'  ->
                                                    let p' =
                                                      let uu___121_2853 = p
                                                         in
                                                      {
                                                        FStar_Tactics_Types.main_context
                                                          =
                                                          (uu___121_2853.FStar_Tactics_Types.main_context);
                                                        FStar_Tactics_Types.main_goal
                                                          =
                                                          (uu___121_2853.FStar_Tactics_Types.main_goal);
                                                        FStar_Tactics_Types.all_implicits
                                                          =
                                                          (uu___121_2853.FStar_Tactics_Types.all_implicits);
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
                                                          (uu___121_2853.FStar_Tactics_Types.depth);
                                                        FStar_Tactics_Types.__dump
                                                          =
                                                          (uu___121_2853.FStar_Tactics_Types.__dump);
                                                        FStar_Tactics_Types.psc
                                                          =
                                                          (uu___121_2853.FStar_Tactics_Types.psc);
                                                        FStar_Tactics_Types.entry_range
                                                          =
                                                          (uu___121_2853.FStar_Tactics_Types.entry_range);
                                                        FStar_Tactics_Types.guard_policy
                                                          =
                                                          (uu___121_2853.FStar_Tactics_Types.guard_policy);
                                                        FStar_Tactics_Types.freshness
                                                          =
                                                          (uu___121_2853.FStar_Tactics_Types.freshness)
                                                      }  in
                                                    let uu____2854 = set p'
                                                       in
                                                    bind uu____2854
                                                      (fun uu____2862  ->
                                                         bind
                                                           remove_solved_goals
                                                           (fun uu____2868 
                                                              -> ret (a, b)))))))))))
  
let focus : 'a . 'a tac -> 'a tac =
  fun f  ->
    let uu____2889 = divide FStar_BigInt.one f idtac  in
    bind uu____2889
      (fun uu____2902  -> match uu____2902 with | (a,()) -> ret a)
  
let rec map : 'a . 'a tac -> 'a Prims.list tac =
  fun tau  ->
    bind get
      (fun p  ->
         match p.FStar_Tactics_Types.goals with
         | [] -> ret []
         | uu____2939::uu____2940 ->
             let uu____2943 =
               let uu____2952 = map tau  in
               divide FStar_BigInt.one tau uu____2952  in
             bind uu____2943
               (fun uu____2970  ->
                  match uu____2970 with | (h,t) -> ret (h :: t)))
  
let (seq : unit tac -> unit tac -> unit tac) =
  fun t1  ->
    fun t2  ->
      let uu____3011 =
        bind t1
          (fun uu____3016  ->
             let uu____3017 = map t2  in
             bind uu____3017 (fun uu____3025  -> ret ()))
         in
      focus uu____3011
  
let (intro : unit -> FStar_Syntax_Syntax.binder tac) =
  fun uu____3034  ->
    let uu____3037 =
      let uu____3040 = cur_goal ()  in
      bind uu____3040
        (fun goal  ->
           let uu____3049 =
             let uu____3056 = FStar_Tactics_Types.goal_type goal  in
             FStar_Syntax_Util.arrow_one uu____3056  in
           match uu____3049 with
           | FStar_Pervasives_Native.Some (b,c) ->
               let uu____3065 =
                 let uu____3066 = FStar_Syntax_Util.is_total_comp c  in
                 Prims.op_Negation uu____3066  in
               if uu____3065
               then fail "Codomain is effectful"
               else
                 (let env' =
                    let uu____3071 = FStar_Tactics_Types.goal_env goal  in
                    FStar_TypeChecker_Env.push_binders uu____3071 [b]  in
                  let typ' = comp_to_typ c  in
                  let uu____3081 = new_uvar "intro" env' typ'  in
                  bind uu____3081
                    (fun uu____3097  ->
                       match uu____3097 with
                       | (body,ctx_uvar) ->
                           let sol =
                             FStar_Syntax_Util.abs [b] body
                               FStar_Pervasives_Native.None
                              in
                           let uu____3117 = set_solution goal sol  in
                           bind uu____3117
                             (fun uu____3123  ->
                                let g =
                                  FStar_Tactics_Types.mk_goal env' ctx_uvar
                                    goal.FStar_Tactics_Types.opts
                                    goal.FStar_Tactics_Types.is_guard
                                   in
                                let uu____3125 =
                                  let uu____3128 = bnorm_goal g  in
                                  replace_cur uu____3128  in
                                bind uu____3125 (fun uu____3130  -> ret b))))
           | FStar_Pervasives_Native.None  ->
               let uu____3135 =
                 let uu____3136 = FStar_Tactics_Types.goal_env goal  in
                 let uu____3137 = FStar_Tactics_Types.goal_type goal  in
                 tts uu____3136 uu____3137  in
               fail1 "goal is not an arrow (%s)" uu____3135)
       in
    FStar_All.pipe_left (wrap_err "intro") uu____3037
  
let (intro_rec :
  unit ->
    (FStar_Syntax_Syntax.binder,FStar_Syntax_Syntax.binder)
      FStar_Pervasives_Native.tuple2 tac)
  =
  fun uu____3152  ->
    let uu____3159 = cur_goal ()  in
    bind uu____3159
      (fun goal  ->
         FStar_Util.print_string
           "WARNING (intro_rec): calling this is known to cause normalizer loops\n";
         FStar_Util.print_string
           "WARNING (intro_rec): proceed at your own risk...\n";
         (let uu____3176 =
            let uu____3183 = FStar_Tactics_Types.goal_type goal  in
            FStar_Syntax_Util.arrow_one uu____3183  in
          match uu____3176 with
          | FStar_Pervasives_Native.Some (b,c) ->
              let uu____3196 =
                let uu____3197 = FStar_Syntax_Util.is_total_comp c  in
                Prims.op_Negation uu____3197  in
              if uu____3196
              then fail "Codomain is effectful"
              else
                (let bv =
                   let uu____3210 = FStar_Tactics_Types.goal_type goal  in
                   FStar_Syntax_Syntax.gen_bv "__recf"
                     FStar_Pervasives_Native.None uu____3210
                    in
                 let bs =
                   let uu____3218 = FStar_Syntax_Syntax.mk_binder bv  in
                   [uu____3218; b]  in
                 let env' =
                   let uu____3236 = FStar_Tactics_Types.goal_env goal  in
                   FStar_TypeChecker_Env.push_binders uu____3236 bs  in
                 let uu____3237 =
                   let uu____3244 = comp_to_typ c  in
                   new_uvar "intro_rec" env' uu____3244  in
                 bind uu____3237
                   (fun uu____3263  ->
                      match uu____3263 with
                      | (u,ctx_uvar_u) ->
                          let lb =
                            let uu____3277 =
                              FStar_Tactics_Types.goal_type goal  in
                            let uu____3280 =
                              FStar_Syntax_Util.abs [b] u
                                FStar_Pervasives_Native.None
                               in
                            FStar_Syntax_Util.mk_letbinding
                              (FStar_Util.Inl bv) [] uu____3277
                              FStar_Parser_Const.effect_Tot_lid uu____3280 []
                              FStar_Range.dummyRange
                             in
                          let body = FStar_Syntax_Syntax.bv_to_name bv  in
                          let uu____3294 =
                            FStar_Syntax_Subst.close_let_rec [lb] body  in
                          (match uu____3294 with
                           | (lbs,body1) ->
                               let tm =
                                 let uu____3316 =
                                   let uu____3317 =
                                     FStar_Tactics_Types.goal_witness goal
                                      in
                                   uu____3317.FStar_Syntax_Syntax.pos  in
                                 FStar_Syntax_Syntax.mk
                                   (FStar_Syntax_Syntax.Tm_let
                                      ((true, lbs), body1))
                                   FStar_Pervasives_Native.None uu____3316
                                  in
                               let uu____3330 = set_solution goal tm  in
                               bind uu____3330
                                 (fun uu____3339  ->
                                    let uu____3340 =
                                      let uu____3343 =
                                        bnorm_goal
                                          (let uu___124_3346 = goal  in
                                           {
                                             FStar_Tactics_Types.goal_main_env
                                               =
                                               (uu___124_3346.FStar_Tactics_Types.goal_main_env);
                                             FStar_Tactics_Types.goal_ctx_uvar
                                               = ctx_uvar_u;
                                             FStar_Tactics_Types.opts =
                                               (uu___124_3346.FStar_Tactics_Types.opts);
                                             FStar_Tactics_Types.is_guard =
                                               (uu___124_3346.FStar_Tactics_Types.is_guard)
                                           })
                                         in
                                      replace_cur uu____3343  in
                                    bind uu____3340
                                      (fun uu____3353  ->
                                         let uu____3354 =
                                           let uu____3359 =
                                             FStar_Syntax_Syntax.mk_binder bv
                                              in
                                           (uu____3359, b)  in
                                         ret uu____3354)))))
          | FStar_Pervasives_Native.None  ->
              let uu____3368 =
                let uu____3369 = FStar_Tactics_Types.goal_env goal  in
                let uu____3370 = FStar_Tactics_Types.goal_type goal  in
                tts uu____3369 uu____3370  in
              fail1 "intro_rec: goal is not an arrow (%s)" uu____3368))
  
let (norm : FStar_Syntax_Embeddings.norm_step Prims.list -> unit tac) =
  fun s  ->
    let uu____3388 = cur_goal ()  in
    bind uu____3388
      (fun goal  ->
         mlog
           (fun uu____3395  ->
              let uu____3396 =
                let uu____3397 = FStar_Tactics_Types.goal_witness goal  in
                FStar_Syntax_Print.term_to_string uu____3397  in
              FStar_Util.print1 "norm: witness = %s\n" uu____3396)
           (fun uu____3402  ->
              let steps =
                let uu____3406 = FStar_TypeChecker_Normalize.tr_norm_steps s
                   in
                FStar_List.append
                  [FStar_TypeChecker_Normalize.Reify;
                  FStar_TypeChecker_Normalize.UnfoldTac] uu____3406
                 in
              let t =
                let uu____3410 = FStar_Tactics_Types.goal_env goal  in
                let uu____3411 = FStar_Tactics_Types.goal_type goal  in
                normalize steps uu____3410 uu____3411  in
              let uu____3412 = FStar_Tactics_Types.goal_with_type goal t  in
              replace_cur uu____3412))
  
let (norm_term_env :
  env ->
    FStar_Syntax_Embeddings.norm_step Prims.list ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term tac)
  =
  fun e  ->
    fun s  ->
      fun t  ->
        let uu____3436 =
          mlog
            (fun uu____3441  ->
               let uu____3442 = FStar_Syntax_Print.term_to_string t  in
               FStar_Util.print1 "norm_term: tm = %s\n" uu____3442)
            (fun uu____3444  ->
               bind get
                 (fun ps  ->
                    let opts =
                      match ps.FStar_Tactics_Types.goals with
                      | g::uu____3450 -> g.FStar_Tactics_Types.opts
                      | uu____3453 -> FStar_Options.peek ()  in
                    mlog
                      (fun uu____3458  ->
                         let uu____3459 =
                           tts ps.FStar_Tactics_Types.main_context t  in
                         FStar_Util.print1 "norm_term_env: t = %s\n"
                           uu____3459)
                      (fun uu____3462  ->
                         let uu____3463 = __tc e t  in
                         bind uu____3463
                           (fun uu____3484  ->
                              match uu____3484 with
                              | (t1,uu____3494,uu____3495) ->
                                  let steps =
                                    let uu____3499 =
                                      FStar_TypeChecker_Normalize.tr_norm_steps
                                        s
                                       in
                                    FStar_List.append
                                      [FStar_TypeChecker_Normalize.Reify;
                                      FStar_TypeChecker_Normalize.UnfoldTac]
                                      uu____3499
                                     in
                                  let t2 =
                                    normalize steps
                                      ps.FStar_Tactics_Types.main_context t1
                                     in
                                  ret t2))))
           in
        FStar_All.pipe_left (wrap_err "norm_term") uu____3436
  
let (refine_intro : unit -> unit tac) =
  fun uu____3513  ->
    let uu____3516 =
      let uu____3519 = cur_goal ()  in
      bind uu____3519
        (fun g  ->
           let uu____3526 =
             let uu____3537 = FStar_Tactics_Types.goal_env g  in
             let uu____3538 = FStar_Tactics_Types.goal_type g  in
             FStar_TypeChecker_Rel.base_and_refinement uu____3537 uu____3538
              in
           match uu____3526 with
           | (uu____3541,FStar_Pervasives_Native.None ) ->
               fail "not a refinement"
           | (t,FStar_Pervasives_Native.Some (bv,phi)) ->
               let g1 = FStar_Tactics_Types.goal_with_type g t  in
               let uu____3566 =
                 let uu____3571 =
                   let uu____3576 =
                     let uu____3577 = FStar_Syntax_Syntax.mk_binder bv  in
                     [uu____3577]  in
                   FStar_Syntax_Subst.open_term uu____3576 phi  in
                 match uu____3571 with
                 | (bvs,phi1) ->
                     let uu____3596 =
                       let uu____3597 = FStar_List.hd bvs  in
                       FStar_Pervasives_Native.fst uu____3597  in
                     (uu____3596, phi1)
                  in
               (match uu____3566 with
                | (bv1,phi1) ->
                    let uu____3610 =
                      let uu____3613 = FStar_Tactics_Types.goal_env g  in
                      let uu____3614 =
                        let uu____3615 =
                          let uu____3618 =
                            let uu____3619 =
                              let uu____3626 =
                                FStar_Tactics_Types.goal_witness g  in
                              (bv1, uu____3626)  in
                            FStar_Syntax_Syntax.NT uu____3619  in
                          [uu____3618]  in
                        FStar_Syntax_Subst.subst uu____3615 phi1  in
                      mk_irrelevant_goal "refine_intro refinement" uu____3613
                        uu____3614 g.FStar_Tactics_Types.opts
                       in
                    bind uu____3610
                      (fun g2  ->
                         bind __dismiss
                           (fun uu____3634  -> add_goals [g1; g2]))))
       in
    FStar_All.pipe_left (wrap_err "refine_intro") uu____3516
  
let (__exact_now : Prims.bool -> FStar_Syntax_Syntax.term -> unit tac) =
  fun set_expected_typ1  ->
    fun t  ->
      let uu____3653 = cur_goal ()  in
      bind uu____3653
        (fun goal  ->
           let env =
             if set_expected_typ1
             then
               let uu____3661 = FStar_Tactics_Types.goal_env goal  in
               let uu____3662 = FStar_Tactics_Types.goal_type goal  in
               FStar_TypeChecker_Env.set_expected_typ uu____3661 uu____3662
             else FStar_Tactics_Types.goal_env goal  in
           let uu____3664 = __tc env t  in
           bind uu____3664
             (fun uu____3683  ->
                match uu____3683 with
                | (t1,typ,guard) ->
                    mlog
                      (fun uu____3698  ->
                         let uu____3699 =
                           let uu____3700 = FStar_Tactics_Types.goal_env goal
                              in
                           tts uu____3700 typ  in
                         let uu____3701 =
                           let uu____3702 = FStar_Tactics_Types.goal_env goal
                              in
                           FStar_TypeChecker_Rel.guard_to_string uu____3702
                             guard
                            in
                         FStar_Util.print2
                           "__exact_now: got type %s\n__exact_now: and guard %s\n"
                           uu____3699 uu____3701)
                      (fun uu____3705  ->
                         let uu____3706 =
                           let uu____3709 = FStar_Tactics_Types.goal_env goal
                              in
                           proc_guard "__exact typing" uu____3709 guard
                             goal.FStar_Tactics_Types.opts
                            in
                         bind uu____3706
                           (fun uu____3711  ->
                              mlog
                                (fun uu____3715  ->
                                   let uu____3716 =
                                     let uu____3717 =
                                       FStar_Tactics_Types.goal_env goal  in
                                     tts uu____3717 typ  in
                                   let uu____3718 =
                                     let uu____3719 =
                                       FStar_Tactics_Types.goal_env goal  in
                                     let uu____3720 =
                                       FStar_Tactics_Types.goal_type goal  in
                                     tts uu____3719 uu____3720  in
                                   FStar_Util.print2
                                     "__exact_now: unifying %s and %s\n"
                                     uu____3716 uu____3718)
                                (fun uu____3723  ->
                                   let uu____3724 =
                                     let uu____3727 =
                                       FStar_Tactics_Types.goal_env goal  in
                                     let uu____3728 =
                                       FStar_Tactics_Types.goal_type goal  in
                                     do_unify uu____3727 typ uu____3728  in
                                   bind uu____3724
                                     (fun b  ->
                                        if b
                                        then solve goal t1
                                        else
                                          (let uu____3734 =
                                             let uu____3735 =
                                               FStar_Tactics_Types.goal_env
                                                 goal
                                                in
                                             tts uu____3735 t1  in
                                           let uu____3736 =
                                             let uu____3737 =
                                               FStar_Tactics_Types.goal_env
                                                 goal
                                                in
                                             tts uu____3737 typ  in
                                           let uu____3738 =
                                             let uu____3739 =
                                               FStar_Tactics_Types.goal_env
                                                 goal
                                                in
                                             let uu____3740 =
                                               FStar_Tactics_Types.goal_type
                                                 goal
                                                in
                                             tts uu____3739 uu____3740  in
                                           let uu____3741 =
                                             let uu____3742 =
                                               FStar_Tactics_Types.goal_env
                                                 goal
                                                in
                                             let uu____3743 =
                                               FStar_Tactics_Types.goal_witness
                                                 goal
                                                in
                                             tts uu____3742 uu____3743  in
                                           fail4
                                             "%s : %s does not exactly solve the goal %s (witness = %s)"
                                             uu____3734 uu____3736 uu____3738
                                             uu____3741)))))))
  
let (t_exact : Prims.bool -> FStar_Syntax_Syntax.term -> unit tac) =
  fun set_expected_typ1  ->
    fun tm  ->
      let uu____3758 =
        mlog
          (fun uu____3763  ->
             let uu____3764 = FStar_Syntax_Print.term_to_string tm  in
             FStar_Util.print1 "t_exact: tm = %s\n" uu____3764)
          (fun uu____3767  ->
             let uu____3768 =
               let uu____3775 = __exact_now set_expected_typ1 tm  in
               trytac' uu____3775  in
             bind uu____3768
               (fun uu___89_3784  ->
                  match uu___89_3784 with
                  | FStar_Util.Inr r -> ret ()
                  | FStar_Util.Inl e ->
                      mlog
                        (fun uu____3794  ->
                           FStar_Util.print_string
                             "__exact_now failed, trying refine...\n")
                        (fun uu____3797  ->
                           let uu____3798 =
                             let uu____3805 =
                               let uu____3808 =
                                 norm [FStar_Syntax_Embeddings.Delta]  in
                               bind uu____3808
                                 (fun uu____3813  ->
                                    let uu____3814 = refine_intro ()  in
                                    bind uu____3814
                                      (fun uu____3818  ->
                                         __exact_now set_expected_typ1 tm))
                                in
                             trytac' uu____3805  in
                           bind uu____3798
                             (fun uu___88_3825  ->
                                match uu___88_3825 with
                                | FStar_Util.Inr r -> ret ()
                                | FStar_Util.Inl uu____3833 -> fail e))))
         in
      FStar_All.pipe_left (wrap_err "exact") uu____3758
  
let (uvar_free_in_goal :
  FStar_Syntax_Syntax.uvar -> FStar_Tactics_Types.goal -> Prims.bool) =
  fun u  ->
    fun g  ->
      if g.FStar_Tactics_Types.is_guard
      then false
      else
        (let free_uvars =
           let uu____3862 =
             let uu____3865 =
               let uu____3868 = FStar_Tactics_Types.goal_type g  in
               FStar_Syntax_Free.uvars uu____3868  in
             FStar_Util.set_elements uu____3865  in
           FStar_List.map (fun u1  -> u1.FStar_Syntax_Syntax.ctx_uvar_head)
             uu____3862
            in
         FStar_List.existsML (FStar_Syntax_Unionfind.equiv u) free_uvars)
  
let (uvar_free :
  FStar_Syntax_Syntax.uvar -> FStar_Tactics_Types.proofstate -> Prims.bool) =
  fun u  ->
    fun ps  ->
      FStar_List.existsML (uvar_free_in_goal u) ps.FStar_Tactics_Types.goals
  
let rec mapM : 'a 'b . ('a -> 'b tac) -> 'a Prims.list -> 'b Prims.list tac =
  fun f  ->
    fun l  ->
      match l with
      | [] -> ret []
      | x::xs ->
          let uu____3946 = f x  in
          bind uu____3946
            (fun y  ->
               let uu____3954 = mapM f xs  in
               bind uu____3954 (fun ys  -> ret (y :: ys)))
  
exception NoUnif 
let (uu___is_NoUnif : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with | NoUnif  -> true | uu____3974 -> false
  
let rec (__apply :
  Prims.bool ->
    FStar_Syntax_Syntax.term -> FStar_Reflection_Data.typ -> unit tac)
  =
  fun uopt  ->
    fun tm  ->
      fun typ  ->
        let uu____3994 = cur_goal ()  in
        bind uu____3994
          (fun goal  ->
             mlog
               (fun uu____4001  ->
                  let uu____4002 = FStar_Syntax_Print.term_to_string tm  in
                  FStar_Util.print1 ">>> Calling __exact(%s)\n" uu____4002)
               (fun uu____4005  ->
                  let uu____4006 =
                    let uu____4011 =
                      let uu____4014 = t_exact false tm  in
                      with_policy FStar_Tactics_Types.Force uu____4014  in
                    trytac_exn uu____4011  in
                  bind uu____4006
                    (fun uu___90_4021  ->
                       match uu___90_4021 with
                       | FStar_Pervasives_Native.Some r -> ret ()
                       | FStar_Pervasives_Native.None  ->
                           mlog
                             (fun uu____4029  ->
                                let uu____4030 =
                                  FStar_Syntax_Print.term_to_string typ  in
                                FStar_Util.print1 ">>> typ = %s\n" uu____4030)
                             (fun uu____4033  ->
                                let uu____4034 =
                                  FStar_Syntax_Util.arrow_one typ  in
                                match uu____4034 with
                                | FStar_Pervasives_Native.None  ->
                                    FStar_Exn.raise NoUnif
                                | FStar_Pervasives_Native.Some ((bv,aq),c) ->
                                    mlog
                                      (fun uu____4058  ->
                                         let uu____4059 =
                                           FStar_Syntax_Print.binder_to_string
                                             (bv, aq)
                                            in
                                         FStar_Util.print1
                                           "__apply: pushing binder %s\n"
                                           uu____4059)
                                      (fun uu____4062  ->
                                         let uu____4063 =
                                           let uu____4064 =
                                             FStar_Syntax_Util.is_total_comp
                                               c
                                              in
                                           Prims.op_Negation uu____4064  in
                                         if uu____4063
                                         then
                                           fail "apply: not total codomain"
                                         else
                                           (let uu____4068 =
                                              let uu____4075 =
                                                FStar_Tactics_Types.goal_env
                                                  goal
                                                 in
                                              new_uvar "apply" uu____4075
                                                bv.FStar_Syntax_Syntax.sort
                                               in
                                            bind uu____4068
                                              (fun uu____4086  ->
                                                 match uu____4086 with
                                                 | (u,_goal_u) ->
                                                     let tm' =
                                                       FStar_Syntax_Syntax.mk_Tm_app
                                                         tm [(u, aq)]
                                                         FStar_Pervasives_Native.None
                                                         tm.FStar_Syntax_Syntax.pos
                                                        in
                                                     let typ' =
                                                       let uu____4113 =
                                                         comp_to_typ c  in
                                                       FStar_All.pipe_left
                                                         (FStar_Syntax_Subst.subst
                                                            [FStar_Syntax_Syntax.NT
                                                               (bv, u)])
                                                         uu____4113
                                                        in
                                                     let uu____4116 =
                                                       __apply uopt tm' typ'
                                                        in
                                                     bind uu____4116
                                                       (fun uu____4124  ->
                                                          let u1 =
                                                            let uu____4126 =
                                                              FStar_Tactics_Types.goal_env
                                                                goal
                                                               in
                                                            bnorm uu____4126
                                                              u
                                                             in
                                                          let uu____4127 =
                                                            let uu____4128 =
                                                              let uu____4131
                                                                =
                                                                let uu____4132
                                                                  =
                                                                  FStar_Syntax_Util.head_and_args
                                                                    u1
                                                                   in
                                                                FStar_Pervasives_Native.fst
                                                                  uu____4132
                                                                 in
                                                              FStar_Syntax_Subst.compress
                                                                uu____4131
                                                               in
                                                            uu____4128.FStar_Syntax_Syntax.n
                                                             in
                                                          match uu____4127
                                                          with
                                                          | FStar_Syntax_Syntax.Tm_uvar
                                                              (goal_u,uu____4160)
                                                              ->
                                                              bind get
                                                                (fun ps  ->
                                                                   let uu____4184
                                                                    =
                                                                    uopt &&
                                                                    (uvar_free
                                                                    goal_u.FStar_Syntax_Syntax.ctx_uvar_head
                                                                    ps)  in
                                                                   if
                                                                    uu____4184
                                                                   then
                                                                    ret ()
                                                                   else
                                                                    (let uu____4188
                                                                    =
                                                                    let uu____4191
                                                                    =
                                                                    bnorm_goal
                                                                    (let uu___125_4194
                                                                    = goal
                                                                     in
                                                                    {
                                                                    FStar_Tactics_Types.goal_main_env
                                                                    =
                                                                    (uu___125_4194.FStar_Tactics_Types.goal_main_env);
                                                                    FStar_Tactics_Types.goal_ctx_uvar
                                                                    = goal_u;
                                                                    FStar_Tactics_Types.opts
                                                                    =
                                                                    (uu___125_4194.FStar_Tactics_Types.opts);
                                                                    FStar_Tactics_Types.is_guard
                                                                    = false
                                                                    })  in
                                                                    [uu____4191]
                                                                     in
                                                                    add_goals
                                                                    uu____4188))
                                                          | t -> ret ()))))))))
  
let try_unif : 'a . 'a tac -> 'a tac -> 'a tac =
  fun t  ->
    fun t'  -> mk_tac (fun ps  -> try run t ps with | NoUnif  -> run t' ps)
  
let (apply : Prims.bool -> FStar_Syntax_Syntax.term -> unit tac) =
  fun uopt  ->
    fun tm  ->
      let uu____4249 =
        mlog
          (fun uu____4254  ->
             let uu____4255 = FStar_Syntax_Print.term_to_string tm  in
             FStar_Util.print1 "apply: tm = %s\n" uu____4255)
          (fun uu____4258  ->
             let uu____4259 = cur_goal ()  in
             bind uu____4259
               (fun goal  ->
                  let uu____4265 =
                    let uu____4274 = FStar_Tactics_Types.goal_env goal  in
                    __tc uu____4274 tm  in
                  bind uu____4265
                    (fun uu____4288  ->
                       match uu____4288 with
                       | (tm1,typ,guard) ->
                           let typ1 =
                             let uu____4301 =
                               FStar_Tactics_Types.goal_env goal  in
                             bnorm uu____4301 typ  in
                           let uu____4302 =
                             let uu____4305 =
                               let uu____4308 = __apply uopt tm1 typ1  in
                               bind uu____4308
                                 (fun uu____4313  ->
                                    let uu____4314 =
                                      FStar_Tactics_Types.goal_env goal  in
                                    proc_guard "apply guard" uu____4314 guard
                                      goal.FStar_Tactics_Types.opts)
                                in
                             focus uu____4305  in
                           let uu____4315 =
                             let uu____4318 =
                               let uu____4319 =
                                 FStar_Tactics_Types.goal_env goal  in
                               tts uu____4319 tm1  in
                             let uu____4320 =
                               let uu____4321 =
                                 FStar_Tactics_Types.goal_env goal  in
                               tts uu____4321 typ1  in
                             let uu____4322 =
                               let uu____4323 =
                                 FStar_Tactics_Types.goal_env goal  in
                               let uu____4324 =
                                 FStar_Tactics_Types.goal_type goal  in
                               tts uu____4323 uu____4324  in
                             fail3
                               "Cannot instantiate %s (of type %s) to match goal (%s)"
                               uu____4318 uu____4320 uu____4322
                              in
                           try_unif uu____4302 uu____4315)))
         in
      FStar_All.pipe_left (wrap_err "apply") uu____4249
  
let (lemma_or_sq :
  FStar_Syntax_Syntax.comp ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun c  ->
    let ct = FStar_Syntax_Util.comp_to_comp_typ_nouniv c  in
    let uu____4347 =
      FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
        FStar_Parser_Const.effect_Lemma_lid
       in
    if uu____4347
    then
      let uu____4354 =
        match ct.FStar_Syntax_Syntax.effect_args with
        | pre::post::uu____4373 ->
            ((FStar_Pervasives_Native.fst pre),
              (FStar_Pervasives_Native.fst post))
        | uu____4414 -> failwith "apply_lemma: impossible: not a lemma"  in
      match uu____4354 with
      | (pre,post) ->
          let post1 =
            let uu____4450 =
              let uu____4459 =
                FStar_Syntax_Syntax.as_arg FStar_Syntax_Util.exp_unit  in
              [uu____4459]  in
            FStar_Syntax_Util.mk_app post uu____4450  in
          FStar_Pervasives_Native.Some (pre, post1)
    else
      (let uu____4483 =
         FStar_Syntax_Util.is_pure_effect ct.FStar_Syntax_Syntax.effect_name
          in
       if uu____4483
       then
         let uu____4490 =
           FStar_Syntax_Util.un_squash ct.FStar_Syntax_Syntax.result_typ  in
         FStar_Util.map_opt uu____4490
           (fun post  -> (FStar_Syntax_Util.t_true, post))
       else FStar_Pervasives_Native.None)
  
let (apply_lemma : FStar_Syntax_Syntax.term -> unit tac) =
  fun tm  ->
    let uu____4523 =
      let uu____4526 =
        mlog
          (fun uu____4531  ->
             let uu____4532 = FStar_Syntax_Print.term_to_string tm  in
             FStar_Util.print1 "apply_lemma: tm = %s\n" uu____4532)
          (fun uu____4536  ->
             let is_unit_t t =
               let uu____4543 =
                 let uu____4544 = FStar_Syntax_Subst.compress t  in
                 uu____4544.FStar_Syntax_Syntax.n  in
               match uu____4543 with
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.unit_lid
                   -> true
               | uu____4548 -> false  in
             let uu____4549 = cur_goal ()  in
             bind uu____4549
               (fun goal  ->
                  let uu____4555 =
                    let uu____4564 = FStar_Tactics_Types.goal_env goal  in
                    __tc uu____4564 tm  in
                  bind uu____4555
                    (fun uu____4579  ->
                       match uu____4579 with
                       | (tm1,t,guard) ->
                           let uu____4591 =
                             FStar_Syntax_Util.arrow_formals_comp t  in
                           (match uu____4591 with
                            | (bs,comp) ->
                                let uu____4618 = lemma_or_sq comp  in
                                (match uu____4618 with
                                 | FStar_Pervasives_Native.None  ->
                                     fail "not a lemma or squashed function"
                                 | FStar_Pervasives_Native.Some (pre,post) ->
                                     let uu____4637 =
                                       FStar_List.fold_left
                                         (fun uu____4679  ->
                                            fun uu____4680  ->
                                              match (uu____4679, uu____4680)
                                              with
                                              | ((uvs,guard1,subst1),(b,aq))
                                                  ->
                                                  let b_t =
                                                    FStar_Syntax_Subst.subst
                                                      subst1
                                                      b.FStar_Syntax_Syntax.sort
                                                     in
                                                  let uu____4771 =
                                                    is_unit_t b_t  in
                                                  if uu____4771
                                                  then
                                                    (((FStar_Syntax_Util.exp_unit,
                                                        aq) :: uvs), guard1,
                                                      ((FStar_Syntax_Syntax.NT
                                                          (b,
                                                            FStar_Syntax_Util.exp_unit))
                                                      :: subst1))
                                                  else
                                                    (let uu____4801 =
                                                       let uu____4814 =
                                                         let uu____4815 =
                                                           FStar_Tactics_Types.goal_type
                                                             goal
                                                            in
                                                         uu____4815.FStar_Syntax_Syntax.pos
                                                          in
                                                       let uu____4818 =
                                                         FStar_Tactics_Types.goal_env
                                                           goal
                                                          in
                                                       FStar_TypeChecker_Util.new_implicit_var
                                                         "apply_lemma"
                                                         uu____4814
                                                         uu____4818 b_t
                                                        in
                                                     match uu____4801 with
                                                     | (u,uu____4834,g_u) ->
                                                         let uu____4848 =
                                                           FStar_TypeChecker_Rel.conj_guard
                                                             guard1 g_u
                                                            in
                                                         (((u, aq) :: uvs),
                                                           uu____4848,
                                                           ((FStar_Syntax_Syntax.NT
                                                               (b, u)) ::
                                                           subst1))))
                                         ([], guard, []) bs
                                        in
                                     (match uu____4637 with
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
                                          let uu____4909 =
                                            let uu____4912 =
                                              FStar_Tactics_Types.goal_env
                                                goal
                                               in
                                            let uu____4913 =
                                              FStar_Syntax_Util.mk_squash
                                                FStar_Syntax_Syntax.U_zero
                                                post1
                                               in
                                            let uu____4914 =
                                              FStar_Tactics_Types.goal_type
                                                goal
                                               in
                                            do_unify uu____4912 uu____4913
                                              uu____4914
                                             in
                                          bind uu____4909
                                            (fun b  ->
                                               if Prims.op_Negation b
                                               then
                                                 let uu____4922 =
                                                   let uu____4923 =
                                                     FStar_Tactics_Types.goal_env
                                                       goal
                                                      in
                                                   tts uu____4923 tm1  in
                                                 let uu____4924 =
                                                   let uu____4925 =
                                                     FStar_Tactics_Types.goal_env
                                                       goal
                                                      in
                                                   let uu____4926 =
                                                     FStar_Syntax_Util.mk_squash
                                                       FStar_Syntax_Syntax.U_zero
                                                       post1
                                                      in
                                                   tts uu____4925 uu____4926
                                                    in
                                                 let uu____4927 =
                                                   let uu____4928 =
                                                     FStar_Tactics_Types.goal_env
                                                       goal
                                                      in
                                                   let uu____4929 =
                                                     FStar_Tactics_Types.goal_type
                                                       goal
                                                      in
                                                   tts uu____4928 uu____4929
                                                    in
                                                 fail3
                                                   "Cannot instantiate lemma %s (with postcondition: %s) to match goal (%s)"
                                                   uu____4922 uu____4924
                                                   uu____4927
                                               else
                                                 (let uu____4931 =
                                                    add_implicits
                                                      implicits.FStar_TypeChecker_Env.implicits
                                                     in
                                                  bind uu____4931
                                                    (fun uu____4936  ->
                                                       let uu____4937 =
                                                         solve' goal
                                                           FStar_Syntax_Util.exp_unit
                                                          in
                                                       bind uu____4937
                                                         (fun uu____4945  ->
                                                            let is_free_uvar
                                                              uv t1 =
                                                              let free_uvars
                                                                =
                                                                let uu____4970
                                                                  =
                                                                  let uu____4973
                                                                    =
                                                                    FStar_Syntax_Free.uvars
                                                                    t1  in
                                                                  FStar_Util.set_elements
                                                                    uu____4973
                                                                   in
                                                                FStar_List.map
                                                                  (fun x  ->
                                                                    x.FStar_Syntax_Syntax.ctx_uvar_head)
                                                                  uu____4970
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
                                                                   let uu____5008
                                                                    =
                                                                    FStar_Tactics_Types.goal_type
                                                                    g'  in
                                                                   is_free_uvar
                                                                    uv
                                                                    uu____5008)
                                                                goals
                                                               in
                                                            let checkone t1
                                                              goals =
                                                              let uu____5024
                                                                =
                                                                FStar_Syntax_Util.head_and_args
                                                                  t1
                                                                 in
                                                              match uu____5024
                                                              with
                                                              | (hd1,uu____5040)
                                                                  ->
                                                                  (match 
                                                                    hd1.FStar_Syntax_Syntax.n
                                                                   with
                                                                   | 
                                                                   FStar_Syntax_Syntax.Tm_uvar
                                                                    (uv,uu____5062)
                                                                    ->
                                                                    appears
                                                                    uv.FStar_Syntax_Syntax.ctx_uvar_head
                                                                    goals
                                                                   | 
                                                                   uu____5083
                                                                    -> false)
                                                               in
                                                            let uu____5084 =
                                                              FStar_All.pipe_right
                                                                implicits.FStar_TypeChecker_Env.implicits
                                                                (mapM
                                                                   (fun
                                                                    uu____5147
                                                                     ->
                                                                    match uu____5147
                                                                    with
                                                                    | 
                                                                    (_msg,term,ctx_uvar,_range)
                                                                    ->
                                                                    let uu____5170
                                                                    =
                                                                    FStar_Syntax_Util.head_and_args
                                                                    term  in
                                                                    (match uu____5170
                                                                    with
                                                                    | 
                                                                    (hd1,uu____5196)
                                                                    ->
                                                                    let uu____5217
                                                                    =
                                                                    let uu____5218
                                                                    =
                                                                    FStar_Syntax_Subst.compress
                                                                    hd1  in
                                                                    uu____5218.FStar_Syntax_Syntax.n
                                                                     in
                                                                    (match uu____5217
                                                                    with
                                                                    | 
                                                                    FStar_Syntax_Syntax.Tm_uvar
                                                                    (ctx_uvar1,uu____5232)
                                                                    ->
                                                                    let goal1
                                                                    =
                                                                    bnorm_goal
                                                                    (let uu___128_5256
                                                                    = goal
                                                                     in
                                                                    {
                                                                    FStar_Tactics_Types.goal_main_env
                                                                    =
                                                                    (uu___128_5256.FStar_Tactics_Types.goal_main_env);
                                                                    FStar_Tactics_Types.goal_ctx_uvar
                                                                    =
                                                                    ctx_uvar1;
                                                                    FStar_Tactics_Types.opts
                                                                    =
                                                                    (uu___128_5256.FStar_Tactics_Types.opts);
                                                                    FStar_Tactics_Types.is_guard
                                                                    =
                                                                    (uu___128_5256.FStar_Tactics_Types.is_guard)
                                                                    })  in
                                                                    ret
                                                                    ([goal1],
                                                                    [])
                                                                    | 
                                                                    uu____5269
                                                                    ->
                                                                    let env =
                                                                    let uu___129_5271
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    goal  in
                                                                    {
                                                                    FStar_TypeChecker_Env.solver
                                                                    =
                                                                    (uu___129_5271.FStar_TypeChecker_Env.solver);
                                                                    FStar_TypeChecker_Env.range
                                                                    =
                                                                    (uu___129_5271.FStar_TypeChecker_Env.range);
                                                                    FStar_TypeChecker_Env.curmodule
                                                                    =
                                                                    (uu___129_5271.FStar_TypeChecker_Env.curmodule);
                                                                    FStar_TypeChecker_Env.gamma
                                                                    =
                                                                    (ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_gamma);
                                                                    FStar_TypeChecker_Env.gamma_sig
                                                                    =
                                                                    (uu___129_5271.FStar_TypeChecker_Env.gamma_sig);
                                                                    FStar_TypeChecker_Env.gamma_cache
                                                                    =
                                                                    (uu___129_5271.FStar_TypeChecker_Env.gamma_cache);
                                                                    FStar_TypeChecker_Env.modules
                                                                    =
                                                                    (uu___129_5271.FStar_TypeChecker_Env.modules);
                                                                    FStar_TypeChecker_Env.expected_typ
                                                                    =
                                                                    (uu___129_5271.FStar_TypeChecker_Env.expected_typ);
                                                                    FStar_TypeChecker_Env.sigtab
                                                                    =
                                                                    (uu___129_5271.FStar_TypeChecker_Env.sigtab);
                                                                    FStar_TypeChecker_Env.is_pattern
                                                                    =
                                                                    (uu___129_5271.FStar_TypeChecker_Env.is_pattern);
                                                                    FStar_TypeChecker_Env.instantiate_imp
                                                                    =
                                                                    (uu___129_5271.FStar_TypeChecker_Env.instantiate_imp);
                                                                    FStar_TypeChecker_Env.effects
                                                                    =
                                                                    (uu___129_5271.FStar_TypeChecker_Env.effects);
                                                                    FStar_TypeChecker_Env.generalize
                                                                    =
                                                                    (uu___129_5271.FStar_TypeChecker_Env.generalize);
                                                                    FStar_TypeChecker_Env.letrecs
                                                                    =
                                                                    (uu___129_5271.FStar_TypeChecker_Env.letrecs);
                                                                    FStar_TypeChecker_Env.top_level
                                                                    =
                                                                    (uu___129_5271.FStar_TypeChecker_Env.top_level);
                                                                    FStar_TypeChecker_Env.check_uvars
                                                                    =
                                                                    (uu___129_5271.FStar_TypeChecker_Env.check_uvars);
                                                                    FStar_TypeChecker_Env.use_eq
                                                                    =
                                                                    (uu___129_5271.FStar_TypeChecker_Env.use_eq);
                                                                    FStar_TypeChecker_Env.is_iface
                                                                    =
                                                                    (uu___129_5271.FStar_TypeChecker_Env.is_iface);
                                                                    FStar_TypeChecker_Env.admit
                                                                    =
                                                                    (uu___129_5271.FStar_TypeChecker_Env.admit);
                                                                    FStar_TypeChecker_Env.lax
                                                                    =
                                                                    (uu___129_5271.FStar_TypeChecker_Env.lax);
                                                                    FStar_TypeChecker_Env.lax_universes
                                                                    =
                                                                    (uu___129_5271.FStar_TypeChecker_Env.lax_universes);
                                                                    FStar_TypeChecker_Env.failhard
                                                                    =
                                                                    (uu___129_5271.FStar_TypeChecker_Env.failhard);
                                                                    FStar_TypeChecker_Env.nosynth
                                                                    =
                                                                    (uu___129_5271.FStar_TypeChecker_Env.nosynth);
                                                                    FStar_TypeChecker_Env.uvar_subtyping
                                                                    =
                                                                    (uu___129_5271.FStar_TypeChecker_Env.uvar_subtyping);
                                                                    FStar_TypeChecker_Env.tc_term
                                                                    =
                                                                    (uu___129_5271.FStar_TypeChecker_Env.tc_term);
                                                                    FStar_TypeChecker_Env.type_of
                                                                    =
                                                                    (uu___129_5271.FStar_TypeChecker_Env.type_of);
                                                                    FStar_TypeChecker_Env.universe_of
                                                                    =
                                                                    (uu___129_5271.FStar_TypeChecker_Env.universe_of);
                                                                    FStar_TypeChecker_Env.check_type_of
                                                                    =
                                                                    (uu___129_5271.FStar_TypeChecker_Env.check_type_of);
                                                                    FStar_TypeChecker_Env.use_bv_sorts
                                                                    =
                                                                    (uu___129_5271.FStar_TypeChecker_Env.use_bv_sorts);
                                                                    FStar_TypeChecker_Env.qtbl_name_and_index
                                                                    =
                                                                    (uu___129_5271.FStar_TypeChecker_Env.qtbl_name_and_index);
                                                                    FStar_TypeChecker_Env.normalized_eff_names
                                                                    =
                                                                    (uu___129_5271.FStar_TypeChecker_Env.normalized_eff_names);
                                                                    FStar_TypeChecker_Env.proof_ns
                                                                    =
                                                                    (uu___129_5271.FStar_TypeChecker_Env.proof_ns);
                                                                    FStar_TypeChecker_Env.synth_hook
                                                                    =
                                                                    (uu___129_5271.FStar_TypeChecker_Env.synth_hook);
                                                                    FStar_TypeChecker_Env.splice
                                                                    =
                                                                    (uu___129_5271.FStar_TypeChecker_Env.splice);
                                                                    FStar_TypeChecker_Env.is_native_tactic
                                                                    =
                                                                    (uu___129_5271.FStar_TypeChecker_Env.is_native_tactic);
                                                                    FStar_TypeChecker_Env.identifier_info
                                                                    =
                                                                    (uu___129_5271.FStar_TypeChecker_Env.identifier_info);
                                                                    FStar_TypeChecker_Env.tc_hooks
                                                                    =
                                                                    (uu___129_5271.FStar_TypeChecker_Env.tc_hooks);
                                                                    FStar_TypeChecker_Env.dsenv
                                                                    =
                                                                    (uu___129_5271.FStar_TypeChecker_Env.dsenv);
                                                                    FStar_TypeChecker_Env.dep_graph
                                                                    =
                                                                    (uu___129_5271.FStar_TypeChecker_Env.dep_graph)
                                                                    }  in
                                                                    let g_typ
                                                                    =
                                                                    let uu____5273
                                                                    =
                                                                    FStar_Options.__temp_fast_implicits
                                                                    ()  in
                                                                    if
                                                                    uu____5273
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
                                                                    let uu____5276
                                                                    =
                                                                    let uu____5283
                                                                    =
                                                                    FStar_TypeChecker_Env.set_expected_typ
                                                                    env
                                                                    ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_typ
                                                                     in
                                                                    env.FStar_TypeChecker_Env.type_of
                                                                    uu____5283
                                                                    term1  in
                                                                    match uu____5276
                                                                    with
                                                                    | 
                                                                    (uu____5284,uu____5285,g_typ)
                                                                    -> g_typ)
                                                                     in
                                                                    let uu____5287
                                                                    =
                                                                    let uu____5292
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    goal  in
                                                                    goal_from_guard
                                                                    "apply_lemma solved arg"
                                                                    uu____5292
                                                                    g_typ
                                                                    goal.FStar_Tactics_Types.opts
                                                                     in
                                                                    bind
                                                                    uu____5287
                                                                    (fun
                                                                    uu___91_5304
                                                                     ->
                                                                    match uu___91_5304
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.None
                                                                     ->
                                                                    ret
                                                                    ([], [])
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    g ->
                                                                    ret
                                                                    ([], [g]))))))
                                                               in
                                                            bind uu____5084
                                                              (fun goals_  ->
                                                                 let sub_goals
                                                                   =
                                                                   let uu____5372
                                                                    =
                                                                    FStar_List.map
                                                                    FStar_Pervasives_Native.fst
                                                                    goals_
                                                                     in
                                                                   FStar_List.flatten
                                                                    uu____5372
                                                                    in
                                                                 let smt_goals
                                                                   =
                                                                   let uu____5394
                                                                    =
                                                                    FStar_List.map
                                                                    FStar_Pervasives_Native.snd
                                                                    goals_
                                                                     in
                                                                   FStar_List.flatten
                                                                    uu____5394
                                                                    in
                                                                 let rec filter'
                                                                   f xs =
                                                                   match xs
                                                                   with
                                                                   | 
                                                                   [] -> []
                                                                   | 
                                                                   x::xs1 ->
                                                                    let uu____5455
                                                                    = f x xs1
                                                                     in
                                                                    if
                                                                    uu____5455
                                                                    then
                                                                    let uu____5458
                                                                    =
                                                                    filter' f
                                                                    xs1  in x
                                                                    ::
                                                                    uu____5458
                                                                    else
                                                                    filter' f
                                                                    xs1
                                                                    in
                                                                 let sub_goals1
                                                                   =
                                                                   filter'
                                                                    (fun g 
                                                                    ->
                                                                    fun goals
                                                                     ->
                                                                    let uu____5472
                                                                    =
                                                                    let uu____5473
                                                                    =
                                                                    FStar_Tactics_Types.goal_witness
                                                                    g  in
                                                                    checkone
                                                                    uu____5473
                                                                    goals  in
                                                                    Prims.op_Negation
                                                                    uu____5472)
                                                                    sub_goals
                                                                    in
                                                                 let uu____5474
                                                                   =
                                                                   let uu____5477
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    goal  in
                                                                   proc_guard
                                                                    "apply_lemma guard"
                                                                    uu____5477
                                                                    guard
                                                                    goal.FStar_Tactics_Types.opts
                                                                    in
                                                                 bind
                                                                   uu____5474
                                                                   (fun
                                                                    uu____5480
                                                                     ->
                                                                    let uu____5481
                                                                    =
                                                                    let uu____5484
                                                                    =
                                                                    let uu____5485
                                                                    =
                                                                    let uu____5486
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    goal  in
                                                                    let uu____5487
                                                                    =
                                                                    FStar_Syntax_Util.mk_squash
                                                                    FStar_Syntax_Syntax.U_zero
                                                                    pre1  in
                                                                    istrivial
                                                                    uu____5486
                                                                    uu____5487
                                                                     in
                                                                    Prims.op_Negation
                                                                    uu____5485
                                                                     in
                                                                    if
                                                                    uu____5484
                                                                    then
                                                                    let uu____5490
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    goal  in
                                                                    add_irrelevant_goal
                                                                    "apply_lemma precondition"
                                                                    uu____5490
                                                                    pre1
                                                                    goal.FStar_Tactics_Types.opts
                                                                    else
                                                                    ret ()
                                                                     in
                                                                    bind
                                                                    uu____5481
                                                                    (fun
                                                                    uu____5494
                                                                     ->
                                                                    let uu____5495
                                                                    =
                                                                    add_smt_goals
                                                                    smt_goals
                                                                     in
                                                                    bind
                                                                    uu____5495
                                                                    (fun
                                                                    uu____5499
                                                                     ->
                                                                    add_goals
                                                                    sub_goals1))))))))))))))
         in
      focus uu____4526  in
    FStar_All.pipe_left (wrap_err "apply_lemma") uu____4523
  
let (destruct_eq' :
  FStar_Reflection_Data.typ ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun typ  ->
    let uu____5521 = FStar_Syntax_Util.destruct_typ_as_formula typ  in
    match uu____5521 with
    | FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn
        (l,uu____5531::(e1,uu____5533)::(e2,uu____5535)::[])) when
        FStar_Ident.lid_equals l FStar_Parser_Const.eq2_lid ->
        FStar_Pervasives_Native.Some (e1, e2)
    | uu____5578 -> FStar_Pervasives_Native.None
  
let (destruct_eq :
  FStar_Reflection_Data.typ ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun typ  ->
    let uu____5602 = destruct_eq' typ  in
    match uu____5602 with
    | FStar_Pervasives_Native.Some t -> FStar_Pervasives_Native.Some t
    | FStar_Pervasives_Native.None  ->
        let uu____5632 = FStar_Syntax_Util.un_squash typ  in
        (match uu____5632 with
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
        let uu____5694 = FStar_TypeChecker_Env.pop_bv e1  in
        match uu____5694 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (bv',e') ->
            if FStar_Syntax_Syntax.bv_eq bvar bv'
            then FStar_Pervasives_Native.Some (e', [])
            else
              (let uu____5742 = aux e'  in
               FStar_Util.map_opt uu____5742
                 (fun uu____5766  ->
                    match uu____5766 with | (e'',bvs) -> (e'', (bv' :: bvs))))
         in
      let uu____5787 = aux e  in
      FStar_Util.map_opt uu____5787
        (fun uu____5811  ->
           match uu____5811 with | (e',bvs) -> (e', (FStar_List.rev bvs)))
  
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
          let uu____5878 =
            let uu____5887 = FStar_Tactics_Types.goal_env g  in
            split_env b1 uu____5887  in
          FStar_Util.map_opt uu____5878
            (fun uu____5902  ->
               match uu____5902 with
               | (e0,bvs) ->
                   let s1 bv =
                     let uu___130_5921 = bv  in
                     let uu____5922 =
                       FStar_Syntax_Subst.subst s bv.FStar_Syntax_Syntax.sort
                        in
                     {
                       FStar_Syntax_Syntax.ppname =
                         (uu___130_5921.FStar_Syntax_Syntax.ppname);
                       FStar_Syntax_Syntax.index =
                         (uu___130_5921.FStar_Syntax_Syntax.index);
                       FStar_Syntax_Syntax.sort = uu____5922
                     }  in
                   let bvs1 = FStar_List.map s1 bvs  in
                   let new_env = push_bvs e0 (b2 :: bvs1)  in
                   let new_goal =
                     let uu___131_5930 = g.FStar_Tactics_Types.goal_ctx_uvar
                        in
                     let uu____5931 =
                       FStar_TypeChecker_Env.all_binders new_env  in
                     let uu____5938 =
                       let uu____5941 = FStar_Tactics_Types.goal_type g  in
                       FStar_Syntax_Subst.subst s uu____5941  in
                     {
                       FStar_Syntax_Syntax.ctx_uvar_head =
                         (uu___131_5930.FStar_Syntax_Syntax.ctx_uvar_head);
                       FStar_Syntax_Syntax.ctx_uvar_gamma =
                         (new_env.FStar_TypeChecker_Env.gamma);
                       FStar_Syntax_Syntax.ctx_uvar_binders = uu____5931;
                       FStar_Syntax_Syntax.ctx_uvar_typ = uu____5938;
                       FStar_Syntax_Syntax.ctx_uvar_reason =
                         (uu___131_5930.FStar_Syntax_Syntax.ctx_uvar_reason);
                       FStar_Syntax_Syntax.ctx_uvar_should_check =
                         (uu___131_5930.FStar_Syntax_Syntax.ctx_uvar_should_check);
                       FStar_Syntax_Syntax.ctx_uvar_range =
                         (uu___131_5930.FStar_Syntax_Syntax.ctx_uvar_range)
                     }  in
                   let uu___132_5942 = g  in
                   {
                     FStar_Tactics_Types.goal_main_env =
                       (uu___132_5942.FStar_Tactics_Types.goal_main_env);
                     FStar_Tactics_Types.goal_ctx_uvar = new_goal;
                     FStar_Tactics_Types.opts =
                       (uu___132_5942.FStar_Tactics_Types.opts);
                     FStar_Tactics_Types.is_guard =
                       (uu___132_5942.FStar_Tactics_Types.is_guard)
                   })
  
let (rewrite : FStar_Syntax_Syntax.binder -> unit tac) =
  fun h  ->
    let uu____5952 =
      let uu____5955 = cur_goal ()  in
      bind uu____5955
        (fun goal  ->
           let uu____5963 = h  in
           match uu____5963 with
           | (bv,uu____5967) ->
               mlog
                 (fun uu____5971  ->
                    let uu____5972 = FStar_Syntax_Print.bv_to_string bv  in
                    let uu____5973 =
                      let uu____5974 = FStar_Tactics_Types.goal_env goal  in
                      tts uu____5974 bv.FStar_Syntax_Syntax.sort  in
                    FStar_Util.print2 "+++Rewrite %s : %s\n" uu____5972
                      uu____5973)
                 (fun uu____5977  ->
                    let uu____5978 =
                      let uu____5987 = FStar_Tactics_Types.goal_env goal  in
                      split_env bv uu____5987  in
                    match uu____5978 with
                    | FStar_Pervasives_Native.None  ->
                        fail "binder not found in environment"
                    | FStar_Pervasives_Native.Some (e0,bvs) ->
                        let uu____6008 =
                          destruct_eq bv.FStar_Syntax_Syntax.sort  in
                        (match uu____6008 with
                         | FStar_Pervasives_Native.Some (x,e) ->
                             let uu____6023 =
                               let uu____6024 = FStar_Syntax_Subst.compress x
                                  in
                               uu____6024.FStar_Syntax_Syntax.n  in
                             (match uu____6023 with
                              | FStar_Syntax_Syntax.Tm_name x1 ->
                                  let s = [FStar_Syntax_Syntax.NT (x1, e)]
                                     in
                                  let s1 bv1 =
                                    let uu___133_6041 = bv1  in
                                    let uu____6042 =
                                      FStar_Syntax_Subst.subst s
                                        bv1.FStar_Syntax_Syntax.sort
                                       in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___133_6041.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___133_6041.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = uu____6042
                                    }  in
                                  let bvs1 = FStar_List.map s1 bvs  in
                                  let new_env = push_bvs e0 (bv :: bvs1)  in
                                  let new_goal =
                                    let uu___134_6050 =
                                      goal.FStar_Tactics_Types.goal_ctx_uvar
                                       in
                                    let uu____6051 =
                                      FStar_TypeChecker_Env.all_binders
                                        new_env
                                       in
                                    let uu____6058 =
                                      let uu____6061 =
                                        FStar_Tactics_Types.goal_type goal
                                         in
                                      FStar_Syntax_Subst.subst s uu____6061
                                       in
                                    {
                                      FStar_Syntax_Syntax.ctx_uvar_head =
                                        (uu___134_6050.FStar_Syntax_Syntax.ctx_uvar_head);
                                      FStar_Syntax_Syntax.ctx_uvar_gamma =
                                        (new_env.FStar_TypeChecker_Env.gamma);
                                      FStar_Syntax_Syntax.ctx_uvar_binders =
                                        uu____6051;
                                      FStar_Syntax_Syntax.ctx_uvar_typ =
                                        uu____6058;
                                      FStar_Syntax_Syntax.ctx_uvar_reason =
                                        (uu___134_6050.FStar_Syntax_Syntax.ctx_uvar_reason);
                                      FStar_Syntax_Syntax.ctx_uvar_should_check
                                        =
                                        (uu___134_6050.FStar_Syntax_Syntax.ctx_uvar_should_check);
                                      FStar_Syntax_Syntax.ctx_uvar_range =
                                        (uu___134_6050.FStar_Syntax_Syntax.ctx_uvar_range)
                                    }  in
                                  replace_cur
                                    (let uu___135_6064 = goal  in
                                     {
                                       FStar_Tactics_Types.goal_main_env =
                                         (uu___135_6064.FStar_Tactics_Types.goal_main_env);
                                       FStar_Tactics_Types.goal_ctx_uvar =
                                         new_goal;
                                       FStar_Tactics_Types.opts =
                                         (uu___135_6064.FStar_Tactics_Types.opts);
                                       FStar_Tactics_Types.is_guard =
                                         (uu___135_6064.FStar_Tactics_Types.is_guard)
                                     })
                              | uu____6065 ->
                                  fail
                                    "Not an equality hypothesis with a variable on the LHS")
                         | uu____6066 -> fail "Not an equality hypothesis")))
       in
    FStar_All.pipe_left (wrap_err "rewrite") uu____5952
  
let (rename_to : FStar_Syntax_Syntax.binder -> Prims.string -> unit tac) =
  fun b  ->
    fun s  ->
      let uu____6091 =
        let uu____6094 = cur_goal ()  in
        bind uu____6094
          (fun goal  ->
             let uu____6105 = b  in
             match uu____6105 with
             | (bv,uu____6109) ->
                 let bv' =
                   let uu____6111 =
                     let uu___136_6112 = bv  in
                     let uu____6113 =
                       FStar_Ident.mk_ident
                         (s,
                           ((bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange))
                        in
                     {
                       FStar_Syntax_Syntax.ppname = uu____6113;
                       FStar_Syntax_Syntax.index =
                         (uu___136_6112.FStar_Syntax_Syntax.index);
                       FStar_Syntax_Syntax.sort =
                         (uu___136_6112.FStar_Syntax_Syntax.sort)
                     }  in
                   FStar_Syntax_Syntax.freshen_bv uu____6111  in
                 let s1 =
                   let uu____6117 =
                     let uu____6118 =
                       let uu____6125 = FStar_Syntax_Syntax.bv_to_name bv'
                          in
                       (bv, uu____6125)  in
                     FStar_Syntax_Syntax.NT uu____6118  in
                   [uu____6117]  in
                 let uu____6130 = subst_goal bv bv' s1 goal  in
                 (match uu____6130 with
                  | FStar_Pervasives_Native.None  ->
                      fail "binder not found in environment"
                  | FStar_Pervasives_Native.Some goal1 -> replace_cur goal1))
         in
      FStar_All.pipe_left (wrap_err "rename_to") uu____6091
  
let (binder_retype : FStar_Syntax_Syntax.binder -> unit tac) =
  fun b  ->
    let uu____6149 =
      let uu____6152 = cur_goal ()  in
      bind uu____6152
        (fun goal  ->
           let uu____6161 = b  in
           match uu____6161 with
           | (bv,uu____6165) ->
               let uu____6166 =
                 let uu____6175 = FStar_Tactics_Types.goal_env goal  in
                 split_env bv uu____6175  in
               (match uu____6166 with
                | FStar_Pervasives_Native.None  ->
                    fail "binder is not present in environment"
                | FStar_Pervasives_Native.Some (e0,bvs) ->
                    let uu____6196 = FStar_Syntax_Util.type_u ()  in
                    (match uu____6196 with
                     | (ty,u) ->
                         let uu____6205 = new_uvar "binder_retype" e0 ty  in
                         bind uu____6205
                           (fun uu____6223  ->
                              match uu____6223 with
                              | (t',u_t') ->
                                  let bv'' =
                                    let uu___137_6233 = bv  in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___137_6233.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___137_6233.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = t'
                                    }  in
                                  let s =
                                    let uu____6237 =
                                      let uu____6238 =
                                        let uu____6245 =
                                          FStar_Syntax_Syntax.bv_to_name bv''
                                           in
                                        (bv, uu____6245)  in
                                      FStar_Syntax_Syntax.NT uu____6238  in
                                    [uu____6237]  in
                                  let bvs1 =
                                    FStar_List.map
                                      (fun b1  ->
                                         let uu___138_6257 = b1  in
                                         let uu____6258 =
                                           FStar_Syntax_Subst.subst s
                                             b1.FStar_Syntax_Syntax.sort
                                            in
                                         {
                                           FStar_Syntax_Syntax.ppname =
                                             (uu___138_6257.FStar_Syntax_Syntax.ppname);
                                           FStar_Syntax_Syntax.index =
                                             (uu___138_6257.FStar_Syntax_Syntax.index);
                                           FStar_Syntax_Syntax.sort =
                                             uu____6258
                                         }) bvs
                                     in
                                  let env' = push_bvs e0 (bv'' :: bvs1)  in
                                  bind __dismiss
                                    (fun uu____6265  ->
                                       let new_goal =
                                         let uu____6267 =
                                           FStar_Tactics_Types.goal_with_env
                                             goal env'
                                            in
                                         let uu____6268 =
                                           let uu____6269 =
                                             FStar_Tactics_Types.goal_type
                                               goal
                                              in
                                           FStar_Syntax_Subst.subst s
                                             uu____6269
                                            in
                                         FStar_Tactics_Types.goal_with_type
                                           uu____6267 uu____6268
                                          in
                                       let uu____6270 = add_goals [new_goal]
                                          in
                                       bind uu____6270
                                         (fun uu____6275  ->
                                            let uu____6276 =
                                              FStar_Syntax_Util.mk_eq2
                                                (FStar_Syntax_Syntax.U_succ u)
                                                ty
                                                bv.FStar_Syntax_Syntax.sort
                                                t'
                                               in
                                            add_irrelevant_goal
                                              "binder_retype equation" e0
                                              uu____6276
                                              goal.FStar_Tactics_Types.opts))))))
       in
    FStar_All.pipe_left (wrap_err "binder_retype") uu____6149
  
let (norm_binder_type :
  FStar_Syntax_Embeddings.norm_step Prims.list ->
    FStar_Syntax_Syntax.binder -> unit tac)
  =
  fun s  ->
    fun b  ->
      let uu____6299 =
        let uu____6302 = cur_goal ()  in
        bind uu____6302
          (fun goal  ->
             let uu____6311 = b  in
             match uu____6311 with
             | (bv,uu____6315) ->
                 let uu____6316 =
                   let uu____6325 = FStar_Tactics_Types.goal_env goal  in
                   split_env bv uu____6325  in
                 (match uu____6316 with
                  | FStar_Pervasives_Native.None  ->
                      fail "binder is not present in environment"
                  | FStar_Pervasives_Native.Some (e0,bvs) ->
                      let steps =
                        let uu____6349 =
                          FStar_TypeChecker_Normalize.tr_norm_steps s  in
                        FStar_List.append
                          [FStar_TypeChecker_Normalize.Reify;
                          FStar_TypeChecker_Normalize.UnfoldTac] uu____6349
                         in
                      let sort' =
                        normalize steps e0 bv.FStar_Syntax_Syntax.sort  in
                      let bv' =
                        let uu___139_6354 = bv  in
                        {
                          FStar_Syntax_Syntax.ppname =
                            (uu___139_6354.FStar_Syntax_Syntax.ppname);
                          FStar_Syntax_Syntax.index =
                            (uu___139_6354.FStar_Syntax_Syntax.index);
                          FStar_Syntax_Syntax.sort = sort'
                        }  in
                      let env' = push_bvs e0 (bv' :: bvs)  in
                      let uu____6356 =
                        FStar_Tactics_Types.goal_with_env goal env'  in
                      replace_cur uu____6356))
         in
      FStar_All.pipe_left (wrap_err "norm_binder_type") uu____6299
  
let (revert : unit -> unit tac) =
  fun uu____6367  ->
    let uu____6370 = cur_goal ()  in
    bind uu____6370
      (fun goal  ->
         let uu____6376 =
           let uu____6383 = FStar_Tactics_Types.goal_env goal  in
           FStar_TypeChecker_Env.pop_bv uu____6383  in
         match uu____6376 with
         | FStar_Pervasives_Native.None  ->
             fail "Cannot revert; empty context"
         | FStar_Pervasives_Native.Some (x,env') ->
             let typ' =
               let uu____6399 =
                 let uu____6402 = FStar_Tactics_Types.goal_type goal  in
                 FStar_Syntax_Syntax.mk_Total uu____6402  in
               FStar_Syntax_Util.arrow [(x, FStar_Pervasives_Native.None)]
                 uu____6399
                in
             let uu____6411 = new_uvar "revert" env' typ'  in
             bind uu____6411
               (fun uu____6426  ->
                  match uu____6426 with
                  | (r,u_r) ->
                      let uu____6435 =
                        let uu____6438 =
                          let uu____6439 =
                            let uu____6440 =
                              FStar_Tactics_Types.goal_type goal  in
                            uu____6440.FStar_Syntax_Syntax.pos  in
                          let uu____6443 =
                            let uu____6448 =
                              let uu____6449 =
                                let uu____6456 =
                                  FStar_Syntax_Syntax.bv_to_name x  in
                                FStar_Syntax_Syntax.as_arg uu____6456  in
                              [uu____6449]  in
                            FStar_Syntax_Syntax.mk_Tm_app r uu____6448  in
                          uu____6443 FStar_Pervasives_Native.None uu____6439
                           in
                        set_solution goal uu____6438  in
                      bind uu____6435
                        (fun uu____6473  ->
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
      let uu____6485 = FStar_Syntax_Free.names t  in
      FStar_Util.set_mem bv uu____6485
  
let rec (clear : FStar_Syntax_Syntax.binder -> unit tac) =
  fun b  ->
    let bv = FStar_Pervasives_Native.fst b  in
    let uu____6498 = cur_goal ()  in
    bind uu____6498
      (fun goal  ->
         mlog
           (fun uu____6506  ->
              let uu____6507 = FStar_Syntax_Print.binder_to_string b  in
              let uu____6508 =
                let uu____6509 =
                  let uu____6510 =
                    let uu____6517 = FStar_Tactics_Types.goal_env goal  in
                    FStar_TypeChecker_Env.all_binders uu____6517  in
                  FStar_All.pipe_right uu____6510 FStar_List.length  in
                FStar_All.pipe_right uu____6509 FStar_Util.string_of_int  in
              FStar_Util.print2 "Clear of (%s), env has %s binders\n"
                uu____6507 uu____6508)
           (fun uu____6530  ->
              let uu____6531 =
                let uu____6540 = FStar_Tactics_Types.goal_env goal  in
                split_env bv uu____6540  in
              match uu____6531 with
              | FStar_Pervasives_Native.None  ->
                  fail "Cannot clear; binder not in environment"
              | FStar_Pervasives_Native.Some (e',bvs) ->
                  let rec check1 bvs1 =
                    match bvs1 with
                    | [] -> ret ()
                    | bv'::bvs2 ->
                        let uu____6579 =
                          free_in bv bv'.FStar_Syntax_Syntax.sort  in
                        if uu____6579
                        then
                          let uu____6582 =
                            let uu____6583 =
                              FStar_Syntax_Print.bv_to_string bv'  in
                            FStar_Util.format1
                              "Cannot clear; binder present in the type of %s"
                              uu____6583
                             in
                          fail uu____6582
                        else check1 bvs2
                     in
                  let uu____6585 =
                    let uu____6586 = FStar_Tactics_Types.goal_type goal  in
                    free_in bv uu____6586  in
                  if uu____6585
                  then fail "Cannot clear; binder present in goal"
                  else
                    (let uu____6590 = check1 bvs  in
                     bind uu____6590
                       (fun uu____6596  ->
                          let env' = push_bvs e' bvs  in
                          let uu____6598 =
                            let uu____6605 =
                              FStar_Tactics_Types.goal_type goal  in
                            new_uvar "clear.witness" env' uu____6605  in
                          bind uu____6598
                            (fun uu____6614  ->
                               match uu____6614 with
                               | (ut,uvar_ut) ->
                                   let uu____6623 = set_solution goal ut  in
                                   bind uu____6623
                                     (fun uu____6628  ->
                                        let uu____6629 =
                                          FStar_Tactics_Types.mk_goal env'
                                            uvar_ut
                                            goal.FStar_Tactics_Types.opts
                                            goal.FStar_Tactics_Types.is_guard
                                           in
                                        replace_cur uu____6629))))))
  
let (clear_top : unit -> unit tac) =
  fun uu____6636  ->
    let uu____6639 = cur_goal ()  in
    bind uu____6639
      (fun goal  ->
         let uu____6645 =
           let uu____6652 = FStar_Tactics_Types.goal_env goal  in
           FStar_TypeChecker_Env.pop_bv uu____6652  in
         match uu____6645 with
         | FStar_Pervasives_Native.None  ->
             fail "Cannot clear; empty context"
         | FStar_Pervasives_Native.Some (x,uu____6660) ->
             let uu____6665 = FStar_Syntax_Syntax.mk_binder x  in
             clear uu____6665)
  
let (prune : Prims.string -> unit tac) =
  fun s  ->
    let uu____6675 = cur_goal ()  in
    bind uu____6675
      (fun g  ->
         let ctx = FStar_Tactics_Types.goal_env g  in
         let ctx' =
           let uu____6685 = FStar_Ident.path_of_text s  in
           FStar_TypeChecker_Env.rem_proof_ns ctx uu____6685  in
         let g' = FStar_Tactics_Types.goal_with_env g ctx'  in
         bind __dismiss (fun uu____6688  -> add_goals [g']))
  
let (addns : Prims.string -> unit tac) =
  fun s  ->
    let uu____6698 = cur_goal ()  in
    bind uu____6698
      (fun g  ->
         let ctx = FStar_Tactics_Types.goal_env g  in
         let ctx' =
           let uu____6708 = FStar_Ident.path_of_text s  in
           FStar_TypeChecker_Env.add_proof_ns ctx uu____6708  in
         let g' = FStar_Tactics_Types.goal_with_env g ctx'  in
         bind __dismiss (fun uu____6711  -> add_goals [g']))
  
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
            let uu____6751 = FStar_Syntax_Subst.compress t  in
            uu____6751.FStar_Syntax_Syntax.n  in
          let uu____6754 =
            if d = FStar_Tactics_Types.TopDown
            then
              f env
                (let uu___143_6760 = t  in
                 {
                   FStar_Syntax_Syntax.n = tn;
                   FStar_Syntax_Syntax.pos =
                     (uu___143_6760.FStar_Syntax_Syntax.pos);
                   FStar_Syntax_Syntax.vars =
                     (uu___143_6760.FStar_Syntax_Syntax.vars)
                 })
            else ret t  in
          bind uu____6754
            (fun t1  ->
               let ff = tac_fold_env d f env  in
               let tn1 =
                 let uu____6776 =
                   let uu____6777 = FStar_Syntax_Subst.compress t1  in
                   uu____6777.FStar_Syntax_Syntax.n  in
                 match uu____6776 with
                 | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
                     let uu____6804 = ff hd1  in
                     bind uu____6804
                       (fun hd2  ->
                          let fa uu____6826 =
                            match uu____6826 with
                            | (a,q) ->
                                let uu____6839 = ff a  in
                                bind uu____6839 (fun a1  -> ret (a1, q))
                             in
                          let uu____6852 = mapM fa args  in
                          bind uu____6852
                            (fun args1  ->
                               ret (FStar_Syntax_Syntax.Tm_app (hd2, args1))))
                 | FStar_Syntax_Syntax.Tm_abs (bs,t2,k) ->
                     let uu____6918 = FStar_Syntax_Subst.open_term bs t2  in
                     (match uu____6918 with
                      | (bs1,t') ->
                          let uu____6927 =
                            let uu____6930 =
                              FStar_TypeChecker_Env.push_binders env bs1  in
                            tac_fold_env d f uu____6930 t'  in
                          bind uu____6927
                            (fun t''  ->
                               let uu____6934 =
                                 let uu____6935 =
                                   let uu____6952 =
                                     FStar_Syntax_Subst.close_binders bs1  in
                                   let uu____6959 =
                                     FStar_Syntax_Subst.close bs1 t''  in
                                   (uu____6952, uu____6959, k)  in
                                 FStar_Syntax_Syntax.Tm_abs uu____6935  in
                               ret uu____6934))
                 | FStar_Syntax_Syntax.Tm_arrow (bs,k) -> ret tn
                 | FStar_Syntax_Syntax.Tm_match (hd1,brs) ->
                     let uu____7028 = ff hd1  in
                     bind uu____7028
                       (fun hd2  ->
                          let ffb br =
                            let uu____7043 =
                              FStar_Syntax_Subst.open_branch br  in
                            match uu____7043 with
                            | (pat,w,e) ->
                                let bvs = FStar_Syntax_Syntax.pat_bvs pat  in
                                let ff1 =
                                  let uu____7075 =
                                    FStar_TypeChecker_Env.push_bvs env bvs
                                     in
                                  tac_fold_env d f uu____7075  in
                                let uu____7076 = ff1 e  in
                                bind uu____7076
                                  (fun e1  ->
                                     let br1 =
                                       FStar_Syntax_Subst.close_branch
                                         (pat, w, e1)
                                        in
                                     ret br1)
                             in
                          let uu____7091 = mapM ffb brs  in
                          bind uu____7091
                            (fun brs1  ->
                               ret (FStar_Syntax_Syntax.Tm_match (hd2, brs1))))
                 | FStar_Syntax_Syntax.Tm_let
                     ((false
                       ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inl bv;
                          FStar_Syntax_Syntax.lbunivs = uu____7135;
                          FStar_Syntax_Syntax.lbtyp = uu____7136;
                          FStar_Syntax_Syntax.lbeff = uu____7137;
                          FStar_Syntax_Syntax.lbdef = def;
                          FStar_Syntax_Syntax.lbattrs = uu____7139;
                          FStar_Syntax_Syntax.lbpos = uu____7140;_}::[]),e)
                     ->
                     let lb =
                       let uu____7165 =
                         let uu____7166 = FStar_Syntax_Subst.compress t1  in
                         uu____7166.FStar_Syntax_Syntax.n  in
                       match uu____7165 with
                       | FStar_Syntax_Syntax.Tm_let
                           ((false ,lb::[]),uu____7170) -> lb
                       | uu____7183 -> failwith "impossible"  in
                     let fflb lb1 =
                       let uu____7192 = ff lb1.FStar_Syntax_Syntax.lbdef  in
                       bind uu____7192
                         (fun def1  ->
                            ret
                              (let uu___140_7198 = lb1  in
                               {
                                 FStar_Syntax_Syntax.lbname =
                                   (uu___140_7198.FStar_Syntax_Syntax.lbname);
                                 FStar_Syntax_Syntax.lbunivs =
                                   (uu___140_7198.FStar_Syntax_Syntax.lbunivs);
                                 FStar_Syntax_Syntax.lbtyp =
                                   (uu___140_7198.FStar_Syntax_Syntax.lbtyp);
                                 FStar_Syntax_Syntax.lbeff =
                                   (uu___140_7198.FStar_Syntax_Syntax.lbeff);
                                 FStar_Syntax_Syntax.lbdef = def1;
                                 FStar_Syntax_Syntax.lbattrs =
                                   (uu___140_7198.FStar_Syntax_Syntax.lbattrs);
                                 FStar_Syntax_Syntax.lbpos =
                                   (uu___140_7198.FStar_Syntax_Syntax.lbpos)
                               }))
                        in
                     let uu____7199 = fflb lb  in
                     bind uu____7199
                       (fun lb1  ->
                          let uu____7209 =
                            let uu____7214 =
                              let uu____7215 =
                                FStar_Syntax_Syntax.mk_binder bv  in
                              [uu____7215]  in
                            FStar_Syntax_Subst.open_term uu____7214 e  in
                          match uu____7209 with
                          | (bs,e1) ->
                              let ff1 =
                                let uu____7239 =
                                  FStar_TypeChecker_Env.push_binders env bs
                                   in
                                tac_fold_env d f uu____7239  in
                              let uu____7240 = ff1 e1  in
                              bind uu____7240
                                (fun e2  ->
                                   let e3 = FStar_Syntax_Subst.close bs e2
                                      in
                                   ret
                                     (FStar_Syntax_Syntax.Tm_let
                                        ((false, [lb1]), e3))))
                 | FStar_Syntax_Syntax.Tm_let ((true ,lbs),e) ->
                     let fflb lb =
                       let uu____7281 = ff lb.FStar_Syntax_Syntax.lbdef  in
                       bind uu____7281
                         (fun def  ->
                            ret
                              (let uu___141_7287 = lb  in
                               {
                                 FStar_Syntax_Syntax.lbname =
                                   (uu___141_7287.FStar_Syntax_Syntax.lbname);
                                 FStar_Syntax_Syntax.lbunivs =
                                   (uu___141_7287.FStar_Syntax_Syntax.lbunivs);
                                 FStar_Syntax_Syntax.lbtyp =
                                   (uu___141_7287.FStar_Syntax_Syntax.lbtyp);
                                 FStar_Syntax_Syntax.lbeff =
                                   (uu___141_7287.FStar_Syntax_Syntax.lbeff);
                                 FStar_Syntax_Syntax.lbdef = def;
                                 FStar_Syntax_Syntax.lbattrs =
                                   (uu___141_7287.FStar_Syntax_Syntax.lbattrs);
                                 FStar_Syntax_Syntax.lbpos =
                                   (uu___141_7287.FStar_Syntax_Syntax.lbpos)
                               }))
                        in
                     let uu____7288 = FStar_Syntax_Subst.open_let_rec lbs e
                        in
                     (match uu____7288 with
                      | (lbs1,e1) ->
                          let uu____7303 = mapM fflb lbs1  in
                          bind uu____7303
                            (fun lbs2  ->
                               let uu____7315 = ff e1  in
                               bind uu____7315
                                 (fun e2  ->
                                    let uu____7323 =
                                      FStar_Syntax_Subst.close_let_rec lbs2
                                        e2
                                       in
                                    match uu____7323 with
                                    | (lbs3,e3) ->
                                        ret
                                          (FStar_Syntax_Syntax.Tm_let
                                             ((true, lbs3), e3)))))
                 | FStar_Syntax_Syntax.Tm_ascribed (t2,asc,eff) ->
                     let uu____7391 = ff t2  in
                     bind uu____7391
                       (fun t3  ->
                          ret
                            (FStar_Syntax_Syntax.Tm_ascribed (t3, asc, eff)))
                 | FStar_Syntax_Syntax.Tm_meta (t2,m) ->
                     let uu____7422 = ff t2  in
                     bind uu____7422
                       (fun t3  -> ret (FStar_Syntax_Syntax.Tm_meta (t3, m)))
                 | uu____7429 -> ret tn  in
               bind tn1
                 (fun tn2  ->
                    let t' =
                      let uu___142_7436 = t1  in
                      {
                        FStar_Syntax_Syntax.n = tn2;
                        FStar_Syntax_Syntax.pos =
                          (uu___142_7436.FStar_Syntax_Syntax.pos);
                        FStar_Syntax_Syntax.vars =
                          (uu___142_7436.FStar_Syntax_Syntax.vars)
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
            let uu____7473 = FStar_TypeChecker_TcTerm.tc_term env t  in
            match uu____7473 with
            | (t1,lcomp,g) ->
                let uu____7485 =
                  (let uu____7488 =
                     FStar_Syntax_Util.is_pure_or_ghost_lcomp lcomp  in
                   Prims.op_Negation uu____7488) ||
                    (let uu____7490 = FStar_TypeChecker_Rel.is_trivial g  in
                     Prims.op_Negation uu____7490)
                   in
                if uu____7485
                then ret t1
                else
                  (let rewrite_eq =
                     let typ = lcomp.FStar_Syntax_Syntax.res_typ  in
                     let uu____7498 = new_uvar "pointwise_rec" env typ  in
                     bind uu____7498
                       (fun uu____7514  ->
                          match uu____7514 with
                          | (ut,uvar_ut) ->
                              (log ps
                                 (fun uu____7527  ->
                                    let uu____7528 =
                                      FStar_Syntax_Print.term_to_string t1
                                       in
                                    let uu____7529 =
                                      FStar_Syntax_Print.term_to_string ut
                                       in
                                    FStar_Util.print2
                                      "Pointwise_rec: making equality\n\t%s ==\n\t%s\n"
                                      uu____7528 uu____7529);
                               (let uu____7530 =
                                  let uu____7533 =
                                    let uu____7534 =
                                      FStar_TypeChecker_TcTerm.universe_of
                                        env typ
                                       in
                                    FStar_Syntax_Util.mk_eq2 uu____7534 typ
                                      t1 ut
                                     in
                                  add_irrelevant_goal
                                    "pointwise_rec equation" env uu____7533
                                    opts
                                   in
                                bind uu____7530
                                  (fun uu____7537  ->
                                     let uu____7538 =
                                       bind tau
                                         (fun uu____7544  ->
                                            let ut1 =
                                              FStar_TypeChecker_Normalize.reduce_uvar_solutions
                                                env ut
                                               in
                                            log ps
                                              (fun uu____7550  ->
                                                 let uu____7551 =
                                                   FStar_Syntax_Print.term_to_string
                                                     t1
                                                    in
                                                 let uu____7552 =
                                                   FStar_Syntax_Print.term_to_string
                                                     ut1
                                                    in
                                                 FStar_Util.print2
                                                   "Pointwise_rec: succeeded rewriting\n\t%s to\n\t%s\n"
                                                   uu____7551 uu____7552);
                                            ret ut1)
                                        in
                                     focus uu____7538))))
                      in
                   let uu____7553 = trytac' rewrite_eq  in
                   bind uu____7553
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
          let uu____7751 = FStar_Syntax_Subst.compress t  in
          maybe_continue ctrl uu____7751
            (fun t1  ->
               let uu____7759 =
                 f env
                   (let uu___146_7768 = t1  in
                    {
                      FStar_Syntax_Syntax.n = (t1.FStar_Syntax_Syntax.n);
                      FStar_Syntax_Syntax.pos =
                        (uu___146_7768.FStar_Syntax_Syntax.pos);
                      FStar_Syntax_Syntax.vars =
                        (uu___146_7768.FStar_Syntax_Syntax.vars)
                    })
                  in
               bind uu____7759
                 (fun uu____7784  ->
                    match uu____7784 with
                    | (t2,ctrl1) ->
                        maybe_continue ctrl1 t2
                          (fun t3  ->
                             let uu____7807 =
                               let uu____7808 =
                                 FStar_Syntax_Subst.compress t3  in
                               uu____7808.FStar_Syntax_Syntax.n  in
                             match uu____7807 with
                             | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
                                 let uu____7841 =
                                   ctrl_tac_fold f env ctrl1 hd1  in
                                 bind uu____7841
                                   (fun uu____7866  ->
                                      match uu____7866 with
                                      | (hd2,ctrl2) ->
                                          let ctrl3 = keep_going ctrl2  in
                                          let uu____7882 =
                                            ctrl_tac_fold_args f env ctrl3
                                              args
                                             in
                                          bind uu____7882
                                            (fun uu____7909  ->
                                               match uu____7909 with
                                               | (args1,ctrl4) ->
                                                   ret
                                                     ((let uu___144_7939 = t3
                                                          in
                                                       {
                                                         FStar_Syntax_Syntax.n
                                                           =
                                                           (FStar_Syntax_Syntax.Tm_app
                                                              (hd2, args1));
                                                         FStar_Syntax_Syntax.pos
                                                           =
                                                           (uu___144_7939.FStar_Syntax_Syntax.pos);
                                                         FStar_Syntax_Syntax.vars
                                                           =
                                                           (uu___144_7939.FStar_Syntax_Syntax.vars)
                                                       }), ctrl4)))
                             | FStar_Syntax_Syntax.Tm_abs (bs,t4,k) ->
                                 let uu____7975 =
                                   FStar_Syntax_Subst.open_term bs t4  in
                                 (match uu____7975 with
                                  | (bs1,t') ->
                                      let uu____7990 =
                                        let uu____7997 =
                                          FStar_TypeChecker_Env.push_binders
                                            env bs1
                                           in
                                        ctrl_tac_fold f uu____7997 ctrl1 t'
                                         in
                                      bind uu____7990
                                        (fun uu____8015  ->
                                           match uu____8015 with
                                           | (t'',ctrl2) ->
                                               let uu____8030 =
                                                 let uu____8037 =
                                                   let uu___145_8040 = t4  in
                                                   let uu____8043 =
                                                     let uu____8044 =
                                                       let uu____8061 =
                                                         FStar_Syntax_Subst.close_binders
                                                           bs1
                                                          in
                                                       let uu____8068 =
                                                         FStar_Syntax_Subst.close
                                                           bs1 t''
                                                          in
                                                       (uu____8061,
                                                         uu____8068, k)
                                                        in
                                                     FStar_Syntax_Syntax.Tm_abs
                                                       uu____8044
                                                      in
                                                   {
                                                     FStar_Syntax_Syntax.n =
                                                       uu____8043;
                                                     FStar_Syntax_Syntax.pos
                                                       =
                                                       (uu___145_8040.FStar_Syntax_Syntax.pos);
                                                     FStar_Syntax_Syntax.vars
                                                       =
                                                       (uu___145_8040.FStar_Syntax_Syntax.vars)
                                                   }  in
                                                 (uu____8037, ctrl2)  in
                                               ret uu____8030))
                             | FStar_Syntax_Syntax.Tm_arrow (bs,k) ->
                                 ret (t3, ctrl1)
                             | uu____8115 -> ret (t3, ctrl1))))

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
              let uu____8158 = ctrl_tac_fold f env ctrl t  in
              bind uu____8158
                (fun uu____8182  ->
                   match uu____8182 with
                   | (t1,ctrl1) ->
                       let uu____8197 = ctrl_tac_fold_args f env ctrl1 ts1
                          in
                       bind uu____8197
                         (fun uu____8224  ->
                            match uu____8224 with
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
              let uu____8306 =
                let uu____8313 =
                  add_irrelevant_goal "dummy" env FStar_Syntax_Util.t_true
                    opts
                   in
                bind uu____8313
                  (fun uu____8322  ->
                     let uu____8323 = ctrl t1  in
                     bind uu____8323
                       (fun res  ->
                          let uu____8346 = trivial ()  in
                          bind uu____8346 (fun uu____8354  -> ret res)))
                 in
              bind uu____8306
                (fun uu____8370  ->
                   match uu____8370 with
                   | (should_rewrite,ctrl1) ->
                       if Prims.op_Negation should_rewrite
                       then ret (t1, ctrl1)
                       else
                         (let uu____8394 =
                            FStar_TypeChecker_TcTerm.tc_term env t1  in
                          match uu____8394 with
                          | (t2,lcomp,g) ->
                              let uu____8410 =
                                (let uu____8413 =
                                   FStar_Syntax_Util.is_pure_or_ghost_lcomp
                                     lcomp
                                    in
                                 Prims.op_Negation uu____8413) ||
                                  (let uu____8415 =
                                     FStar_TypeChecker_Rel.is_trivial g  in
                                   Prims.op_Negation uu____8415)
                                 in
                              if uu____8410
                              then ret (t2, globalStop)
                              else
                                (let typ = lcomp.FStar_Syntax_Syntax.res_typ
                                    in
                                 let uu____8428 =
                                   new_uvar "pointwise_rec" env typ  in
                                 bind uu____8428
                                   (fun uu____8448  ->
                                      match uu____8448 with
                                      | (ut,uvar_ut) ->
                                          (log ps
                                             (fun uu____8465  ->
                                                let uu____8466 =
                                                  FStar_Syntax_Print.term_to_string
                                                    t2
                                                   in
                                                let uu____8467 =
                                                  FStar_Syntax_Print.term_to_string
                                                    ut
                                                   in
                                                FStar_Util.print2
                                                  "Pointwise_rec: making equality\n\t%s ==\n\t%s\n"
                                                  uu____8466 uu____8467);
                                           (let uu____8468 =
                                              let uu____8471 =
                                                let uu____8472 =
                                                  FStar_TypeChecker_TcTerm.universe_of
                                                    env typ
                                                   in
                                                FStar_Syntax_Util.mk_eq2
                                                  uu____8472 typ t2 ut
                                                 in
                                              add_irrelevant_goal
                                                "rewrite_rec equation" env
                                                uu____8471 opts
                                               in
                                            bind uu____8468
                                              (fun uu____8479  ->
                                                 let uu____8480 =
                                                   bind rewriter
                                                     (fun uu____8494  ->
                                                        let ut1 =
                                                          FStar_TypeChecker_Normalize.reduce_uvar_solutions
                                                            env ut
                                                           in
                                                        log ps
                                                          (fun uu____8500  ->
                                                             let uu____8501 =
                                                               FStar_Syntax_Print.term_to_string
                                                                 t2
                                                                in
                                                             let uu____8502 =
                                                               FStar_Syntax_Print.term_to_string
                                                                 ut1
                                                                in
                                                             FStar_Util.print2
                                                               "rewrite_rec: succeeded rewriting\n\t%s to\n\t%s\n"
                                                               uu____8501
                                                               uu____8502);
                                                        ret (ut1, ctrl1))
                                                    in
                                                 focus uu____8480)))))))
  
let (topdown_rewrite :
  (FStar_Syntax_Syntax.term ->
     (Prims.bool,FStar_BigInt.t) FStar_Pervasives_Native.tuple2 tac)
    -> unit tac -> unit tac)
  =
  fun ctrl  ->
    fun rewriter  ->
      let uu____8543 =
        bind get
          (fun ps  ->
             let uu____8553 =
               match ps.FStar_Tactics_Types.goals with
               | g::gs -> (g, gs)
               | [] -> failwith "no goals"  in
             match uu____8553 with
             | (g,gs) ->
                 let gt1 = FStar_Tactics_Types.goal_type g  in
                 (log ps
                    (fun uu____8590  ->
                       let uu____8591 = FStar_Syntax_Print.term_to_string gt1
                          in
                       FStar_Util.print1 "Topdown_rewrite starting with %s\n"
                         uu____8591);
                  bind dismiss_all
                    (fun uu____8594  ->
                       let uu____8595 =
                         let uu____8602 = FStar_Tactics_Types.goal_env g  in
                         ctrl_tac_fold
                           (rewrite_rec ps ctrl rewriter
                              g.FStar_Tactics_Types.opts) uu____8602
                           keepGoing gt1
                          in
                       bind uu____8595
                         (fun uu____8614  ->
                            match uu____8614 with
                            | (gt',uu____8622) ->
                                (log ps
                                   (fun uu____8626  ->
                                      let uu____8627 =
                                        FStar_Syntax_Print.term_to_string gt'
                                         in
                                      FStar_Util.print1
                                        "Topdown_rewrite seems to have succeded with %s\n"
                                        uu____8627);
                                 (let uu____8628 = push_goals gs  in
                                  bind uu____8628
                                    (fun uu____8633  ->
                                       let uu____8634 =
                                         let uu____8637 =
                                           FStar_Tactics_Types.goal_with_type
                                             g gt'
                                            in
                                         [uu____8637]  in
                                       add_goals uu____8634)))))))
         in
      FStar_All.pipe_left (wrap_err "topdown_rewrite") uu____8543
  
let (pointwise : FStar_Tactics_Types.direction -> unit tac -> unit tac) =
  fun d  ->
    fun tau  ->
      let uu____8660 =
        bind get
          (fun ps  ->
             let uu____8670 =
               match ps.FStar_Tactics_Types.goals with
               | g::gs -> (g, gs)
               | [] -> failwith "no goals"  in
             match uu____8670 with
             | (g,gs) ->
                 let gt1 = FStar_Tactics_Types.goal_type g  in
                 (log ps
                    (fun uu____8707  ->
                       let uu____8708 = FStar_Syntax_Print.term_to_string gt1
                          in
                       FStar_Util.print1 "Pointwise starting with %s\n"
                         uu____8708);
                  bind dismiss_all
                    (fun uu____8711  ->
                       let uu____8712 =
                         let uu____8715 = FStar_Tactics_Types.goal_env g  in
                         tac_fold_env d
                           (pointwise_rec ps tau g.FStar_Tactics_Types.opts)
                           uu____8715 gt1
                          in
                       bind uu____8712
                         (fun gt'  ->
                            log ps
                              (fun uu____8723  ->
                                 let uu____8724 =
                                   FStar_Syntax_Print.term_to_string gt'  in
                                 FStar_Util.print1
                                   "Pointwise seems to have succeded with %s\n"
                                   uu____8724);
                            (let uu____8725 = push_goals gs  in
                             bind uu____8725
                               (fun uu____8730  ->
                                  let uu____8731 =
                                    let uu____8734 =
                                      FStar_Tactics_Types.goal_with_type g
                                        gt'
                                       in
                                    [uu____8734]  in
                                  add_goals uu____8731))))))
         in
      FStar_All.pipe_left (wrap_err "pointwise") uu____8660
  
let (trefl : unit -> unit tac) =
  fun uu____8745  ->
    let uu____8748 =
      let uu____8751 = cur_goal ()  in
      bind uu____8751
        (fun g  ->
           let uu____8769 =
             let uu____8774 = FStar_Tactics_Types.goal_type g  in
             FStar_Syntax_Util.un_squash uu____8774  in
           match uu____8769 with
           | FStar_Pervasives_Native.Some t ->
               let uu____8782 = FStar_Syntax_Util.head_and_args' t  in
               (match uu____8782 with
                | (hd1,args) ->
                    let uu____8815 =
                      let uu____8826 =
                        let uu____8827 = FStar_Syntax_Util.un_uinst hd1  in
                        uu____8827.FStar_Syntax_Syntax.n  in
                      (uu____8826, args)  in
                    (match uu____8815 with
                     | (FStar_Syntax_Syntax.Tm_fvar
                        fv,uu____8839::(l,uu____8841)::(r,uu____8843)::[])
                         when
                         FStar_Syntax_Syntax.fv_eq_lid fv
                           FStar_Parser_Const.eq2_lid
                         ->
                         let uu____8870 =
                           let uu____8873 = FStar_Tactics_Types.goal_env g
                              in
                           do_unify uu____8873 l r  in
                         bind uu____8870
                           (fun b  ->
                              if Prims.op_Negation b
                              then
                                let uu____8880 =
                                  let uu____8881 =
                                    FStar_Tactics_Types.goal_env g  in
                                  tts uu____8881 l  in
                                let uu____8882 =
                                  let uu____8883 =
                                    FStar_Tactics_Types.goal_env g  in
                                  tts uu____8883 r  in
                                fail2 "not a trivial equality (%s vs %s)"
                                  uu____8880 uu____8882
                              else solve' g FStar_Syntax_Util.exp_unit)
                     | (hd2,uu____8886) ->
                         let uu____8899 =
                           let uu____8900 = FStar_Tactics_Types.goal_env g
                              in
                           tts uu____8900 t  in
                         fail1 "trefl: not an equality (%s)" uu____8899))
           | FStar_Pervasives_Native.None  -> fail "not an irrelevant goal")
       in
    FStar_All.pipe_left (wrap_err "trefl") uu____8748
  
let (dup : unit -> unit tac) =
  fun uu____8913  ->
    let uu____8916 = cur_goal ()  in
    bind uu____8916
      (fun g  ->
         let uu____8922 =
           let uu____8929 = FStar_Tactics_Types.goal_env g  in
           let uu____8930 = FStar_Tactics_Types.goal_type g  in
           new_uvar "dup" uu____8929 uu____8930  in
         bind uu____8922
           (fun uu____8939  ->
              match uu____8939 with
              | (u,u_uvar) ->
                  let g' =
                    let uu___147_8949 = g  in
                    {
                      FStar_Tactics_Types.goal_main_env =
                        (uu___147_8949.FStar_Tactics_Types.goal_main_env);
                      FStar_Tactics_Types.goal_ctx_uvar = u_uvar;
                      FStar_Tactics_Types.opts =
                        (uu___147_8949.FStar_Tactics_Types.opts);
                      FStar_Tactics_Types.is_guard =
                        (uu___147_8949.FStar_Tactics_Types.is_guard)
                    }  in
                  bind __dismiss
                    (fun uu____8952  ->
                       let uu____8953 =
                         let uu____8956 = FStar_Tactics_Types.goal_env g  in
                         let uu____8957 =
                           let uu____8958 =
                             let uu____8959 = FStar_Tactics_Types.goal_env g
                                in
                             let uu____8960 = FStar_Tactics_Types.goal_type g
                                in
                             FStar_TypeChecker_TcTerm.universe_of uu____8959
                               uu____8960
                              in
                           let uu____8961 = FStar_Tactics_Types.goal_type g
                              in
                           let uu____8962 =
                             FStar_Tactics_Types.goal_witness g  in
                           FStar_Syntax_Util.mk_eq2 uu____8958 uu____8961 u
                             uu____8962
                            in
                         add_irrelevant_goal "dup equation" uu____8956
                           uu____8957 g.FStar_Tactics_Types.opts
                          in
                       bind uu____8953
                         (fun uu____8965  ->
                            let uu____8966 = add_goals [g']  in
                            bind uu____8966 (fun uu____8970  -> ret ())))))
  
let (flip : unit -> unit tac) =
  fun uu____8977  ->
    bind get
      (fun ps  ->
         match ps.FStar_Tactics_Types.goals with
         | g1::g2::gs ->
             set
               (let uu___148_8994 = ps  in
                {
                  FStar_Tactics_Types.main_context =
                    (uu___148_8994.FStar_Tactics_Types.main_context);
                  FStar_Tactics_Types.main_goal =
                    (uu___148_8994.FStar_Tactics_Types.main_goal);
                  FStar_Tactics_Types.all_implicits =
                    (uu___148_8994.FStar_Tactics_Types.all_implicits);
                  FStar_Tactics_Types.goals = (g2 :: g1 :: gs);
                  FStar_Tactics_Types.smt_goals =
                    (uu___148_8994.FStar_Tactics_Types.smt_goals);
                  FStar_Tactics_Types.depth =
                    (uu___148_8994.FStar_Tactics_Types.depth);
                  FStar_Tactics_Types.__dump =
                    (uu___148_8994.FStar_Tactics_Types.__dump);
                  FStar_Tactics_Types.psc =
                    (uu___148_8994.FStar_Tactics_Types.psc);
                  FStar_Tactics_Types.entry_range =
                    (uu___148_8994.FStar_Tactics_Types.entry_range);
                  FStar_Tactics_Types.guard_policy =
                    (uu___148_8994.FStar_Tactics_Types.guard_policy);
                  FStar_Tactics_Types.freshness =
                    (uu___148_8994.FStar_Tactics_Types.freshness)
                })
         | uu____8995 -> fail "flip: less than 2 goals")
  
let (later : unit -> unit tac) =
  fun uu____9004  ->
    bind get
      (fun ps  ->
         match ps.FStar_Tactics_Types.goals with
         | [] -> ret ()
         | g::gs ->
             set
               (let uu___149_9017 = ps  in
                {
                  FStar_Tactics_Types.main_context =
                    (uu___149_9017.FStar_Tactics_Types.main_context);
                  FStar_Tactics_Types.main_goal =
                    (uu___149_9017.FStar_Tactics_Types.main_goal);
                  FStar_Tactics_Types.all_implicits =
                    (uu___149_9017.FStar_Tactics_Types.all_implicits);
                  FStar_Tactics_Types.goals = (FStar_List.append gs [g]);
                  FStar_Tactics_Types.smt_goals =
                    (uu___149_9017.FStar_Tactics_Types.smt_goals);
                  FStar_Tactics_Types.depth =
                    (uu___149_9017.FStar_Tactics_Types.depth);
                  FStar_Tactics_Types.__dump =
                    (uu___149_9017.FStar_Tactics_Types.__dump);
                  FStar_Tactics_Types.psc =
                    (uu___149_9017.FStar_Tactics_Types.psc);
                  FStar_Tactics_Types.entry_range =
                    (uu___149_9017.FStar_Tactics_Types.entry_range);
                  FStar_Tactics_Types.guard_policy =
                    (uu___149_9017.FStar_Tactics_Types.guard_policy);
                  FStar_Tactics_Types.freshness =
                    (uu___149_9017.FStar_Tactics_Types.freshness)
                }))
  
let (qed : unit -> unit tac) =
  fun uu____9024  ->
    bind get
      (fun ps  ->
         match ps.FStar_Tactics_Types.goals with
         | [] -> ret ()
         | uu____9031 -> fail "Not done!")
  
let (cases :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 tac)
  =
  fun t  ->
    let uu____9051 =
      let uu____9058 = cur_goal ()  in
      bind uu____9058
        (fun g  ->
           let uu____9068 =
             let uu____9077 = FStar_Tactics_Types.goal_env g  in
             __tc uu____9077 t  in
           bind uu____9068
             (fun uu____9105  ->
                match uu____9105 with
                | (t1,typ,guard) ->
                    let uu____9121 = FStar_Syntax_Util.head_and_args typ  in
                    (match uu____9121 with
                     | (hd1,args) ->
                         let uu____9164 =
                           let uu____9177 =
                             let uu____9178 = FStar_Syntax_Util.un_uinst hd1
                                in
                             uu____9178.FStar_Syntax_Syntax.n  in
                           (uu____9177, args)  in
                         (match uu____9164 with
                          | (FStar_Syntax_Syntax.Tm_fvar
                             fv,(p,uu____9197)::(q,uu____9199)::[]) when
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
                                let uu____9237 =
                                  let uu____9238 =
                                    FStar_Tactics_Types.goal_env g  in
                                  FStar_TypeChecker_Env.push_bv uu____9238
                                    v_p
                                   in
                                FStar_Tactics_Types.goal_with_env g
                                  uu____9237
                                 in
                              let g2 =
                                let uu____9240 =
                                  let uu____9241 =
                                    FStar_Tactics_Types.goal_env g  in
                                  FStar_TypeChecker_Env.push_bv uu____9241
                                    v_q
                                   in
                                FStar_Tactics_Types.goal_with_env g
                                  uu____9240
                                 in
                              bind __dismiss
                                (fun uu____9248  ->
                                   let uu____9249 = add_goals [g1; g2]  in
                                   bind uu____9249
                                     (fun uu____9258  ->
                                        let uu____9259 =
                                          let uu____9264 =
                                            FStar_Syntax_Syntax.bv_to_name
                                              v_p
                                             in
                                          let uu____9265 =
                                            FStar_Syntax_Syntax.bv_to_name
                                              v_q
                                             in
                                          (uu____9264, uu____9265)  in
                                        ret uu____9259))
                          | uu____9270 ->
                              let uu____9283 =
                                let uu____9284 =
                                  FStar_Tactics_Types.goal_env g  in
                                tts uu____9284 typ  in
                              fail1 "Not a disjunction: %s" uu____9283))))
       in
    FStar_All.pipe_left (wrap_err "cases") uu____9051
  
let (set_options : Prims.string -> unit tac) =
  fun s  ->
    let uu____9314 =
      let uu____9317 = cur_goal ()  in
      bind uu____9317
        (fun g  ->
           FStar_Options.push ();
           (let uu____9330 = FStar_Util.smap_copy g.FStar_Tactics_Types.opts
               in
            FStar_Options.set uu____9330);
           (let res = FStar_Options.set_options FStar_Options.Set s  in
            let opts' = FStar_Options.peek ()  in
            FStar_Options.pop ();
            (match res with
             | FStar_Getopt.Success  ->
                 let g' =
                   let uu___150_9337 = g  in
                   {
                     FStar_Tactics_Types.goal_main_env =
                       (uu___150_9337.FStar_Tactics_Types.goal_main_env);
                     FStar_Tactics_Types.goal_ctx_uvar =
                       (uu___150_9337.FStar_Tactics_Types.goal_ctx_uvar);
                     FStar_Tactics_Types.opts = opts';
                     FStar_Tactics_Types.is_guard =
                       (uu___150_9337.FStar_Tactics_Types.is_guard)
                   }  in
                 replace_cur g'
             | FStar_Getopt.Error err ->
                 fail2 "Setting options `%s` failed: %s" s err
             | FStar_Getopt.Help  ->
                 fail1 "Setting options `%s` failed (got `Help`?)" s)))
       in
    FStar_All.pipe_left (wrap_err "set_options") uu____9314
  
let (top_env : unit -> env tac) =
  fun uu____9349  ->
    bind get
      (fun ps  -> FStar_All.pipe_left ret ps.FStar_Tactics_Types.main_context)
  
let (cur_env : unit -> env tac) =
  fun uu____9362  ->
    let uu____9365 = cur_goal ()  in
    bind uu____9365
      (fun g  ->
         let uu____9371 = FStar_Tactics_Types.goal_env g  in
         FStar_All.pipe_left ret uu____9371)
  
let (cur_goal' : unit -> FStar_Syntax_Syntax.term tac) =
  fun uu____9380  ->
    let uu____9383 = cur_goal ()  in
    bind uu____9383
      (fun g  ->
         let uu____9389 = FStar_Tactics_Types.goal_type g  in
         FStar_All.pipe_left ret uu____9389)
  
let (cur_witness : unit -> FStar_Syntax_Syntax.term tac) =
  fun uu____9398  ->
    let uu____9401 = cur_goal ()  in
    bind uu____9401
      (fun g  ->
         let uu____9407 = FStar_Tactics_Types.goal_witness g  in
         FStar_All.pipe_left ret uu____9407)
  
let (unquote :
  FStar_Reflection_Data.typ ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term tac)
  =
  fun ty  ->
    fun tm  ->
      let uu____9424 =
        let uu____9427 = cur_goal ()  in
        bind uu____9427
          (fun goal  ->
             let env =
               let uu____9435 = FStar_Tactics_Types.goal_env goal  in
               FStar_TypeChecker_Env.set_expected_typ uu____9435 ty  in
             let uu____9436 = __tc env tm  in
             bind uu____9436
               (fun uu____9456  ->
                  match uu____9456 with
                  | (tm1,typ,guard) ->
                      let uu____9468 =
                        proc_guard "unquote" env guard
                          goal.FStar_Tactics_Types.opts
                         in
                      bind uu____9468 (fun uu____9472  -> ret tm1)))
         in
      FStar_All.pipe_left (wrap_err "unquote") uu____9424
  
let (uvar_env :
  env ->
    FStar_Reflection_Data.typ FStar_Pervasives_Native.option ->
      FStar_Syntax_Syntax.term tac)
  =
  fun env  ->
    fun ty  ->
      let uu____9495 =
        match ty with
        | FStar_Pervasives_Native.Some ty1 -> ret ty1
        | FStar_Pervasives_Native.None  ->
            let uu____9501 =
              let uu____9508 =
                let uu____9509 = FStar_Syntax_Util.type_u ()  in
                FStar_All.pipe_left FStar_Pervasives_Native.fst uu____9509
                 in
              new_uvar "uvar_env.2" env uu____9508  in
            bind uu____9501
              (fun uu____9525  ->
                 match uu____9525 with | (typ,uvar_typ) -> ret typ)
         in
      bind uu____9495
        (fun typ  ->
           let uu____9537 = new_uvar "uvar_env" env typ  in
           bind uu____9537
             (fun uu____9551  -> match uu____9551 with | (t,uvar_t) -> ret t))
  
let (unshelve : FStar_Syntax_Syntax.term -> unit tac) =
  fun t  ->
    let uu____9569 =
      bind get
        (fun ps  ->
           let env = ps.FStar_Tactics_Types.main_context  in
           let opts =
             match ps.FStar_Tactics_Types.goals with
             | g::uu____9588 -> g.FStar_Tactics_Types.opts
             | uu____9591 -> FStar_Options.peek ()  in
           let uu____9594 = FStar_Syntax_Util.head_and_args t  in
           match uu____9594 with
           | ({
                FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                  (ctx_uvar,uu____9612);
                FStar_Syntax_Syntax.pos = uu____9613;
                FStar_Syntax_Syntax.vars = uu____9614;_},uu____9615)
               ->
               let env1 =
                 let uu___151_9657 = env  in
                 {
                   FStar_TypeChecker_Env.solver =
                     (uu___151_9657.FStar_TypeChecker_Env.solver);
                   FStar_TypeChecker_Env.range =
                     (uu___151_9657.FStar_TypeChecker_Env.range);
                   FStar_TypeChecker_Env.curmodule =
                     (uu___151_9657.FStar_TypeChecker_Env.curmodule);
                   FStar_TypeChecker_Env.gamma =
                     (ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_gamma);
                   FStar_TypeChecker_Env.gamma_sig =
                     (uu___151_9657.FStar_TypeChecker_Env.gamma_sig);
                   FStar_TypeChecker_Env.gamma_cache =
                     (uu___151_9657.FStar_TypeChecker_Env.gamma_cache);
                   FStar_TypeChecker_Env.modules =
                     (uu___151_9657.FStar_TypeChecker_Env.modules);
                   FStar_TypeChecker_Env.expected_typ =
                     (uu___151_9657.FStar_TypeChecker_Env.expected_typ);
                   FStar_TypeChecker_Env.sigtab =
                     (uu___151_9657.FStar_TypeChecker_Env.sigtab);
                   FStar_TypeChecker_Env.is_pattern =
                     (uu___151_9657.FStar_TypeChecker_Env.is_pattern);
                   FStar_TypeChecker_Env.instantiate_imp =
                     (uu___151_9657.FStar_TypeChecker_Env.instantiate_imp);
                   FStar_TypeChecker_Env.effects =
                     (uu___151_9657.FStar_TypeChecker_Env.effects);
                   FStar_TypeChecker_Env.generalize =
                     (uu___151_9657.FStar_TypeChecker_Env.generalize);
                   FStar_TypeChecker_Env.letrecs =
                     (uu___151_9657.FStar_TypeChecker_Env.letrecs);
                   FStar_TypeChecker_Env.top_level =
                     (uu___151_9657.FStar_TypeChecker_Env.top_level);
                   FStar_TypeChecker_Env.check_uvars =
                     (uu___151_9657.FStar_TypeChecker_Env.check_uvars);
                   FStar_TypeChecker_Env.use_eq =
                     (uu___151_9657.FStar_TypeChecker_Env.use_eq);
                   FStar_TypeChecker_Env.is_iface =
                     (uu___151_9657.FStar_TypeChecker_Env.is_iface);
                   FStar_TypeChecker_Env.admit =
                     (uu___151_9657.FStar_TypeChecker_Env.admit);
                   FStar_TypeChecker_Env.lax =
                     (uu___151_9657.FStar_TypeChecker_Env.lax);
                   FStar_TypeChecker_Env.lax_universes =
                     (uu___151_9657.FStar_TypeChecker_Env.lax_universes);
                   FStar_TypeChecker_Env.failhard =
                     (uu___151_9657.FStar_TypeChecker_Env.failhard);
                   FStar_TypeChecker_Env.nosynth =
                     (uu___151_9657.FStar_TypeChecker_Env.nosynth);
                   FStar_TypeChecker_Env.uvar_subtyping =
                     (uu___151_9657.FStar_TypeChecker_Env.uvar_subtyping);
                   FStar_TypeChecker_Env.tc_term =
                     (uu___151_9657.FStar_TypeChecker_Env.tc_term);
                   FStar_TypeChecker_Env.type_of =
                     (uu___151_9657.FStar_TypeChecker_Env.type_of);
                   FStar_TypeChecker_Env.universe_of =
                     (uu___151_9657.FStar_TypeChecker_Env.universe_of);
                   FStar_TypeChecker_Env.check_type_of =
                     (uu___151_9657.FStar_TypeChecker_Env.check_type_of);
                   FStar_TypeChecker_Env.use_bv_sorts =
                     (uu___151_9657.FStar_TypeChecker_Env.use_bv_sorts);
                   FStar_TypeChecker_Env.qtbl_name_and_index =
                     (uu___151_9657.FStar_TypeChecker_Env.qtbl_name_and_index);
                   FStar_TypeChecker_Env.normalized_eff_names =
                     (uu___151_9657.FStar_TypeChecker_Env.normalized_eff_names);
                   FStar_TypeChecker_Env.proof_ns =
                     (uu___151_9657.FStar_TypeChecker_Env.proof_ns);
                   FStar_TypeChecker_Env.synth_hook =
                     (uu___151_9657.FStar_TypeChecker_Env.synth_hook);
                   FStar_TypeChecker_Env.splice =
                     (uu___151_9657.FStar_TypeChecker_Env.splice);
                   FStar_TypeChecker_Env.is_native_tactic =
                     (uu___151_9657.FStar_TypeChecker_Env.is_native_tactic);
                   FStar_TypeChecker_Env.identifier_info =
                     (uu___151_9657.FStar_TypeChecker_Env.identifier_info);
                   FStar_TypeChecker_Env.tc_hooks =
                     (uu___151_9657.FStar_TypeChecker_Env.tc_hooks);
                   FStar_TypeChecker_Env.dsenv =
                     (uu___151_9657.FStar_TypeChecker_Env.dsenv);
                   FStar_TypeChecker_Env.dep_graph =
                     (uu___151_9657.FStar_TypeChecker_Env.dep_graph)
                 }  in
               let g = FStar_Tactics_Types.mk_goal env1 ctx_uvar opts false
                  in
               let uu____9659 =
                 let uu____9662 = bnorm_goal g  in [uu____9662]  in
               add_goals uu____9659
           | uu____9663 -> fail "not a uvar")
       in
    FStar_All.pipe_left (wrap_err "unshelve") uu____9569
  
let (unify :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.bool tac) =
  fun t1  ->
    fun t2  ->
      bind get
        (fun ps  -> do_unify ps.FStar_Tactics_Types.main_context t1 t2)
  
let (launch_process :
  Prims.string -> Prims.string Prims.list -> Prims.string -> Prims.string tac)
  =
  fun prog  ->
    fun args  ->
      fun input  ->
        bind idtac
          (fun uu____9724  ->
             let uu____9725 = FStar_Options.unsafe_tactic_exec ()  in
             if uu____9725
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
        (fun uu____9746  ->
           let uu____9747 =
             FStar_Syntax_Syntax.gen_bv nm FStar_Pervasives_Native.None t  in
           ret uu____9747)
  
let (change : FStar_Reflection_Data.typ -> unit tac) =
  fun ty  ->
    let uu____9757 =
      mlog
        (fun uu____9762  ->
           let uu____9763 = FStar_Syntax_Print.term_to_string ty  in
           FStar_Util.print1 "change: ty = %s\n" uu____9763)
        (fun uu____9766  ->
           let uu____9767 = cur_goal ()  in
           bind uu____9767
             (fun g  ->
                let uu____9773 =
                  let uu____9782 = FStar_Tactics_Types.goal_env g  in
                  __tc uu____9782 ty  in
                bind uu____9773
                  (fun uu____9794  ->
                     match uu____9794 with
                     | (ty1,uu____9804,guard) ->
                         let uu____9806 =
                           let uu____9809 = FStar_Tactics_Types.goal_env g
                              in
                           proc_guard "change" uu____9809 guard
                             g.FStar_Tactics_Types.opts
                            in
                         bind uu____9806
                           (fun uu____9812  ->
                              let uu____9813 =
                                let uu____9816 =
                                  FStar_Tactics_Types.goal_env g  in
                                let uu____9817 =
                                  FStar_Tactics_Types.goal_type g  in
                                do_unify uu____9816 uu____9817 ty1  in
                              bind uu____9813
                                (fun bb  ->
                                   if bb
                                   then
                                     let uu____9823 =
                                       FStar_Tactics_Types.goal_with_type g
                                         ty1
                                        in
                                     replace_cur uu____9823
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
                                        let uu____9829 =
                                          FStar_Tactics_Types.goal_env g  in
                                        let uu____9830 =
                                          FStar_Tactics_Types.goal_type g  in
                                        normalize steps uu____9829 uu____9830
                                         in
                                      let nty =
                                        let uu____9832 =
                                          FStar_Tactics_Types.goal_env g  in
                                        normalize steps uu____9832 ty1  in
                                      let uu____9833 =
                                        let uu____9836 =
                                          FStar_Tactics_Types.goal_env g  in
                                        do_unify uu____9836 ng nty  in
                                      bind uu____9833
                                        (fun b  ->
                                           if b
                                           then
                                             let uu____9842 =
                                               FStar_Tactics_Types.goal_with_type
                                                 g ty1
                                                in
                                             replace_cur uu____9842
                                           else fail "not convertible")))))))
       in
    FStar_All.pipe_left (wrap_err "change") uu____9757
  
let rec last : 'a . 'a Prims.list -> 'a =
  fun l  ->
    match l with
    | [] -> failwith "last: empty list"
    | x::[] -> x
    | uu____9864::xs -> last xs
  
let rec init : 'a . 'a Prims.list -> 'a Prims.list =
  fun l  ->
    match l with
    | [] -> failwith "init: empty list"
    | x::[] -> []
    | x::xs -> let uu____9892 = init xs  in x :: uu____9892
  
let rec (inspect :
  FStar_Syntax_Syntax.term -> FStar_Reflection_Data.term_view tac) =
  fun t  ->
    let uu____9904 =
      let t1 = FStar_Syntax_Util.unascribe t  in
      let t2 = FStar_Syntax_Util.un_uinst t1  in
      match t2.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_meta (t3,uu____9912) -> inspect t3
      | FStar_Syntax_Syntax.Tm_name bv ->
          FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_Var bv)
      | FStar_Syntax_Syntax.Tm_bvar bv ->
          FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_BVar bv)
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_FVar fv)
      | FStar_Syntax_Syntax.Tm_app (hd1,[]) ->
          failwith "empty arguments on Tm_app"
      | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
          let uu____9969 = last args  in
          (match uu____9969 with
           | (a,q) ->
               let q' = FStar_Reflection_Basic.inspect_aqual q  in
               let uu____9991 =
                 let uu____9992 =
                   let uu____9997 =
                     let uu____9998 =
                       let uu____10003 = init args  in
                       FStar_Syntax_Syntax.mk_Tm_app hd1 uu____10003  in
                     uu____9998 FStar_Pervasives_Native.None
                       t2.FStar_Syntax_Syntax.pos
                      in
                   (uu____9997, (a, q'))  in
                 FStar_Reflection_Data.Tv_App uu____9992  in
               FStar_All.pipe_left ret uu____9991)
      | FStar_Syntax_Syntax.Tm_abs ([],uu____10014,uu____10015) ->
          failwith "empty arguments on Tm_abs"
      | FStar_Syntax_Syntax.Tm_abs (bs,t3,k) ->
          let uu____10059 = FStar_Syntax_Subst.open_term bs t3  in
          (match uu____10059 with
           | (bs1,t4) ->
               (match bs1 with
                | [] -> failwith "impossible"
                | b::bs2 ->
                    let uu____10092 =
                      let uu____10093 =
                        let uu____10098 = FStar_Syntax_Util.abs bs2 t4 k  in
                        (b, uu____10098)  in
                      FStar_Reflection_Data.Tv_Abs uu____10093  in
                    FStar_All.pipe_left ret uu____10092))
      | FStar_Syntax_Syntax.Tm_type uu____10101 ->
          FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_Type ())
      | FStar_Syntax_Syntax.Tm_arrow ([],k) ->
          failwith "empty binders on arrow"
      | FStar_Syntax_Syntax.Tm_arrow uu____10121 ->
          let uu____10134 = FStar_Syntax_Util.arrow_one t2  in
          (match uu____10134 with
           | FStar_Pervasives_Native.Some (b,c) ->
               FStar_All.pipe_left ret
                 (FStar_Reflection_Data.Tv_Arrow (b, c))
           | FStar_Pervasives_Native.None  -> failwith "impossible")
      | FStar_Syntax_Syntax.Tm_refine (bv,t3) ->
          let b = FStar_Syntax_Syntax.mk_binder bv  in
          let uu____10164 = FStar_Syntax_Subst.open_term [b] t3  in
          (match uu____10164 with
           | (b',t4) ->
               let b1 =
                 match b' with
                 | b'1::[] -> b'1
                 | uu____10203 -> failwith "impossible"  in
               FStar_All.pipe_left ret
                 (FStar_Reflection_Data.Tv_Refine
                    ((FStar_Pervasives_Native.fst b1), t4)))
      | FStar_Syntax_Syntax.Tm_constant c ->
          let uu____10211 =
            let uu____10212 = FStar_Reflection_Basic.inspect_const c  in
            FStar_Reflection_Data.Tv_Const uu____10212  in
          FStar_All.pipe_left ret uu____10211
      | FStar_Syntax_Syntax.Tm_uvar (ctx_u,s) ->
          let uu____10237 =
            let uu____10238 =
              let uu____10243 =
                let uu____10244 =
                  FStar_Syntax_Unionfind.uvar_id
                    ctx_u.FStar_Syntax_Syntax.ctx_uvar_head
                   in
                FStar_BigInt.of_int_fs uu____10244  in
              (uu____10243, (ctx_u, s))  in
            FStar_Reflection_Data.Tv_Uvar uu____10238  in
          FStar_All.pipe_left ret uu____10237
      | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),t21) ->
          if lb.FStar_Syntax_Syntax.lbunivs <> []
          then FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown
          else
            (match lb.FStar_Syntax_Syntax.lbname with
             | FStar_Util.Inr uu____10280 ->
                 FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown
             | FStar_Util.Inl bv ->
                 let b = FStar_Syntax_Syntax.mk_binder bv  in
                 let uu____10285 = FStar_Syntax_Subst.open_term [b] t21  in
                 (match uu____10285 with
                  | (bs,t22) ->
                      let b1 =
                        match bs with
                        | b1::[] -> b1
                        | uu____10324 ->
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
             | FStar_Util.Inr uu____10354 ->
                 FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown
             | FStar_Util.Inl bv ->
                 let uu____10358 = FStar_Syntax_Subst.open_let_rec [lb] t21
                    in
                 (match uu____10358 with
                  | (lbs,t22) ->
                      (match lbs with
                       | lb1::[] ->
                           (match lb1.FStar_Syntax_Syntax.lbname with
                            | FStar_Util.Inr uu____10378 ->
                                ret FStar_Reflection_Data.Tv_Unknown
                            | FStar_Util.Inl bv1 ->
                                FStar_All.pipe_left ret
                                  (FStar_Reflection_Data.Tv_Let
                                     (true, bv1,
                                       (lb1.FStar_Syntax_Syntax.lbdef), t22)))
                       | uu____10382 ->
                           failwith
                             "impossible: open_term returned different amount of binders")))
      | FStar_Syntax_Syntax.Tm_match (t3,brs) ->
          let rec inspect_pat p =
            match p.FStar_Syntax_Syntax.v with
            | FStar_Syntax_Syntax.Pat_constant c ->
                let uu____10436 = FStar_Reflection_Basic.inspect_const c  in
                FStar_Reflection_Data.Pat_Constant uu____10436
            | FStar_Syntax_Syntax.Pat_cons (fv,ps) ->
                let uu____10455 =
                  let uu____10462 =
                    FStar_List.map
                      (fun uu____10474  ->
                         match uu____10474 with
                         | (p1,uu____10482) -> inspect_pat p1) ps
                     in
                  (fv, uu____10462)  in
                FStar_Reflection_Data.Pat_Cons uu____10455
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
              (fun uu___92_10566  ->
                 match uu___92_10566 with
                 | (pat,uu____10584,t4) ->
                     let uu____10598 = inspect_pat pat  in (uu____10598, t4))
              brs1
             in
          FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_Match (t3, brs2))
      | FStar_Syntax_Syntax.Tm_unknown  ->
          FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown
      | uu____10605 ->
          ((let uu____10607 =
              let uu____10612 =
                let uu____10613 = FStar_Syntax_Print.tag_of_term t2  in
                let uu____10614 = FStar_Syntax_Print.term_to_string t2  in
                FStar_Util.format2
                  "inspect: outside of expected syntax (%s, %s)\n"
                  uu____10613 uu____10614
                 in
              (FStar_Errors.Warning_CantInspect, uu____10612)  in
            FStar_Errors.log_issue t2.FStar_Syntax_Syntax.pos uu____10607);
           FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown)
       in
    wrap_err "inspect" uu____9904
  
let (pack : FStar_Reflection_Data.term_view -> FStar_Syntax_Syntax.term tac)
  =
  fun tv  ->
    match tv with
    | FStar_Reflection_Data.Tv_Var bv ->
        let uu____10627 = FStar_Syntax_Syntax.bv_to_name bv  in
        FStar_All.pipe_left ret uu____10627
    | FStar_Reflection_Data.Tv_BVar bv ->
        let uu____10631 = FStar_Syntax_Syntax.bv_to_tm bv  in
        FStar_All.pipe_left ret uu____10631
    | FStar_Reflection_Data.Tv_FVar fv ->
        let uu____10635 = FStar_Syntax_Syntax.fv_to_tm fv  in
        FStar_All.pipe_left ret uu____10635
    | FStar_Reflection_Data.Tv_App (l,(r,q)) ->
        let q' = FStar_Reflection_Basic.pack_aqual q  in
        let uu____10642 = FStar_Syntax_Util.mk_app l [(r, q')]  in
        FStar_All.pipe_left ret uu____10642
    | FStar_Reflection_Data.Tv_Abs (b,t) ->
        let uu____10665 =
          FStar_Syntax_Util.abs [b] t FStar_Pervasives_Native.None  in
        FStar_All.pipe_left ret uu____10665
    | FStar_Reflection_Data.Tv_Arrow (b,c) ->
        let uu____10682 = FStar_Syntax_Util.arrow [b] c  in
        FStar_All.pipe_left ret uu____10682
    | FStar_Reflection_Data.Tv_Type () ->
        FStar_All.pipe_left ret FStar_Syntax_Util.ktype
    | FStar_Reflection_Data.Tv_Refine (bv,t) ->
        let uu____10701 = FStar_Syntax_Util.refine bv t  in
        FStar_All.pipe_left ret uu____10701
    | FStar_Reflection_Data.Tv_Const c ->
        let uu____10709 =
          let uu____10712 =
            let uu____10719 =
              let uu____10720 = FStar_Reflection_Basic.pack_const c  in
              FStar_Syntax_Syntax.Tm_constant uu____10720  in
            FStar_Syntax_Syntax.mk uu____10719  in
          uu____10712 FStar_Pervasives_Native.None FStar_Range.dummyRange  in
        FStar_All.pipe_left ret uu____10709
    | FStar_Reflection_Data.Tv_Uvar (_u,ctx_u_s) ->
        let uu____10730 =
          FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_uvar ctx_u_s)
            FStar_Pervasives_Native.None FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____10730
    | FStar_Reflection_Data.Tv_Let (false ,bv,t1,t2) ->
        let lb =
          FStar_Syntax_Util.mk_letbinding (FStar_Util.Inl bv) []
            bv.FStar_Syntax_Syntax.sort FStar_Parser_Const.effect_Tot_lid t1
            [] FStar_Range.dummyRange
           in
        let uu____10743 =
          let uu____10746 =
            let uu____10753 =
              let uu____10754 =
                let uu____10767 =
                  let uu____10770 =
                    let uu____10771 = FStar_Syntax_Syntax.mk_binder bv  in
                    [uu____10771]  in
                  FStar_Syntax_Subst.close uu____10770 t2  in
                ((false, [lb]), uu____10767)  in
              FStar_Syntax_Syntax.Tm_let uu____10754  in
            FStar_Syntax_Syntax.mk uu____10753  in
          uu____10746 FStar_Pervasives_Native.None FStar_Range.dummyRange  in
        FStar_All.pipe_left ret uu____10743
    | FStar_Reflection_Data.Tv_Let (true ,bv,t1,t2) ->
        let lb =
          FStar_Syntax_Util.mk_letbinding (FStar_Util.Inl bv) []
            bv.FStar_Syntax_Syntax.sort FStar_Parser_Const.effect_Tot_lid t1
            [] FStar_Range.dummyRange
           in
        let uu____10807 = FStar_Syntax_Subst.close_let_rec [lb] t2  in
        (match uu____10807 with
         | (lbs,body) ->
             let uu____10822 =
               FStar_Syntax_Syntax.mk
                 (FStar_Syntax_Syntax.Tm_let ((true, lbs), body))
                 FStar_Pervasives_Native.None FStar_Range.dummyRange
                in
             FStar_All.pipe_left ret uu____10822)
    | FStar_Reflection_Data.Tv_Match (t,brs) ->
        let wrap v1 =
          {
            FStar_Syntax_Syntax.v = v1;
            FStar_Syntax_Syntax.p = FStar_Range.dummyRange
          }  in
        let rec pack_pat p =
          match p with
          | FStar_Reflection_Data.Pat_Constant c ->
              let uu____10860 =
                let uu____10861 = FStar_Reflection_Basic.pack_const c  in
                FStar_Syntax_Syntax.Pat_constant uu____10861  in
              FStar_All.pipe_left wrap uu____10860
          | FStar_Reflection_Data.Pat_Cons (fv,ps) ->
              let uu____10868 =
                let uu____10869 =
                  let uu____10882 =
                    FStar_List.map
                      (fun p1  ->
                         let uu____10898 = pack_pat p1  in
                         (uu____10898, false)) ps
                     in
                  (fv, uu____10882)  in
                FStar_Syntax_Syntax.Pat_cons uu____10869  in
              FStar_All.pipe_left wrap uu____10868
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
            (fun uu___93_10944  ->
               match uu___93_10944 with
               | (pat,t1) ->
                   let uu____10961 = pack_pat pat  in
                   (uu____10961, FStar_Pervasives_Native.None, t1)) brs
           in
        let brs2 = FStar_List.map FStar_Syntax_Subst.close_branch brs1  in
        let uu____11009 =
          FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_match (t, brs2))
            FStar_Pervasives_Native.None FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____11009
    | FStar_Reflection_Data.Tv_AscribedT (e,t,tacopt) ->
        let uu____11041 =
          FStar_Syntax_Syntax.mk
            (FStar_Syntax_Syntax.Tm_ascribed
               (e, ((FStar_Util.Inl t), tacopt),
                 FStar_Pervasives_Native.None)) FStar_Pervasives_Native.None
            FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____11041
    | FStar_Reflection_Data.Tv_AscribedC (e,c,tacopt) ->
        let uu____11091 =
          FStar_Syntax_Syntax.mk
            (FStar_Syntax_Syntax.Tm_ascribed
               (e, ((FStar_Util.Inr c), tacopt),
                 FStar_Pervasives_Native.None)) FStar_Pervasives_Native.None
            FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____11091
    | FStar_Reflection_Data.Tv_Unknown  ->
        let uu____11134 =
          FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown
            FStar_Pervasives_Native.None FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____11134
  
let (goal_of_goal_ty :
  env ->
    FStar_Reflection_Data.typ ->
      (FStar_Tactics_Types.goal,FStar_TypeChecker_Env.guard_t)
        FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun typ  ->
      let uu____11155 =
        FStar_TypeChecker_Util.new_implicit_var "proofstate_of_goal_ty"
          typ.FStar_Syntax_Syntax.pos env typ
         in
      match uu____11155 with
      | (u,ctx_uvars,g_u) ->
          let uu____11187 = FStar_List.hd ctx_uvars  in
          (match uu____11187 with
           | (ctx_uvar,uu____11201) ->
               let g =
                 let uu____11203 = FStar_Options.peek ()  in
                 FStar_Tactics_Types.mk_goal env ctx_uvar uu____11203 false
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
        let uu____11223 = goal_of_goal_ty env typ  in
        match uu____11223 with
        | (g,g_u) ->
            let ps =
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
                FStar_Tactics_Types.freshness = (Prims.parse_int "0")
              }  in
            let uu____11239 = FStar_Tactics_Types.goal_witness g  in
            (ps, uu____11239)
  