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
           let uu____245 = run t1 p  in
           match uu____245 with
           | FStar_Tactics_Result.Success (a,q) ->
               let uu____252 = t2 a  in run uu____252 q
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
    let uu____272 =
      FStar_Syntax_Unionfind.find uv.FStar_Syntax_Syntax.ctx_uvar_head  in
    match uu____272 with
    | FStar_Pervasives_Native.Some t -> FStar_Pervasives_Native.Some t
    | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
  
let (check_goal_solved :
  FStar_Tactics_Types.goal ->
    FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  = fun goal  -> get_uvar_solved goal.FStar_Tactics_Types.goal_ctx_uvar 
let (goal_to_string_verbose : FStar_Tactics_Types.goal -> Prims.string) =
  fun g  ->
    let uu____290 =
      FStar_Syntax_Print.ctx_uvar_to_string
        g.FStar_Tactics_Types.goal_ctx_uvar
       in
    let uu____291 =
      let uu____292 = check_goal_solved g  in
      match uu____292 with
      | FStar_Pervasives_Native.None  -> ""
      | FStar_Pervasives_Native.Some t ->
          let uu____296 = FStar_Syntax_Print.term_to_string t  in
          FStar_Util.format1 "\tGOAL ALREADY SOLVED!: %s" uu____296
       in
    FStar_Util.format2 "%s%s" uu____290 uu____291
  
let (goal_to_string :
  FStar_Tactics_Types.proofstate -> FStar_Tactics_Types.goal -> Prims.string)
  =
  fun ps  ->
    fun g  ->
      let uu____307 =
        (FStar_Options.print_implicits ()) ||
          ps.FStar_Tactics_Types.tac_verb_dbg
         in
      if uu____307
      then goal_to_string_verbose g
      else
        (let w =
           let uu____310 =
             get_uvar_solved g.FStar_Tactics_Types.goal_ctx_uvar  in
           match uu____310 with
           | FStar_Pervasives_Native.None  -> "_"
           | FStar_Pervasives_Native.Some t ->
               let uu____314 = FStar_Tactics_Types.goal_env g  in
               tts uu____314 t
            in
         let uu____315 =
           FStar_Syntax_Print.binders_to_string ", "
             (g.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_binders
            in
         let uu____316 =
           let uu____317 = FStar_Tactics_Types.goal_env g  in
           tts uu____317
             (g.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_typ
            in
         FStar_Util.format3 "%s |- %s : %s" uu____315 w uu____316)
  
let (tacprint : Prims.string -> unit) =
  fun s  -> FStar_Util.print1 "TAC>> %s\n" s 
let (tacprint1 : Prims.string -> Prims.string -> unit) =
  fun s  ->
    fun x  ->
      let uu____333 = FStar_Util.format1 s x  in
      FStar_Util.print1 "TAC>> %s\n" uu____333
  
let (tacprint2 : Prims.string -> Prims.string -> Prims.string -> unit) =
  fun s  ->
    fun x  ->
      fun y  ->
        let uu____349 = FStar_Util.format2 s x y  in
        FStar_Util.print1 "TAC>> %s\n" uu____349
  
let (tacprint3 :
  Prims.string -> Prims.string -> Prims.string -> Prims.string -> unit) =
  fun s  ->
    fun x  ->
      fun y  ->
        fun z  ->
          let uu____370 = FStar_Util.format3 s x y z  in
          FStar_Util.print1 "TAC>> %s\n" uu____370
  
let (comp_to_typ : FStar_Syntax_Syntax.comp -> FStar_Reflection_Data.typ) =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Total (t,uu____377) -> t
    | FStar_Syntax_Syntax.GTotal (t,uu____387) -> t
    | FStar_Syntax_Syntax.Comp ct -> ct.FStar_Syntax_Syntax.result_typ
  
let (is_irrelevant : FStar_Tactics_Types.goal -> Prims.bool) =
  fun g  ->
    let uu____402 =
      let uu____407 =
        let uu____408 = FStar_Tactics_Types.goal_env g  in
        let uu____409 = FStar_Tactics_Types.goal_type g  in
        FStar_TypeChecker_Normalize.unfold_whnf uu____408 uu____409  in
      FStar_Syntax_Util.un_squash uu____407  in
    match uu____402 with
    | FStar_Pervasives_Native.Some t -> true
    | uu____415 -> false
  
let (print : Prims.string -> unit tac) = fun msg  -> tacprint msg; ret () 
let (debug : Prims.string -> unit tac) =
  fun msg  ->
    bind get
      (fun ps  ->
         (let uu____443 =
            let uu____444 =
              FStar_Ident.string_of_lid
                (ps.FStar_Tactics_Types.main_context).FStar_TypeChecker_Env.curmodule
               in
            FStar_Options.debug_module uu____444  in
          if uu____443 then tacprint msg else ());
         ret ())
  
let (dump_goal :
  FStar_Tactics_Types.proofstate -> FStar_Tactics_Types.goal -> unit) =
  fun ps  ->
    fun goal  ->
      let uu____457 = goal_to_string ps goal  in tacprint uu____457
  
let (dump_cur : FStar_Tactics_Types.proofstate -> Prims.string -> unit) =
  fun ps  ->
    fun msg  ->
      match ps.FStar_Tactics_Types.goals with
      | [] -> tacprint1 "No more goals (%s)" msg
      | h::uu____469 ->
          (tacprint1 "Current goal (%s):" msg;
           (let uu____473 = FStar_List.hd ps.FStar_Tactics_Types.goals  in
            dump_goal ps uu____473))
  
let (ps_to_string :
  (Prims.string,FStar_Tactics_Types.proofstate)
    FStar_Pervasives_Native.tuple2 -> Prims.string)
  =
  fun uu____482  ->
    match uu____482 with
    | (msg,ps) ->
        let p_imp uu____502 =
          match uu____502 with
          | (uu____511,uu____512,uv,uu____514) ->
              FStar_Syntax_Print.uvar_to_string
                uv.FStar_Syntax_Syntax.ctx_uvar_head
           in
        let uu____515 =
          let uu____518 =
            let uu____519 =
              FStar_Util.string_of_int ps.FStar_Tactics_Types.depth  in
            FStar_Util.format2 "State dump @ depth %s (%s):\n" uu____519 msg
             in
          let uu____520 =
            let uu____523 =
              if ps.FStar_Tactics_Types.entry_range <> FStar_Range.dummyRange
              then
                let uu____524 =
                  FStar_Range.string_of_def_range
                    ps.FStar_Tactics_Types.entry_range
                   in
                FStar_Util.format1 "Location: %s\n" uu____524
              else ""  in
            let uu____526 =
              let uu____529 =
                let uu____530 =
                  FStar_TypeChecker_Env.debug
                    ps.FStar_Tactics_Types.main_context
                    (FStar_Options.Other "Imp")
                   in
                if uu____530
                then
                  let uu____531 =
                    FStar_Common.string_of_list p_imp
                      ps.FStar_Tactics_Types.all_implicits
                     in
                  FStar_Util.format1 "Imps: %s\n" uu____531
                else ""  in
              let uu____541 =
                let uu____544 =
                  let uu____545 =
                    FStar_Util.string_of_int
                      (FStar_List.length ps.FStar_Tactics_Types.goals)
                     in
                  let uu____546 =
                    let uu____547 =
                      FStar_List.map (goal_to_string ps)
                        ps.FStar_Tactics_Types.goals
                       in
                    FStar_String.concat "\n" uu____547  in
                  FStar_Util.format2 "ACTIVE goals (%s):\n%s\n" uu____545
                    uu____546
                   in
                let uu____550 =
                  let uu____553 =
                    let uu____554 =
                      FStar_Util.string_of_int
                        (FStar_List.length ps.FStar_Tactics_Types.smt_goals)
                       in
                    let uu____555 =
                      let uu____556 =
                        FStar_List.map (goal_to_string ps)
                          ps.FStar_Tactics_Types.smt_goals
                         in
                      FStar_String.concat "\n" uu____556  in
                    FStar_Util.format2 "SMT goals (%s):\n%s\n" uu____554
                      uu____555
                     in
                  [uu____553]  in
                uu____544 :: uu____550  in
              uu____529 :: uu____541  in
            uu____523 :: uu____526  in
          uu____518 :: uu____520  in
        FStar_String.concat "" uu____515
  
let (goal_to_json : FStar_Tactics_Types.goal -> FStar_Util.json) =
  fun g  ->
    let g_binders =
      let uu____565 =
        let uu____566 = FStar_Tactics_Types.goal_env g  in
        FStar_TypeChecker_Env.all_binders uu____566  in
      let uu____567 =
        let uu____572 =
          let uu____573 = FStar_Tactics_Types.goal_env g  in
          FStar_TypeChecker_Env.dsenv uu____573  in
        FStar_Syntax_Print.binders_to_json uu____572  in
      FStar_All.pipe_right uu____565 uu____567  in
    let uu____574 =
      let uu____581 =
        let uu____588 =
          let uu____593 =
            let uu____594 =
              let uu____601 =
                let uu____606 =
                  let uu____607 =
                    let uu____608 = FStar_Tactics_Types.goal_env g  in
                    let uu____609 = FStar_Tactics_Types.goal_witness g  in
                    tts uu____608 uu____609  in
                  FStar_Util.JsonStr uu____607  in
                ("witness", uu____606)  in
              let uu____610 =
                let uu____617 =
                  let uu____622 =
                    let uu____623 =
                      let uu____624 = FStar_Tactics_Types.goal_env g  in
                      let uu____625 = FStar_Tactics_Types.goal_type g  in
                      tts uu____624 uu____625  in
                    FStar_Util.JsonStr uu____623  in
                  ("type", uu____622)  in
                [uu____617]  in
              uu____601 :: uu____610  in
            FStar_Util.JsonAssoc uu____594  in
          ("goal", uu____593)  in
        [uu____588]  in
      ("hyps", g_binders) :: uu____581  in
    FStar_Util.JsonAssoc uu____574
  
let (ps_to_json :
  (Prims.string,FStar_Tactics_Types.proofstate)
    FStar_Pervasives_Native.tuple2 -> FStar_Util.json)
  =
  fun uu____658  ->
    match uu____658 with
    | (msg,ps) ->
        let uu____665 =
          let uu____672 =
            let uu____679 =
              let uu____686 =
                let uu____693 =
                  let uu____698 =
                    let uu____699 =
                      FStar_List.map goal_to_json
                        ps.FStar_Tactics_Types.goals
                       in
                    FStar_Util.JsonList uu____699  in
                  ("goals", uu____698)  in
                let uu____702 =
                  let uu____709 =
                    let uu____714 =
                      let uu____715 =
                        FStar_List.map goal_to_json
                          ps.FStar_Tactics_Types.smt_goals
                         in
                      FStar_Util.JsonList uu____715  in
                    ("smt-goals", uu____714)  in
                  [uu____709]  in
                uu____693 :: uu____702  in
              ("depth", (FStar_Util.JsonInt (ps.FStar_Tactics_Types.depth)))
                :: uu____686
               in
            ("label", (FStar_Util.JsonStr msg)) :: uu____679  in
          let uu____738 =
            if ps.FStar_Tactics_Types.entry_range <> FStar_Range.dummyRange
            then
              let uu____751 =
                let uu____756 =
                  FStar_Range.json_of_def_range
                    ps.FStar_Tactics_Types.entry_range
                   in
                ("location", uu____756)  in
              [uu____751]
            else []  in
          FStar_List.append uu____672 uu____738  in
        FStar_Util.JsonAssoc uu____665
  
let (dump_proofstate :
  FStar_Tactics_Types.proofstate -> Prims.string -> unit) =
  fun ps  ->
    fun msg  ->
      FStar_Options.with_saved_options
        (fun uu____786  ->
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
         (let uu____809 = FStar_Tactics_Types.subst_proof_state subst1 ps  in
          dump_cur uu____809 msg);
         FStar_Tactics_Result.Success ((), ps))
  
let (print_proof_state : Prims.string -> unit tac) =
  fun msg  ->
    mk_tac
      (fun ps  ->
         let psc = ps.FStar_Tactics_Types.psc  in
         let subst1 = FStar_TypeChecker_Normalize.psc_subst psc  in
         (let uu____827 = FStar_Tactics_Types.subst_proof_state subst1 ps  in
          dump_proofstate uu____827 msg);
         FStar_Tactics_Result.Success ((), ps))
  
let mlog : 'a . (unit -> unit) -> (unit -> 'a tac) -> 'a tac =
  fun f  -> fun cont  -> bind get (fun ps  -> log ps f; cont ()) 
let fail : 'a . Prims.string -> 'a tac =
  fun msg  ->
    mk_tac
      (fun ps  ->
         (let uu____881 =
            FStar_TypeChecker_Env.debug ps.FStar_Tactics_Types.main_context
              (FStar_Options.Other "TacFail")
             in
          if uu____881
          then dump_proofstate ps (Prims.strcat "TACTIC FAILING: " msg)
          else ());
         FStar_Tactics_Result.Failed (msg, ps))
  
let fail1 : 'Auu____889 . Prims.string -> Prims.string -> 'Auu____889 tac =
  fun msg  ->
    fun x  -> let uu____902 = FStar_Util.format1 msg x  in fail uu____902
  
let fail2 :
  'Auu____911 .
    Prims.string -> Prims.string -> Prims.string -> 'Auu____911 tac
  =
  fun msg  ->
    fun x  ->
      fun y  -> let uu____929 = FStar_Util.format2 msg x y  in fail uu____929
  
let fail3 :
  'Auu____940 .
    Prims.string ->
      Prims.string -> Prims.string -> Prims.string -> 'Auu____940 tac
  =
  fun msg  ->
    fun x  ->
      fun y  ->
        fun z  ->
          let uu____963 = FStar_Util.format3 msg x y z  in fail uu____963
  
let fail4 :
  'Auu____976 .
    Prims.string ->
      Prims.string ->
        Prims.string -> Prims.string -> Prims.string -> 'Auu____976 tac
  =
  fun msg  ->
    fun x  ->
      fun y  ->
        fun z  ->
          fun w  ->
            let uu____1004 = FStar_Util.format4 msg x y z w  in
            fail uu____1004
  
let trytac' : 'a . 'a tac -> (Prims.string,'a) FStar_Util.either tac =
  fun t  ->
    mk_tac
      (fun ps  ->
         let tx = FStar_Syntax_Unionfind.new_transaction ()  in
         let uu____1037 = run t ps  in
         match uu____1037 with
         | FStar_Tactics_Result.Success (a,q) ->
             (FStar_Syntax_Unionfind.commit tx;
              FStar_Tactics_Result.Success ((FStar_Util.Inr a), q))
         | FStar_Tactics_Result.Failed (m,q) ->
             (FStar_Syntax_Unionfind.rollback tx;
              (let ps1 =
                 let uu___347_1061 = ps  in
                 {
                   FStar_Tactics_Types.main_context =
                     (uu___347_1061.FStar_Tactics_Types.main_context);
                   FStar_Tactics_Types.main_goal =
                     (uu___347_1061.FStar_Tactics_Types.main_goal);
                   FStar_Tactics_Types.all_implicits =
                     (uu___347_1061.FStar_Tactics_Types.all_implicits);
                   FStar_Tactics_Types.goals =
                     (uu___347_1061.FStar_Tactics_Types.goals);
                   FStar_Tactics_Types.smt_goals =
                     (uu___347_1061.FStar_Tactics_Types.smt_goals);
                   FStar_Tactics_Types.depth =
                     (uu___347_1061.FStar_Tactics_Types.depth);
                   FStar_Tactics_Types.__dump =
                     (uu___347_1061.FStar_Tactics_Types.__dump);
                   FStar_Tactics_Types.psc =
                     (uu___347_1061.FStar_Tactics_Types.psc);
                   FStar_Tactics_Types.entry_range =
                     (uu___347_1061.FStar_Tactics_Types.entry_range);
                   FStar_Tactics_Types.guard_policy =
                     (uu___347_1061.FStar_Tactics_Types.guard_policy);
                   FStar_Tactics_Types.freshness =
                     (q.FStar_Tactics_Types.freshness);
                   FStar_Tactics_Types.tac_verb_dbg =
                     (uu___347_1061.FStar_Tactics_Types.tac_verb_dbg)
                 }  in
               FStar_Tactics_Result.Success ((FStar_Util.Inl m), ps1))))
  
let trytac : 'a . 'a tac -> 'a FStar_Pervasives_Native.option tac =
  fun t  ->
    let uu____1088 = trytac' t  in
    bind uu____1088
      (fun r  ->
         match r with
         | FStar_Util.Inr v1 -> ret (FStar_Pervasives_Native.Some v1)
         | FStar_Util.Inl uu____1115 -> ret FStar_Pervasives_Native.None)
  
let trytac_exn : 'a . 'a tac -> 'a FStar_Pervasives_Native.option tac =
  fun t  ->
    mk_tac
      (fun ps  ->
         try let uu____1151 = trytac t  in run uu____1151 ps
         with
         | FStar_Errors.Err (uu____1167,msg) ->
             (log ps
                (fun uu____1171  ->
                   FStar_Util.print1 "trytac_exn error: (%s)" msg);
              FStar_Tactics_Result.Success (FStar_Pervasives_Native.None, ps))
         | FStar_Errors.Error (uu____1176,msg,uu____1178) ->
             (log ps
                (fun uu____1181  ->
                   FStar_Util.print1 "trytac_exn error: (%s)" msg);
              FStar_Tactics_Result.Success (FStar_Pervasives_Native.None, ps)))
  
let wrap_err : 'a . Prims.string -> 'a tac -> 'a tac =
  fun pref  ->
    fun t  ->
      mk_tac
        (fun ps  ->
           let uu____1214 = run t ps  in
           match uu____1214 with
           | FStar_Tactics_Result.Success (a,q) ->
               FStar_Tactics_Result.Success (a, q)
           | FStar_Tactics_Result.Failed (msg,q) ->
               FStar_Tactics_Result.Failed
                 ((Prims.strcat pref (Prims.strcat ": " msg)), q))
  
let (set : FStar_Tactics_Types.proofstate -> unit tac) =
  fun p  -> mk_tac (fun uu____1233  -> FStar_Tactics_Result.Success ((), p)) 
let (__do_unify :
  env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.bool tac)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        (let uu____1254 =
           FStar_TypeChecker_Env.debug env (FStar_Options.Other "1346")  in
         if uu____1254
         then
           let uu____1255 = FStar_Syntax_Print.term_to_string t1  in
           let uu____1256 = FStar_Syntax_Print.term_to_string t2  in
           FStar_Util.print2 "%%%%%%%%do_unify %s =? %s\n" uu____1255
             uu____1256
         else ());
        (try
           let res = FStar_TypeChecker_Rel.teq_nosmt env t1 t2  in
           (let uu____1268 =
              FStar_TypeChecker_Env.debug env (FStar_Options.Other "1346")
               in
            if uu____1268
            then
              let uu____1269 = FStar_Util.string_of_bool res  in
              let uu____1270 = FStar_Syntax_Print.term_to_string t1  in
              let uu____1271 = FStar_Syntax_Print.term_to_string t2  in
              FStar_Util.print3 "%%%%%%%%do_unify (RESULT %s) %s =? %s\n"
                uu____1269 uu____1270 uu____1271
            else ());
           ret res
         with
         | FStar_Errors.Err (uu____1279,msg) ->
             mlog
               (fun uu____1282  ->
                  FStar_Util.print1 ">> do_unify error, (%s)\n" msg)
               (fun uu____1284  -> ret false)
         | FStar_Errors.Error (uu____1285,msg,r) ->
             mlog
               (fun uu____1290  ->
                  let uu____1291 = FStar_Range.string_of_range r  in
                  FStar_Util.print2 ">> do_unify error, (%s) at (%s)\n" msg
                    uu____1291) (fun uu____1293  -> ret false))
  
let (do_unify :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.bool tac)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        bind idtac
          (fun uu____1316  ->
             (let uu____1318 =
                FStar_TypeChecker_Env.debug env (FStar_Options.Other "1346")
                 in
              if uu____1318
              then
                (FStar_Options.push ();
                 (let uu____1320 =
                    FStar_Options.set_options FStar_Options.Set
                      "--debug_level Rel --debug_level RelCheck"
                     in
                  ()))
              else ());
             (let uu____1322 = __do_unify env t1 t2  in
              bind uu____1322
                (fun r  ->
                   (let uu____1329 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "1346")
                       in
                    if uu____1329 then FStar_Options.pop () else ());
                   ret r)))
  
let (remove_solved_goals : unit tac) =
  bind get
    (fun ps  ->
       let ps' =
         let uu___352_1337 = ps  in
         let uu____1338 =
           FStar_List.filter
             (fun g  ->
                let uu____1344 = check_goal_solved g  in
                FStar_Option.isNone uu____1344) ps.FStar_Tactics_Types.goals
            in
         {
           FStar_Tactics_Types.main_context =
             (uu___352_1337.FStar_Tactics_Types.main_context);
           FStar_Tactics_Types.main_goal =
             (uu___352_1337.FStar_Tactics_Types.main_goal);
           FStar_Tactics_Types.all_implicits =
             (uu___352_1337.FStar_Tactics_Types.all_implicits);
           FStar_Tactics_Types.goals = uu____1338;
           FStar_Tactics_Types.smt_goals =
             (uu___352_1337.FStar_Tactics_Types.smt_goals);
           FStar_Tactics_Types.depth =
             (uu___352_1337.FStar_Tactics_Types.depth);
           FStar_Tactics_Types.__dump =
             (uu___352_1337.FStar_Tactics_Types.__dump);
           FStar_Tactics_Types.psc = (uu___352_1337.FStar_Tactics_Types.psc);
           FStar_Tactics_Types.entry_range =
             (uu___352_1337.FStar_Tactics_Types.entry_range);
           FStar_Tactics_Types.guard_policy =
             (uu___352_1337.FStar_Tactics_Types.guard_policy);
           FStar_Tactics_Types.freshness =
             (uu___352_1337.FStar_Tactics_Types.freshness);
           FStar_Tactics_Types.tac_verb_dbg =
             (uu___352_1337.FStar_Tactics_Types.tac_verb_dbg)
         }  in
       set ps')
  
let (set_solution :
  FStar_Tactics_Types.goal -> FStar_Syntax_Syntax.term -> unit tac) =
  fun goal  ->
    fun solution  ->
      let uu____1361 =
        FStar_Syntax_Unionfind.find
          (goal.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_head
         in
      match uu____1361 with
      | FStar_Pervasives_Native.Some uu____1366 ->
          let uu____1367 =
            let uu____1368 = goal_to_string_verbose goal  in
            FStar_Util.format1 "Goal %s is already solved" uu____1368  in
          fail uu____1367
      | FStar_Pervasives_Native.None  ->
          (FStar_Syntax_Unionfind.change
             (goal.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_head
             solution;
           ret ())
  
let (trysolve :
  FStar_Tactics_Types.goal -> FStar_Syntax_Syntax.term -> Prims.bool tac) =
  fun goal  ->
    fun solution  ->
      let uu____1384 = FStar_Tactics_Types.goal_env goal  in
      let uu____1385 = FStar_Tactics_Types.goal_witness goal  in
      do_unify uu____1384 solution uu____1385
  
let (__dismiss : unit tac) =
  bind get
    (fun p  ->
       let uu____1391 =
         let uu___353_1392 = p  in
         let uu____1393 = FStar_List.tl p.FStar_Tactics_Types.goals  in
         {
           FStar_Tactics_Types.main_context =
             (uu___353_1392.FStar_Tactics_Types.main_context);
           FStar_Tactics_Types.main_goal =
             (uu___353_1392.FStar_Tactics_Types.main_goal);
           FStar_Tactics_Types.all_implicits =
             (uu___353_1392.FStar_Tactics_Types.all_implicits);
           FStar_Tactics_Types.goals = uu____1393;
           FStar_Tactics_Types.smt_goals =
             (uu___353_1392.FStar_Tactics_Types.smt_goals);
           FStar_Tactics_Types.depth =
             (uu___353_1392.FStar_Tactics_Types.depth);
           FStar_Tactics_Types.__dump =
             (uu___353_1392.FStar_Tactics_Types.__dump);
           FStar_Tactics_Types.psc = (uu___353_1392.FStar_Tactics_Types.psc);
           FStar_Tactics_Types.entry_range =
             (uu___353_1392.FStar_Tactics_Types.entry_range);
           FStar_Tactics_Types.guard_policy =
             (uu___353_1392.FStar_Tactics_Types.guard_policy);
           FStar_Tactics_Types.freshness =
             (uu___353_1392.FStar_Tactics_Types.freshness);
           FStar_Tactics_Types.tac_verb_dbg =
             (uu___353_1392.FStar_Tactics_Types.tac_verb_dbg)
         }  in
       set uu____1391)
  
let (dismiss : unit -> unit tac) =
  fun uu____1402  ->
    bind get
      (fun p  ->
         match p.FStar_Tactics_Types.goals with
         | [] -> fail "dismiss: no more goals"
         | uu____1409 -> __dismiss)
  
let (solve :
  FStar_Tactics_Types.goal -> FStar_Syntax_Syntax.term -> unit tac) =
  fun goal  ->
    fun solution  ->
      let e = FStar_Tactics_Types.goal_env goal  in
      mlog
        (fun uu____1430  ->
           let uu____1431 =
             let uu____1432 = FStar_Tactics_Types.goal_witness goal  in
             FStar_Syntax_Print.term_to_string uu____1432  in
           let uu____1433 = FStar_Syntax_Print.term_to_string solution  in
           FStar_Util.print2 "solve %s := %s\n" uu____1431 uu____1433)
        (fun uu____1436  ->
           let uu____1437 = trysolve goal solution  in
           bind uu____1437
             (fun b  ->
                if b
                then bind __dismiss (fun uu____1445  -> remove_solved_goals)
                else
                  (let uu____1447 =
                     let uu____1448 =
                       let uu____1449 = FStar_Tactics_Types.goal_env goal  in
                       tts uu____1449 solution  in
                     let uu____1450 =
                       let uu____1451 = FStar_Tactics_Types.goal_env goal  in
                       let uu____1452 = FStar_Tactics_Types.goal_witness goal
                          in
                       tts uu____1451 uu____1452  in
                     let uu____1453 =
                       let uu____1454 = FStar_Tactics_Types.goal_env goal  in
                       let uu____1455 = FStar_Tactics_Types.goal_type goal
                          in
                       tts uu____1454 uu____1455  in
                     FStar_Util.format3 "%s does not solve %s : %s"
                       uu____1448 uu____1450 uu____1453
                      in
                   fail uu____1447)))
  
let (solve' :
  FStar_Tactics_Types.goal -> FStar_Syntax_Syntax.term -> unit tac) =
  fun goal  ->
    fun solution  ->
      let uu____1470 = set_solution goal solution  in
      bind uu____1470
        (fun uu____1474  ->
           bind __dismiss (fun uu____1476  -> remove_solved_goals))
  
let (dismiss_all : unit tac) =
  bind get
    (fun p  ->
       set
         (let uu___354_1483 = p  in
          {
            FStar_Tactics_Types.main_context =
              (uu___354_1483.FStar_Tactics_Types.main_context);
            FStar_Tactics_Types.main_goal =
              (uu___354_1483.FStar_Tactics_Types.main_goal);
            FStar_Tactics_Types.all_implicits =
              (uu___354_1483.FStar_Tactics_Types.all_implicits);
            FStar_Tactics_Types.goals = [];
            FStar_Tactics_Types.smt_goals =
              (uu___354_1483.FStar_Tactics_Types.smt_goals);
            FStar_Tactics_Types.depth =
              (uu___354_1483.FStar_Tactics_Types.depth);
            FStar_Tactics_Types.__dump =
              (uu___354_1483.FStar_Tactics_Types.__dump);
            FStar_Tactics_Types.psc = (uu___354_1483.FStar_Tactics_Types.psc);
            FStar_Tactics_Types.entry_range =
              (uu___354_1483.FStar_Tactics_Types.entry_range);
            FStar_Tactics_Types.guard_policy =
              (uu___354_1483.FStar_Tactics_Types.guard_policy);
            FStar_Tactics_Types.freshness =
              (uu___354_1483.FStar_Tactics_Types.freshness);
            FStar_Tactics_Types.tac_verb_dbg =
              (uu___354_1483.FStar_Tactics_Types.tac_verb_dbg)
          }))
  
let (nwarn : Prims.int FStar_ST.ref) =
  FStar_Util.mk_ref (Prims.parse_int "0") 
let (check_valid_goal : FStar_Tactics_Types.goal -> unit) =
  fun g  ->
    let uu____1502 = FStar_Options.defensive ()  in
    if uu____1502
    then
      let b = true  in
      let env = FStar_Tactics_Types.goal_env g  in
      let b1 =
        b &&
          (let uu____1507 = FStar_Tactics_Types.goal_witness g  in
           FStar_TypeChecker_Env.closed env uu____1507)
         in
      let b2 =
        b1 &&
          (let uu____1510 = FStar_Tactics_Types.goal_type g  in
           FStar_TypeChecker_Env.closed env uu____1510)
         in
      let rec aux b3 e =
        let uu____1522 = FStar_TypeChecker_Env.pop_bv e  in
        match uu____1522 with
        | FStar_Pervasives_Native.None  -> b3
        | FStar_Pervasives_Native.Some (bv,e1) ->
            let b4 =
              b3 &&
                (FStar_TypeChecker_Env.closed e1 bv.FStar_Syntax_Syntax.sort)
               in
            aux b4 e1
         in
      let uu____1540 =
        (let uu____1543 = aux b2 env  in Prims.op_Negation uu____1543) &&
          (let uu____1545 = FStar_ST.op_Bang nwarn  in
           uu____1545 < (Prims.parse_int "5"))
         in
      (if uu____1540
       then
         ((let uu____1570 =
             let uu____1571 = FStar_Tactics_Types.goal_type g  in
             uu____1571.FStar_Syntax_Syntax.pos  in
           let uu____1574 =
             let uu____1579 =
               let uu____1580 = goal_to_string_verbose g  in
               FStar_Util.format1
                 "The following goal is ill-formed. Keeping calm and carrying on...\n<%s>\n\n"
                 uu____1580
                in
             (FStar_Errors.Warning_IllFormedGoal, uu____1579)  in
           FStar_Errors.log_issue uu____1570 uu____1574);
          (let uu____1581 =
             let uu____1582 = FStar_ST.op_Bang nwarn  in
             uu____1582 + (Prims.parse_int "1")  in
           FStar_ST.op_Colon_Equals nwarn uu____1581))
       else ())
    else ()
  
let (add_goals : FStar_Tactics_Types.goal Prims.list -> unit tac) =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___355_1650 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___355_1650.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___355_1650.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___355_1650.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (FStar_List.append gs p.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (uu___355_1650.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___355_1650.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___355_1650.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___355_1650.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___355_1650.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___355_1650.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___355_1650.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___355_1650.FStar_Tactics_Types.tac_verb_dbg)
            }))
  
let (add_smt_goals : FStar_Tactics_Types.goal Prims.list -> unit tac) =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___356_1670 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___356_1670.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___356_1670.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___356_1670.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___356_1670.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (FStar_List.append gs p.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___356_1670.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___356_1670.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___356_1670.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___356_1670.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___356_1670.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___356_1670.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___356_1670.FStar_Tactics_Types.tac_verb_dbg)
            }))
  
let (push_goals : FStar_Tactics_Types.goal Prims.list -> unit tac) =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___357_1690 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___357_1690.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___357_1690.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___357_1690.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (FStar_List.append p.FStar_Tactics_Types.goals gs);
              FStar_Tactics_Types.smt_goals =
                (uu___357_1690.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___357_1690.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___357_1690.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___357_1690.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___357_1690.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___357_1690.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___357_1690.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___357_1690.FStar_Tactics_Types.tac_verb_dbg)
            }))
  
let (push_smt_goals : FStar_Tactics_Types.goal Prims.list -> unit tac) =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___358_1710 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___358_1710.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___358_1710.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___358_1710.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___358_1710.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (FStar_List.append p.FStar_Tactics_Types.smt_goals gs);
              FStar_Tactics_Types.depth =
                (uu___358_1710.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___358_1710.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___358_1710.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___358_1710.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___358_1710.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___358_1710.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___358_1710.FStar_Tactics_Types.tac_verb_dbg)
            }))
  
let (replace_cur : FStar_Tactics_Types.goal -> unit tac) =
  fun g  -> bind __dismiss (fun uu____1721  -> add_goals [g]) 
let (add_implicits : implicits -> unit tac) =
  fun i  ->
    bind get
      (fun p  ->
         set
           (let uu___359_1735 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___359_1735.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___359_1735.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (FStar_List.append i p.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___359_1735.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (uu___359_1735.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___359_1735.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___359_1735.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___359_1735.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___359_1735.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___359_1735.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___359_1735.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___359_1735.FStar_Tactics_Types.tac_verb_dbg)
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
        let uu____1771 =
          FStar_TypeChecker_Util.new_implicit_var reason
            typ.FStar_Syntax_Syntax.pos env typ
           in
        match uu____1771 with
        | (u,ctx_uvar,g_u) ->
            let uu____1805 =
              add_implicits g_u.FStar_TypeChecker_Env.implicits  in
            bind uu____1805
              (fun uu____1814  ->
                 let uu____1815 =
                   let uu____1820 =
                     let uu____1821 = FStar_List.hd ctx_uvar  in
                     FStar_Pervasives_Native.fst uu____1821  in
                   (u, uu____1820)  in
                 ret uu____1815)
  
let (is_true : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____1839 = FStar_Syntax_Util.un_squash t  in
    match uu____1839 with
    | FStar_Pervasives_Native.Some t' ->
        let uu____1849 =
          let uu____1850 = FStar_Syntax_Subst.compress t'  in
          uu____1850.FStar_Syntax_Syntax.n  in
        (match uu____1849 with
         | FStar_Syntax_Syntax.Tm_fvar fv ->
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.true_lid
         | uu____1854 -> false)
    | uu____1855 -> false
  
let (is_false : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____1865 = FStar_Syntax_Util.un_squash t  in
    match uu____1865 with
    | FStar_Pervasives_Native.Some t' ->
        let uu____1875 =
          let uu____1876 = FStar_Syntax_Subst.compress t'  in
          uu____1876.FStar_Syntax_Syntax.n  in
        (match uu____1875 with
         | FStar_Syntax_Syntax.Tm_fvar fv ->
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.false_lid
         | uu____1880 -> false)
    | uu____1881 -> false
  
let (cur_goal : unit -> FStar_Tactics_Types.goal tac) =
  fun uu____1892  ->
    bind get
      (fun p  ->
         match p.FStar_Tactics_Types.goals with
         | [] -> fail "No more goals (1)"
         | hd1::tl1 ->
             let uu____1903 =
               FStar_Syntax_Unionfind.find
                 (hd1.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_head
                in
             (match uu____1903 with
              | FStar_Pervasives_Native.None  -> ret hd1
              | FStar_Pervasives_Native.Some t ->
                  ((let uu____1910 = goal_to_string_verbose hd1  in
                    let uu____1911 = FStar_Syntax_Print.term_to_string t  in
                    FStar_Util.print2
                      "!!!!!!!!!!!! GOAL IS ALREADY SOLVED! %s\nsol is %s\n"
                      uu____1910 uu____1911);
                   ret hd1)))
  
let (tadmit : unit -> unit tac) =
  fun uu____1918  ->
    let uu____1921 =
      bind get
        (fun ps  ->
           let uu____1927 = cur_goal ()  in
           bind uu____1927
             (fun g  ->
                (let uu____1934 =
                   let uu____1935 = FStar_Tactics_Types.goal_type g  in
                   uu____1935.FStar_Syntax_Syntax.pos  in
                 let uu____1938 =
                   let uu____1943 =
                     let uu____1944 = goal_to_string ps g  in
                     FStar_Util.format1 "Tactics admitted goal <%s>\n\n"
                       uu____1944
                      in
                   (FStar_Errors.Warning_TacAdmit, uu____1943)  in
                 FStar_Errors.log_issue uu____1934 uu____1938);
                solve' g FStar_Syntax_Util.exp_unit))
       in
    FStar_All.pipe_left (wrap_err "tadmit") uu____1921
  
let (fresh : unit -> FStar_BigInt.t tac) =
  fun uu____1955  ->
    bind get
      (fun ps  ->
         let n1 = ps.FStar_Tactics_Types.freshness  in
         let ps1 =
           let uu___360_1965 = ps  in
           {
             FStar_Tactics_Types.main_context =
               (uu___360_1965.FStar_Tactics_Types.main_context);
             FStar_Tactics_Types.main_goal =
               (uu___360_1965.FStar_Tactics_Types.main_goal);
             FStar_Tactics_Types.all_implicits =
               (uu___360_1965.FStar_Tactics_Types.all_implicits);
             FStar_Tactics_Types.goals =
               (uu___360_1965.FStar_Tactics_Types.goals);
             FStar_Tactics_Types.smt_goals =
               (uu___360_1965.FStar_Tactics_Types.smt_goals);
             FStar_Tactics_Types.depth =
               (uu___360_1965.FStar_Tactics_Types.depth);
             FStar_Tactics_Types.__dump =
               (uu___360_1965.FStar_Tactics_Types.__dump);
             FStar_Tactics_Types.psc =
               (uu___360_1965.FStar_Tactics_Types.psc);
             FStar_Tactics_Types.entry_range =
               (uu___360_1965.FStar_Tactics_Types.entry_range);
             FStar_Tactics_Types.guard_policy =
               (uu___360_1965.FStar_Tactics_Types.guard_policy);
             FStar_Tactics_Types.freshness = (n1 + (Prims.parse_int "1"));
             FStar_Tactics_Types.tac_verb_dbg =
               (uu___360_1965.FStar_Tactics_Types.tac_verb_dbg)
           }  in
         let uu____1966 = set ps1  in
         bind uu____1966
           (fun uu____1971  ->
              let uu____1972 = FStar_BigInt.of_int_fs n1  in ret uu____1972))
  
let (ngoals : unit -> FStar_BigInt.t tac) =
  fun uu____1979  ->
    bind get
      (fun ps  ->
         let n1 = FStar_List.length ps.FStar_Tactics_Types.goals  in
         let uu____1987 = FStar_BigInt.of_int_fs n1  in ret uu____1987)
  
let (ngoals_smt : unit -> FStar_BigInt.t tac) =
  fun uu____2000  ->
    bind get
      (fun ps  ->
         let n1 = FStar_List.length ps.FStar_Tactics_Types.smt_goals  in
         let uu____2008 = FStar_BigInt.of_int_fs n1  in ret uu____2008)
  
let (is_guard : unit -> Prims.bool tac) =
  fun uu____2021  ->
    let uu____2024 = cur_goal ()  in
    bind uu____2024 (fun g  -> ret g.FStar_Tactics_Types.is_guard)
  
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
            let uu____2056 = env.FStar_TypeChecker_Env.universe_of env phi
               in
            FStar_Syntax_Util.mk_squash uu____2056 phi  in
          let uu____2057 = new_uvar reason env typ  in
          bind uu____2057
            (fun uu____2072  ->
               match uu____2072 with
               | (uu____2079,ctx_uvar) ->
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
             (fun uu____2124  ->
                let uu____2125 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.print1 "Tac> __tc(%s)\n" uu____2125)
             (fun uu____2128  ->
                let e1 =
                  let uu___361_2130 = e  in
                  {
                    FStar_TypeChecker_Env.solver =
                      (uu___361_2130.FStar_TypeChecker_Env.solver);
                    FStar_TypeChecker_Env.range =
                      (uu___361_2130.FStar_TypeChecker_Env.range);
                    FStar_TypeChecker_Env.curmodule =
                      (uu___361_2130.FStar_TypeChecker_Env.curmodule);
                    FStar_TypeChecker_Env.gamma =
                      (uu___361_2130.FStar_TypeChecker_Env.gamma);
                    FStar_TypeChecker_Env.gamma_sig =
                      (uu___361_2130.FStar_TypeChecker_Env.gamma_sig);
                    FStar_TypeChecker_Env.gamma_cache =
                      (uu___361_2130.FStar_TypeChecker_Env.gamma_cache);
                    FStar_TypeChecker_Env.modules =
                      (uu___361_2130.FStar_TypeChecker_Env.modules);
                    FStar_TypeChecker_Env.expected_typ =
                      (uu___361_2130.FStar_TypeChecker_Env.expected_typ);
                    FStar_TypeChecker_Env.sigtab =
                      (uu___361_2130.FStar_TypeChecker_Env.sigtab);
                    FStar_TypeChecker_Env.is_pattern =
                      (uu___361_2130.FStar_TypeChecker_Env.is_pattern);
                    FStar_TypeChecker_Env.instantiate_imp =
                      (uu___361_2130.FStar_TypeChecker_Env.instantiate_imp);
                    FStar_TypeChecker_Env.effects =
                      (uu___361_2130.FStar_TypeChecker_Env.effects);
                    FStar_TypeChecker_Env.generalize =
                      (uu___361_2130.FStar_TypeChecker_Env.generalize);
                    FStar_TypeChecker_Env.letrecs =
                      (uu___361_2130.FStar_TypeChecker_Env.letrecs);
                    FStar_TypeChecker_Env.top_level =
                      (uu___361_2130.FStar_TypeChecker_Env.top_level);
                    FStar_TypeChecker_Env.check_uvars =
                      (uu___361_2130.FStar_TypeChecker_Env.check_uvars);
                    FStar_TypeChecker_Env.use_eq =
                      (uu___361_2130.FStar_TypeChecker_Env.use_eq);
                    FStar_TypeChecker_Env.is_iface =
                      (uu___361_2130.FStar_TypeChecker_Env.is_iface);
                    FStar_TypeChecker_Env.admit =
                      (uu___361_2130.FStar_TypeChecker_Env.admit);
                    FStar_TypeChecker_Env.lax =
                      (uu___361_2130.FStar_TypeChecker_Env.lax);
                    FStar_TypeChecker_Env.lax_universes =
                      (uu___361_2130.FStar_TypeChecker_Env.lax_universes);
                    FStar_TypeChecker_Env.phase1 =
                      (uu___361_2130.FStar_TypeChecker_Env.phase1);
                    FStar_TypeChecker_Env.failhard =
                      (uu___361_2130.FStar_TypeChecker_Env.failhard);
                    FStar_TypeChecker_Env.nosynth =
                      (uu___361_2130.FStar_TypeChecker_Env.nosynth);
                    FStar_TypeChecker_Env.uvar_subtyping = false;
                    FStar_TypeChecker_Env.tc_term =
                      (uu___361_2130.FStar_TypeChecker_Env.tc_term);
                    FStar_TypeChecker_Env.type_of =
                      (uu___361_2130.FStar_TypeChecker_Env.type_of);
                    FStar_TypeChecker_Env.universe_of =
                      (uu___361_2130.FStar_TypeChecker_Env.universe_of);
                    FStar_TypeChecker_Env.check_type_of =
                      (uu___361_2130.FStar_TypeChecker_Env.check_type_of);
                    FStar_TypeChecker_Env.use_bv_sorts =
                      (uu___361_2130.FStar_TypeChecker_Env.use_bv_sorts);
                    FStar_TypeChecker_Env.qtbl_name_and_index =
                      (uu___361_2130.FStar_TypeChecker_Env.qtbl_name_and_index);
                    FStar_TypeChecker_Env.normalized_eff_names =
                      (uu___361_2130.FStar_TypeChecker_Env.normalized_eff_names);
                    FStar_TypeChecker_Env.proof_ns =
                      (uu___361_2130.FStar_TypeChecker_Env.proof_ns);
                    FStar_TypeChecker_Env.synth_hook =
                      (uu___361_2130.FStar_TypeChecker_Env.synth_hook);
                    FStar_TypeChecker_Env.splice =
                      (uu___361_2130.FStar_TypeChecker_Env.splice);
                    FStar_TypeChecker_Env.is_native_tactic =
                      (uu___361_2130.FStar_TypeChecker_Env.is_native_tactic);
                    FStar_TypeChecker_Env.identifier_info =
                      (uu___361_2130.FStar_TypeChecker_Env.identifier_info);
                    FStar_TypeChecker_Env.tc_hooks =
                      (uu___361_2130.FStar_TypeChecker_Env.tc_hooks);
                    FStar_TypeChecker_Env.dsenv =
                      (uu___361_2130.FStar_TypeChecker_Env.dsenv);
                    FStar_TypeChecker_Env.dep_graph =
                      (uu___361_2130.FStar_TypeChecker_Env.dep_graph)
                  }  in
                try
                  let uu____2150 =
                    (ps.FStar_Tactics_Types.main_context).FStar_TypeChecker_Env.type_of
                      e1 t
                     in
                  ret uu____2150
                with
                | FStar_Errors.Err (uu____2177,msg) ->
                    let uu____2179 = tts e1 t  in
                    let uu____2180 =
                      let uu____2181 = FStar_TypeChecker_Env.all_binders e1
                         in
                      FStar_All.pipe_right uu____2181
                        (FStar_Syntax_Print.binders_to_string ", ")
                       in
                    fail3 "Cannot type %s in context (%s). Error = (%s)"
                      uu____2179 uu____2180 msg
                | FStar_Errors.Error (uu____2188,msg,uu____2190) ->
                    let uu____2191 = tts e1 t  in
                    let uu____2192 =
                      let uu____2193 = FStar_TypeChecker_Env.all_binders e1
                         in
                      FStar_All.pipe_right uu____2193
                        (FStar_Syntax_Print.binders_to_string ", ")
                       in
                    fail3 "Cannot type %s in context (%s). Error = (%s)"
                      uu____2191 uu____2192 msg))
  
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
  fun uu____2220  ->
    bind get (fun ps  -> ret ps.FStar_Tactics_Types.guard_policy)
  
let (set_guard_policy : FStar_Tactics_Types.guard_policy -> unit tac) =
  fun pol  ->
    bind get
      (fun ps  ->
         set
           (let uu___364_2238 = ps  in
            {
              FStar_Tactics_Types.main_context =
                (uu___364_2238.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___364_2238.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___364_2238.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___364_2238.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (uu___364_2238.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___364_2238.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___364_2238.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___364_2238.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___364_2238.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy = pol;
              FStar_Tactics_Types.freshness =
                (uu___364_2238.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___364_2238.FStar_Tactics_Types.tac_verb_dbg)
            }))
  
let with_policy : 'a . FStar_Tactics_Types.guard_policy -> 'a tac -> 'a tac =
  fun pol  ->
    fun t  ->
      let uu____2262 = get_guard_policy ()  in
      bind uu____2262
        (fun old_pol  ->
           let uu____2268 = set_guard_policy pol  in
           bind uu____2268
             (fun uu____2272  ->
                bind t
                  (fun r  ->
                     let uu____2276 = set_guard_policy old_pol  in
                     bind uu____2276 (fun uu____2280  -> ret r))))
  
let (getopts : FStar_Options.optionstate tac) =
  let uu____2283 = let uu____2288 = cur_goal ()  in trytac uu____2288  in
  bind uu____2283
    (fun uu___337_2295  ->
       match uu___337_2295 with
       | FStar_Pervasives_Native.Some g -> ret g.FStar_Tactics_Types.opts
       | FStar_Pervasives_Native.None  ->
           let uu____2301 = FStar_Options.peek ()  in ret uu____2301)
  
let (proc_guard :
  Prims.string -> env -> FStar_TypeChecker_Env.guard_t -> unit tac) =
  fun reason  ->
    fun e  ->
      fun g  ->
        bind getopts
          (fun opts  ->
             let uu____2324 =
               let uu____2325 = FStar_TypeChecker_Rel.simplify_guard e g  in
               uu____2325.FStar_TypeChecker_Env.guard_f  in
             match uu____2324 with
             | FStar_TypeChecker_Common.Trivial  -> ret ()
             | FStar_TypeChecker_Common.NonTrivial f ->
                 let uu____2329 = istrivial e f  in
                 if uu____2329
                 then ret ()
                 else
                   bind get
                     (fun ps  ->
                        match ps.FStar_Tactics_Types.guard_policy with
                        | FStar_Tactics_Types.Drop  -> ret ()
                        | FStar_Tactics_Types.Goal  ->
                            let uu____2337 =
                              mk_irrelevant_goal reason e f opts  in
                            bind uu____2337
                              (fun goal  ->
                                 let goal1 =
                                   let uu___365_2344 = goal  in
                                   {
                                     FStar_Tactics_Types.goal_main_env =
                                       (uu___365_2344.FStar_Tactics_Types.goal_main_env);
                                     FStar_Tactics_Types.goal_ctx_uvar =
                                       (uu___365_2344.FStar_Tactics_Types.goal_ctx_uvar);
                                     FStar_Tactics_Types.opts =
                                       (uu___365_2344.FStar_Tactics_Types.opts);
                                     FStar_Tactics_Types.is_guard = true
                                   }  in
                                 push_goals [goal1])
                        | FStar_Tactics_Types.SMT  ->
                            let uu____2345 =
                              mk_irrelevant_goal reason e f opts  in
                            bind uu____2345
                              (fun goal  ->
                                 let goal1 =
                                   let uu___366_2352 = goal  in
                                   {
                                     FStar_Tactics_Types.goal_main_env =
                                       (uu___366_2352.FStar_Tactics_Types.goal_main_env);
                                     FStar_Tactics_Types.goal_ctx_uvar =
                                       (uu___366_2352.FStar_Tactics_Types.goal_ctx_uvar);
                                     FStar_Tactics_Types.opts =
                                       (uu___366_2352.FStar_Tactics_Types.opts);
                                     FStar_Tactics_Types.is_guard = true
                                   }  in
                                 push_smt_goals [goal1])
                        | FStar_Tactics_Types.Force  ->
                            (try
                               let uu____2360 =
                                 let uu____2361 =
                                   let uu____2362 =
                                     FStar_TypeChecker_Rel.discharge_guard_no_smt
                                       e g
                                      in
                                   FStar_All.pipe_left
                                     FStar_TypeChecker_Env.is_trivial
                                     uu____2362
                                    in
                                 Prims.op_Negation uu____2361  in
                               if uu____2360
                               then
                                 mlog
                                   (fun uu____2367  ->
                                      let uu____2368 =
                                        FStar_TypeChecker_Rel.guard_to_string
                                          e g
                                         in
                                      FStar_Util.print1 "guard = %s\n"
                                        uu____2368)
                                   (fun uu____2370  ->
                                      fail1 "Forcing the guard failed %s)"
                                        reason)
                               else ret ()
                             with
                             | uu____2377 ->
                                 mlog
                                   (fun uu____2380  ->
                                      let uu____2381 =
                                        FStar_TypeChecker_Rel.guard_to_string
                                          e g
                                         in
                                      FStar_Util.print1 "guard = %s\n"
                                        uu____2381)
                                   (fun uu____2383  ->
                                      fail1 "Forcing the guard failed (%s)"
                                        reason))))
  
let (tc : FStar_Syntax_Syntax.term -> FStar_Reflection_Data.typ tac) =
  fun t  ->
    let uu____2393 =
      let uu____2396 = cur_goal ()  in
      bind uu____2396
        (fun goal  ->
           let uu____2402 =
             let uu____2411 = FStar_Tactics_Types.goal_env goal  in
             __tc uu____2411 t  in
           bind uu____2402
             (fun uu____2423  ->
                match uu____2423 with
                | (t1,typ,guard) ->
                    let uu____2435 =
                      let uu____2438 = FStar_Tactics_Types.goal_env goal  in
                      proc_guard "tc" uu____2438 guard  in
                    bind uu____2435 (fun uu____2440  -> ret typ)))
       in
    FStar_All.pipe_left (wrap_err "tc") uu____2393
  
let (add_irrelevant_goal :
  Prims.string ->
    env -> FStar_Reflection_Data.typ -> FStar_Options.optionstate -> unit tac)
  =
  fun reason  ->
    fun env  ->
      fun phi  ->
        fun opts  ->
          let uu____2469 = mk_irrelevant_goal reason env phi opts  in
          bind uu____2469 (fun goal  -> add_goals [goal])
  
let (trivial : unit -> unit tac) =
  fun uu____2480  ->
    let uu____2483 = cur_goal ()  in
    bind uu____2483
      (fun goal  ->
         let uu____2489 =
           let uu____2490 = FStar_Tactics_Types.goal_env goal  in
           let uu____2491 = FStar_Tactics_Types.goal_type goal  in
           istrivial uu____2490 uu____2491  in
         if uu____2489
         then solve' goal FStar_Syntax_Util.exp_unit
         else
           (let uu____2495 =
              let uu____2496 = FStar_Tactics_Types.goal_env goal  in
              let uu____2497 = FStar_Tactics_Types.goal_type goal  in
              tts uu____2496 uu____2497  in
            fail1 "Not a trivial goal: %s" uu____2495))
  
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
          let uu____2526 =
            let uu____2527 = FStar_TypeChecker_Rel.simplify_guard e g  in
            uu____2527.FStar_TypeChecker_Env.guard_f  in
          match uu____2526 with
          | FStar_TypeChecker_Common.Trivial  ->
              ret FStar_Pervasives_Native.None
          | FStar_TypeChecker_Common.NonTrivial f ->
              let uu____2535 = istrivial e f  in
              if uu____2535
              then ret FStar_Pervasives_Native.None
              else
                (let uu____2543 = mk_irrelevant_goal reason e f opts  in
                 bind uu____2543
                   (fun goal  ->
                      ret
                        (FStar_Pervasives_Native.Some
                           (let uu___369_2553 = goal  in
                            {
                              FStar_Tactics_Types.goal_main_env =
                                (uu___369_2553.FStar_Tactics_Types.goal_main_env);
                              FStar_Tactics_Types.goal_ctx_uvar =
                                (uu___369_2553.FStar_Tactics_Types.goal_ctx_uvar);
                              FStar_Tactics_Types.opts =
                                (uu___369_2553.FStar_Tactics_Types.opts);
                              FStar_Tactics_Types.is_guard = true
                            }))))
  
let (smt : unit -> unit tac) =
  fun uu____2560  ->
    let uu____2563 = cur_goal ()  in
    bind uu____2563
      (fun g  ->
         let uu____2569 = is_irrelevant g  in
         if uu____2569
         then bind __dismiss (fun uu____2573  -> add_smt_goals [g])
         else
           (let uu____2575 =
              let uu____2576 = FStar_Tactics_Types.goal_env g  in
              let uu____2577 = FStar_Tactics_Types.goal_type g  in
              tts uu____2576 uu____2577  in
            fail1 "goal is not irrelevant: cannot dispatch to smt (%s)"
              uu____2575))
  
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
             let uu____2626 =
               try
                 let uu____2660 =
                   let uu____2669 = FStar_BigInt.to_int_fs n1  in
                   FStar_List.splitAt uu____2669 p.FStar_Tactics_Types.goals
                    in
                 ret uu____2660
               with | uu____2691 -> fail "divide: not enough goals"  in
             bind uu____2626
               (fun uu____2717  ->
                  match uu____2717 with
                  | (lgs,rgs) ->
                      let lp =
                        let uu___370_2743 = p  in
                        {
                          FStar_Tactics_Types.main_context =
                            (uu___370_2743.FStar_Tactics_Types.main_context);
                          FStar_Tactics_Types.main_goal =
                            (uu___370_2743.FStar_Tactics_Types.main_goal);
                          FStar_Tactics_Types.all_implicits =
                            (uu___370_2743.FStar_Tactics_Types.all_implicits);
                          FStar_Tactics_Types.goals = lgs;
                          FStar_Tactics_Types.smt_goals = [];
                          FStar_Tactics_Types.depth =
                            (uu___370_2743.FStar_Tactics_Types.depth);
                          FStar_Tactics_Types.__dump =
                            (uu___370_2743.FStar_Tactics_Types.__dump);
                          FStar_Tactics_Types.psc =
                            (uu___370_2743.FStar_Tactics_Types.psc);
                          FStar_Tactics_Types.entry_range =
                            (uu___370_2743.FStar_Tactics_Types.entry_range);
                          FStar_Tactics_Types.guard_policy =
                            (uu___370_2743.FStar_Tactics_Types.guard_policy);
                          FStar_Tactics_Types.freshness =
                            (uu___370_2743.FStar_Tactics_Types.freshness);
                          FStar_Tactics_Types.tac_verb_dbg =
                            (uu___370_2743.FStar_Tactics_Types.tac_verb_dbg)
                        }  in
                      let uu____2744 = set lp  in
                      bind uu____2744
                        (fun uu____2752  ->
                           bind l
                             (fun a  ->
                                bind get
                                  (fun lp'  ->
                                     let rp =
                                       let uu___371_2768 = lp'  in
                                       {
                                         FStar_Tactics_Types.main_context =
                                           (uu___371_2768.FStar_Tactics_Types.main_context);
                                         FStar_Tactics_Types.main_goal =
                                           (uu___371_2768.FStar_Tactics_Types.main_goal);
                                         FStar_Tactics_Types.all_implicits =
                                           (uu___371_2768.FStar_Tactics_Types.all_implicits);
                                         FStar_Tactics_Types.goals = rgs;
                                         FStar_Tactics_Types.smt_goals = [];
                                         FStar_Tactics_Types.depth =
                                           (uu___371_2768.FStar_Tactics_Types.depth);
                                         FStar_Tactics_Types.__dump =
                                           (uu___371_2768.FStar_Tactics_Types.__dump);
                                         FStar_Tactics_Types.psc =
                                           (uu___371_2768.FStar_Tactics_Types.psc);
                                         FStar_Tactics_Types.entry_range =
                                           (uu___371_2768.FStar_Tactics_Types.entry_range);
                                         FStar_Tactics_Types.guard_policy =
                                           (uu___371_2768.FStar_Tactics_Types.guard_policy);
                                         FStar_Tactics_Types.freshness =
                                           (uu___371_2768.FStar_Tactics_Types.freshness);
                                         FStar_Tactics_Types.tac_verb_dbg =
                                           (uu___371_2768.FStar_Tactics_Types.tac_verb_dbg)
                                       }  in
                                     let uu____2769 = set rp  in
                                     bind uu____2769
                                       (fun uu____2777  ->
                                          bind r
                                            (fun b  ->
                                               bind get
                                                 (fun rp'  ->
                                                    let p' =
                                                      let uu___372_2793 = rp'
                                                         in
                                                      {
                                                        FStar_Tactics_Types.main_context
                                                          =
                                                          (uu___372_2793.FStar_Tactics_Types.main_context);
                                                        FStar_Tactics_Types.main_goal
                                                          =
                                                          (uu___372_2793.FStar_Tactics_Types.main_goal);
                                                        FStar_Tactics_Types.all_implicits
                                                          =
                                                          (uu___372_2793.FStar_Tactics_Types.all_implicits);
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
                                                          (uu___372_2793.FStar_Tactics_Types.depth);
                                                        FStar_Tactics_Types.__dump
                                                          =
                                                          (uu___372_2793.FStar_Tactics_Types.__dump);
                                                        FStar_Tactics_Types.psc
                                                          =
                                                          (uu___372_2793.FStar_Tactics_Types.psc);
                                                        FStar_Tactics_Types.entry_range
                                                          =
                                                          (uu___372_2793.FStar_Tactics_Types.entry_range);
                                                        FStar_Tactics_Types.guard_policy
                                                          =
                                                          (uu___372_2793.FStar_Tactics_Types.guard_policy);
                                                        FStar_Tactics_Types.freshness
                                                          =
                                                          (uu___372_2793.FStar_Tactics_Types.freshness);
                                                        FStar_Tactics_Types.tac_verb_dbg
                                                          =
                                                          (uu___372_2793.FStar_Tactics_Types.tac_verb_dbg)
                                                      }  in
                                                    let uu____2794 = set p'
                                                       in
                                                    bind uu____2794
                                                      (fun uu____2802  ->
                                                         bind
                                                           remove_solved_goals
                                                           (fun uu____2808 
                                                              -> ret (a, b)))))))))))
  
let focus : 'a . 'a tac -> 'a tac =
  fun f  ->
    let uu____2829 = divide FStar_BigInt.one f idtac  in
    bind uu____2829
      (fun uu____2842  -> match uu____2842 with | (a,()) -> ret a)
  
let rec map : 'a . 'a tac -> 'a Prims.list tac =
  fun tau  ->
    bind get
      (fun p  ->
         match p.FStar_Tactics_Types.goals with
         | [] -> ret []
         | uu____2879::uu____2880 ->
             let uu____2883 =
               let uu____2892 = map tau  in
               divide FStar_BigInt.one tau uu____2892  in
             bind uu____2883
               (fun uu____2910  ->
                  match uu____2910 with | (h,t) -> ret (h :: t)))
  
let (seq : unit tac -> unit tac -> unit tac) =
  fun t1  ->
    fun t2  ->
      let uu____2951 =
        bind t1
          (fun uu____2956  ->
             let uu____2957 = map t2  in
             bind uu____2957 (fun uu____2965  -> ret ()))
         in
      focus uu____2951
  
let (intro : unit -> FStar_Syntax_Syntax.binder tac) =
  fun uu____2974  ->
    let uu____2977 =
      let uu____2980 = cur_goal ()  in
      bind uu____2980
        (fun goal  ->
           let uu____2989 =
             let uu____2996 = FStar_Tactics_Types.goal_type goal  in
             FStar_Syntax_Util.arrow_one uu____2996  in
           match uu____2989 with
           | FStar_Pervasives_Native.Some (b,c) ->
               let uu____3005 =
                 let uu____3006 = FStar_Syntax_Util.is_total_comp c  in
                 Prims.op_Negation uu____3006  in
               if uu____3005
               then fail "Codomain is effectful"
               else
                 (let env' =
                    let uu____3011 = FStar_Tactics_Types.goal_env goal  in
                    FStar_TypeChecker_Env.push_binders uu____3011 [b]  in
                  let typ' = comp_to_typ c  in
                  let uu____3021 = new_uvar "intro" env' typ'  in
                  bind uu____3021
                    (fun uu____3037  ->
                       match uu____3037 with
                       | (body,ctx_uvar) ->
                           let sol =
                             FStar_Syntax_Util.abs [b] body
                               FStar_Pervasives_Native.None
                              in
                           let uu____3057 = set_solution goal sol  in
                           bind uu____3057
                             (fun uu____3063  ->
                                let g =
                                  FStar_Tactics_Types.mk_goal env' ctx_uvar
                                    goal.FStar_Tactics_Types.opts
                                    goal.FStar_Tactics_Types.is_guard
                                   in
                                let uu____3065 =
                                  let uu____3068 = bnorm_goal g  in
                                  replace_cur uu____3068  in
                                bind uu____3065 (fun uu____3070  -> ret b))))
           | FStar_Pervasives_Native.None  ->
               let uu____3075 =
                 let uu____3076 = FStar_Tactics_Types.goal_env goal  in
                 let uu____3077 = FStar_Tactics_Types.goal_type goal  in
                 tts uu____3076 uu____3077  in
               fail1 "goal is not an arrow (%s)" uu____3075)
       in
    FStar_All.pipe_left (wrap_err "intro") uu____2977
  
let (intro_rec :
  unit ->
    (FStar_Syntax_Syntax.binder,FStar_Syntax_Syntax.binder)
      FStar_Pervasives_Native.tuple2 tac)
  =
  fun uu____3092  ->
    let uu____3099 = cur_goal ()  in
    bind uu____3099
      (fun goal  ->
         FStar_Util.print_string
           "WARNING (intro_rec): calling this is known to cause normalizer loops\n";
         FStar_Util.print_string
           "WARNING (intro_rec): proceed at your own risk...\n";
         (let uu____3116 =
            let uu____3123 = FStar_Tactics_Types.goal_type goal  in
            FStar_Syntax_Util.arrow_one uu____3123  in
          match uu____3116 with
          | FStar_Pervasives_Native.Some (b,c) ->
              let uu____3136 =
                let uu____3137 = FStar_Syntax_Util.is_total_comp c  in
                Prims.op_Negation uu____3137  in
              if uu____3136
              then fail "Codomain is effectful"
              else
                (let bv =
                   let uu____3150 = FStar_Tactics_Types.goal_type goal  in
                   FStar_Syntax_Syntax.gen_bv "__recf"
                     FStar_Pervasives_Native.None uu____3150
                    in
                 let bs =
                   let uu____3158 = FStar_Syntax_Syntax.mk_binder bv  in
                   [uu____3158; b]  in
                 let env' =
                   let uu____3176 = FStar_Tactics_Types.goal_env goal  in
                   FStar_TypeChecker_Env.push_binders uu____3176 bs  in
                 let uu____3177 =
                   let uu____3184 = comp_to_typ c  in
                   new_uvar "intro_rec" env' uu____3184  in
                 bind uu____3177
                   (fun uu____3203  ->
                      match uu____3203 with
                      | (u,ctx_uvar_u) ->
                          let lb =
                            let uu____3217 =
                              FStar_Tactics_Types.goal_type goal  in
                            let uu____3220 =
                              FStar_Syntax_Util.abs [b] u
                                FStar_Pervasives_Native.None
                               in
                            FStar_Syntax_Util.mk_letbinding
                              (FStar_Util.Inl bv) [] uu____3217
                              FStar_Parser_Const.effect_Tot_lid uu____3220 []
                              FStar_Range.dummyRange
                             in
                          let body = FStar_Syntax_Syntax.bv_to_name bv  in
                          let uu____3234 =
                            FStar_Syntax_Subst.close_let_rec [lb] body  in
                          (match uu____3234 with
                           | (lbs,body1) ->
                               let tm =
                                 let uu____3256 =
                                   let uu____3257 =
                                     FStar_Tactics_Types.goal_witness goal
                                      in
                                   uu____3257.FStar_Syntax_Syntax.pos  in
                                 FStar_Syntax_Syntax.mk
                                   (FStar_Syntax_Syntax.Tm_let
                                      ((true, lbs), body1))
                                   FStar_Pervasives_Native.None uu____3256
                                  in
                               let uu____3270 = set_solution goal tm  in
                               bind uu____3270
                                 (fun uu____3279  ->
                                    let uu____3280 =
                                      let uu____3283 =
                                        bnorm_goal
                                          (let uu___375_3286 = goal  in
                                           {
                                             FStar_Tactics_Types.goal_main_env
                                               =
                                               (uu___375_3286.FStar_Tactics_Types.goal_main_env);
                                             FStar_Tactics_Types.goal_ctx_uvar
                                               = ctx_uvar_u;
                                             FStar_Tactics_Types.opts =
                                               (uu___375_3286.FStar_Tactics_Types.opts);
                                             FStar_Tactics_Types.is_guard =
                                               (uu___375_3286.FStar_Tactics_Types.is_guard)
                                           })
                                         in
                                      replace_cur uu____3283  in
                                    bind uu____3280
                                      (fun uu____3293  ->
                                         let uu____3294 =
                                           let uu____3299 =
                                             FStar_Syntax_Syntax.mk_binder bv
                                              in
                                           (uu____3299, b)  in
                                         ret uu____3294)))))
          | FStar_Pervasives_Native.None  ->
              let uu____3308 =
                let uu____3309 = FStar_Tactics_Types.goal_env goal  in
                let uu____3310 = FStar_Tactics_Types.goal_type goal  in
                tts uu____3309 uu____3310  in
              fail1 "intro_rec: goal is not an arrow (%s)" uu____3308))
  
let (norm : FStar_Syntax_Embeddings.norm_step Prims.list -> unit tac) =
  fun s  ->
    let uu____3328 = cur_goal ()  in
    bind uu____3328
      (fun goal  ->
         mlog
           (fun uu____3335  ->
              let uu____3336 =
                let uu____3337 = FStar_Tactics_Types.goal_witness goal  in
                FStar_Syntax_Print.term_to_string uu____3337  in
              FStar_Util.print1 "norm: witness = %s\n" uu____3336)
           (fun uu____3342  ->
              let steps =
                let uu____3346 = FStar_TypeChecker_Normalize.tr_norm_steps s
                   in
                FStar_List.append
                  [FStar_TypeChecker_Normalize.Reify;
                  FStar_TypeChecker_Normalize.UnfoldTac] uu____3346
                 in
              let t =
                let uu____3350 = FStar_Tactics_Types.goal_env goal  in
                let uu____3351 = FStar_Tactics_Types.goal_type goal  in
                normalize steps uu____3350 uu____3351  in
              let uu____3352 = FStar_Tactics_Types.goal_with_type goal t  in
              replace_cur uu____3352))
  
let (norm_term_env :
  env ->
    FStar_Syntax_Embeddings.norm_step Prims.list ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term tac)
  =
  fun e  ->
    fun s  ->
      fun t  ->
        let uu____3376 =
          mlog
            (fun uu____3381  ->
               let uu____3382 = FStar_Syntax_Print.term_to_string t  in
               FStar_Util.print1 "norm_term: tm = %s\n" uu____3382)
            (fun uu____3384  ->
               bind get
                 (fun ps  ->
                    let opts =
                      match ps.FStar_Tactics_Types.goals with
                      | g::uu____3390 -> g.FStar_Tactics_Types.opts
                      | uu____3393 -> FStar_Options.peek ()  in
                    mlog
                      (fun uu____3398  ->
                         let uu____3399 = FStar_Syntax_Print.term_to_string t
                            in
                         FStar_Util.print1 "norm_term_env: t = %s\n"
                           uu____3399)
                      (fun uu____3402  ->
                         let uu____3403 = __tc e t  in
                         bind uu____3403
                           (fun uu____3424  ->
                              match uu____3424 with
                              | (t1,uu____3434,uu____3435) ->
                                  let steps =
                                    let uu____3439 =
                                      FStar_TypeChecker_Normalize.tr_norm_steps
                                        s
                                       in
                                    FStar_List.append
                                      [FStar_TypeChecker_Normalize.Reify;
                                      FStar_TypeChecker_Normalize.UnfoldTac]
                                      uu____3439
                                     in
                                  let t2 =
                                    normalize steps
                                      ps.FStar_Tactics_Types.main_context t1
                                     in
                                  ret t2))))
           in
        FStar_All.pipe_left (wrap_err "norm_term") uu____3376
  
let (refine_intro : unit -> unit tac) =
  fun uu____3453  ->
    let uu____3456 =
      let uu____3459 = cur_goal ()  in
      bind uu____3459
        (fun g  ->
           let uu____3466 =
             let uu____3477 = FStar_Tactics_Types.goal_env g  in
             let uu____3478 = FStar_Tactics_Types.goal_type g  in
             FStar_TypeChecker_Rel.base_and_refinement uu____3477 uu____3478
              in
           match uu____3466 with
           | (uu____3481,FStar_Pervasives_Native.None ) ->
               fail "not a refinement"
           | (t,FStar_Pervasives_Native.Some (bv,phi)) ->
               let g1 = FStar_Tactics_Types.goal_with_type g t  in
               let uu____3506 =
                 let uu____3511 =
                   let uu____3516 =
                     let uu____3517 = FStar_Syntax_Syntax.mk_binder bv  in
                     [uu____3517]  in
                   FStar_Syntax_Subst.open_term uu____3516 phi  in
                 match uu____3511 with
                 | (bvs,phi1) ->
                     let uu____3536 =
                       let uu____3537 = FStar_List.hd bvs  in
                       FStar_Pervasives_Native.fst uu____3537  in
                     (uu____3536, phi1)
                  in
               (match uu____3506 with
                | (bv1,phi1) ->
                    let uu____3550 =
                      let uu____3553 = FStar_Tactics_Types.goal_env g  in
                      let uu____3554 =
                        let uu____3555 =
                          let uu____3558 =
                            let uu____3559 =
                              let uu____3566 =
                                FStar_Tactics_Types.goal_witness g  in
                              (bv1, uu____3566)  in
                            FStar_Syntax_Syntax.NT uu____3559  in
                          [uu____3558]  in
                        FStar_Syntax_Subst.subst uu____3555 phi1  in
                      mk_irrelevant_goal "refine_intro refinement" uu____3553
                        uu____3554 g.FStar_Tactics_Types.opts
                       in
                    bind uu____3550
                      (fun g2  ->
                         bind __dismiss
                           (fun uu____3574  -> add_goals [g1; g2]))))
       in
    FStar_All.pipe_left (wrap_err "refine_intro") uu____3456
  
let (__exact_now : Prims.bool -> FStar_Syntax_Syntax.term -> unit tac) =
  fun set_expected_typ1  ->
    fun t  ->
      let uu____3593 = cur_goal ()  in
      bind uu____3593
        (fun goal  ->
           let env =
             if set_expected_typ1
             then
               let uu____3601 = FStar_Tactics_Types.goal_env goal  in
               let uu____3602 = FStar_Tactics_Types.goal_type goal  in
               FStar_TypeChecker_Env.set_expected_typ uu____3601 uu____3602
             else FStar_Tactics_Types.goal_env goal  in
           let uu____3604 = __tc env t  in
           bind uu____3604
             (fun uu____3623  ->
                match uu____3623 with
                | (t1,typ,guard) ->
                    mlog
                      (fun uu____3638  ->
                         let uu____3639 =
                           FStar_Syntax_Print.term_to_string typ  in
                         let uu____3640 =
                           let uu____3641 = FStar_Tactics_Types.goal_env goal
                              in
                           FStar_TypeChecker_Rel.guard_to_string uu____3641
                             guard
                            in
                         FStar_Util.print2
                           "__exact_now: got type %s\n__exact_now: and guard %s\n"
                           uu____3639 uu____3640)
                      (fun uu____3644  ->
                         let uu____3645 =
                           let uu____3648 = FStar_Tactics_Types.goal_env goal
                              in
                           proc_guard "__exact typing" uu____3648 guard  in
                         bind uu____3645
                           (fun uu____3650  ->
                              mlog
                                (fun uu____3654  ->
                                   let uu____3655 =
                                     FStar_Syntax_Print.term_to_string typ
                                      in
                                   let uu____3656 =
                                     let uu____3657 =
                                       FStar_Tactics_Types.goal_type goal  in
                                     FStar_Syntax_Print.term_to_string
                                       uu____3657
                                      in
                                   FStar_Util.print2
                                     "__exact_now: unifying %s and %s\n"
                                     uu____3655 uu____3656)
                                (fun uu____3660  ->
                                   let uu____3661 =
                                     let uu____3664 =
                                       FStar_Tactics_Types.goal_env goal  in
                                     let uu____3665 =
                                       FStar_Tactics_Types.goal_type goal  in
                                     do_unify uu____3664 typ uu____3665  in
                                   bind uu____3661
                                     (fun b  ->
                                        if b
                                        then solve goal t1
                                        else
                                          (let uu____3671 =
                                             let uu____3672 =
                                               FStar_Tactics_Types.goal_env
                                                 goal
                                                in
                                             tts uu____3672 t1  in
                                           let uu____3673 =
                                             let uu____3674 =
                                               FStar_Tactics_Types.goal_env
                                                 goal
                                                in
                                             tts uu____3674 typ  in
                                           let uu____3675 =
                                             let uu____3676 =
                                               FStar_Tactics_Types.goal_env
                                                 goal
                                                in
                                             let uu____3677 =
                                               FStar_Tactics_Types.goal_type
                                                 goal
                                                in
                                             tts uu____3676 uu____3677  in
                                           let uu____3678 =
                                             let uu____3679 =
                                               FStar_Tactics_Types.goal_env
                                                 goal
                                                in
                                             let uu____3680 =
                                               FStar_Tactics_Types.goal_witness
                                                 goal
                                                in
                                             tts uu____3679 uu____3680  in
                                           fail4
                                             "%s : %s does not exactly solve the goal %s (witness = %s)"
                                             uu____3671 uu____3673 uu____3675
                                             uu____3678)))))))
  
let (t_exact : Prims.bool -> FStar_Syntax_Syntax.term -> unit tac) =
  fun set_expected_typ1  ->
    fun tm  ->
      let uu____3695 =
        mlog
          (fun uu____3700  ->
             let uu____3701 = FStar_Syntax_Print.term_to_string tm  in
             FStar_Util.print1 "t_exact: tm = %s\n" uu____3701)
          (fun uu____3704  ->
             let uu____3705 =
               let uu____3712 = __exact_now set_expected_typ1 tm  in
               trytac' uu____3712  in
             bind uu____3705
               (fun uu___339_3721  ->
                  match uu___339_3721 with
                  | FStar_Util.Inr r -> ret ()
                  | FStar_Util.Inl e ->
                      mlog
                        (fun uu____3731  ->
                           FStar_Util.print_string
                             "__exact_now failed, trying refine...\n")
                        (fun uu____3734  ->
                           let uu____3735 =
                             let uu____3742 =
                               let uu____3745 =
                                 norm [FStar_Syntax_Embeddings.Delta]  in
                               bind uu____3745
                                 (fun uu____3750  ->
                                    let uu____3751 = refine_intro ()  in
                                    bind uu____3751
                                      (fun uu____3755  ->
                                         __exact_now set_expected_typ1 tm))
                                in
                             trytac' uu____3742  in
                           bind uu____3735
                             (fun uu___338_3762  ->
                                match uu___338_3762 with
                                | FStar_Util.Inr r -> ret ()
                                | FStar_Util.Inl uu____3770 -> fail e))))
         in
      FStar_All.pipe_left (wrap_err "exact") uu____3695
  
let rec mapM : 'a 'b . ('a -> 'b tac) -> 'a Prims.list -> 'b Prims.list tac =
  fun f  ->
    fun l  ->
      match l with
      | [] -> ret []
      | x::xs ->
          let uu____3820 = f x  in
          bind uu____3820
            (fun y  ->
               let uu____3828 = mapM f xs  in
               bind uu____3828 (fun ys  -> ret (y :: ys)))
  
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
          let uu____3899 = do_unify e ty1 ty2  in
          bind uu____3899
            (fun uu___340_3911  ->
               if uu___340_3911
               then ret acc
               else
                 (let uu____3930 = FStar_Syntax_Util.arrow_one ty1  in
                  match uu____3930 with
                  | FStar_Pervasives_Native.None  ->
                      let uu____3951 = FStar_Syntax_Print.term_to_string ty1
                         in
                      let uu____3952 = FStar_Syntax_Print.term_to_string ty2
                         in
                      fail2 "Could not instantiate, %s to %s" uu____3951
                        uu____3952
                  | FStar_Pervasives_Native.Some (b,c) ->
                      let uu____3967 =
                        let uu____3968 = FStar_Syntax_Util.is_total_comp c
                           in
                        Prims.op_Negation uu____3968  in
                      if uu____3967
                      then fail "Codomain is effectful"
                      else
                        (let uu____3988 =
                           new_uvar "apply arg" e
                             (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                            in
                         bind uu____3988
                           (fun uu____4012  ->
                              match uu____4012 with
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
      let uu____4094 =
        mlog
          (fun uu____4099  ->
             let uu____4100 = FStar_Syntax_Print.term_to_string tm  in
             FStar_Util.print1 "apply: tm = %s\n" uu____4100)
          (fun uu____4103  ->
             let uu____4104 = cur_goal ()  in
             bind uu____4104
               (fun goal  ->
                  let e = FStar_Tactics_Types.goal_env goal  in
                  let uu____4112 = __tc e tm  in
                  bind uu____4112
                    (fun uu____4133  ->
                       match uu____4133 with
                       | (tm1,typ,guard) ->
                           let typ1 = bnorm e typ  in
                           let uu____4146 =
                             let uu____4157 =
                               FStar_Tactics_Types.goal_type goal  in
                             try_match_by_application e typ1 uu____4157  in
                           bind uu____4146
                             (fun uvs  ->
                                let w =
                                  FStar_List.fold_right
                                    (fun uu____4198  ->
                                       fun w  ->
                                         match uu____4198 with
                                         | (uvt,q,uu____4214) ->
                                             FStar_Syntax_Util.mk_app w
                                               [(uvt, q)]) uvs tm1
                                   in
                                let uvset =
                                  let uu____4236 =
                                    FStar_Syntax_Free.new_uv_set ()  in
                                  FStar_List.fold_right
                                    (fun uu____4253  ->
                                       fun s  ->
                                         match uu____4253 with
                                         | (uu____4265,uu____4266,uv) ->
                                             let uu____4268 =
                                               FStar_Syntax_Free.uvars
                                                 uv.FStar_Syntax_Syntax.ctx_uvar_typ
                                                in
                                             FStar_Util.set_union s
                                               uu____4268) uvs uu____4236
                                   in
                                let free_in_some_goal uv =
                                  FStar_Util.set_mem uv uvset  in
                                let uu____4277 = solve' goal w  in
                                bind uu____4277
                                  (fun uu____4282  ->
                                     let uu____4283 =
                                       mapM
                                         (fun uu____4300  ->
                                            match uu____4300 with
                                            | (uvt,q,uv) ->
                                                let uu____4312 =
                                                  FStar_Syntax_Unionfind.find
                                                    uv.FStar_Syntax_Syntax.ctx_uvar_head
                                                   in
                                                (match uu____4312 with
                                                 | FStar_Pervasives_Native.Some
                                                     uu____4317 -> ret ()
                                                 | FStar_Pervasives_Native.None
                                                      ->
                                                     let uu____4318 =
                                                       uopt &&
                                                         (free_in_some_goal
                                                            uv)
                                                        in
                                                     if uu____4318
                                                     then ret ()
                                                     else
                                                       (let uu____4322 =
                                                          let uu____4325 =
                                                            bnorm_goal
                                                              (let uu___376_4328
                                                                 = goal  in
                                                               {
                                                                 FStar_Tactics_Types.goal_main_env
                                                                   =
                                                                   (uu___376_4328.FStar_Tactics_Types.goal_main_env);
                                                                 FStar_Tactics_Types.goal_ctx_uvar
                                                                   = uv;
                                                                 FStar_Tactics_Types.opts
                                                                   =
                                                                   (uu___376_4328.FStar_Tactics_Types.opts);
                                                                 FStar_Tactics_Types.is_guard
                                                                   = false
                                                               })
                                                             in
                                                          [uu____4325]  in
                                                        add_goals uu____4322)))
                                         uvs
                                        in
                                     bind uu____4283
                                       (fun uu____4332  ->
                                          proc_guard "apply guard" e guard))))))
         in
      FStar_All.pipe_left (wrap_err "apply") uu____4094
  
let (lemma_or_sq :
  FStar_Syntax_Syntax.comp ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun c  ->
    let ct = FStar_Syntax_Util.comp_to_comp_typ_nouniv c  in
    let uu____4357 =
      FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
        FStar_Parser_Const.effect_Lemma_lid
       in
    if uu____4357
    then
      let uu____4364 =
        match ct.FStar_Syntax_Syntax.effect_args with
        | pre::post::uu____4379 ->
            ((FStar_Pervasives_Native.fst pre),
              (FStar_Pervasives_Native.fst post))
        | uu____4418 -> failwith "apply_lemma: impossible: not a lemma"  in
      match uu____4364 with
      | (pre,post) ->
          let post1 =
            let uu____4448 =
              let uu____4457 =
                FStar_Syntax_Syntax.as_arg FStar_Syntax_Util.exp_unit  in
              [uu____4457]  in
            FStar_Syntax_Util.mk_app post uu____4448  in
          FStar_Pervasives_Native.Some (pre, post1)
    else
      (let uu____4481 =
         FStar_Syntax_Util.is_pure_effect ct.FStar_Syntax_Syntax.effect_name
          in
       if uu____4481
       then
         let uu____4488 =
           FStar_Syntax_Util.un_squash ct.FStar_Syntax_Syntax.result_typ  in
         FStar_Util.map_opt uu____4488
           (fun post  -> (FStar_Syntax_Util.t_true, post))
       else FStar_Pervasives_Native.None)
  
let (apply_lemma : FStar_Syntax_Syntax.term -> unit tac) =
  fun tm  ->
    let uu____4521 =
      let uu____4524 =
        mlog
          (fun uu____4529  ->
             let uu____4530 = FStar_Syntax_Print.term_to_string tm  in
             FStar_Util.print1 "apply_lemma: tm = %s\n" uu____4530)
          (fun uu____4534  ->
             let is_unit_t t =
               let uu____4541 =
                 let uu____4542 = FStar_Syntax_Subst.compress t  in
                 uu____4542.FStar_Syntax_Syntax.n  in
               match uu____4541 with
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.unit_lid
                   -> true
               | uu____4546 -> false  in
             let uu____4547 = cur_goal ()  in
             bind uu____4547
               (fun goal  ->
                  let uu____4553 =
                    let uu____4562 = FStar_Tactics_Types.goal_env goal  in
                    __tc uu____4562 tm  in
                  bind uu____4553
                    (fun uu____4577  ->
                       match uu____4577 with
                       | (tm1,t,guard) ->
                           let uu____4589 =
                             FStar_Syntax_Util.arrow_formals_comp t  in
                           (match uu____4589 with
                            | (bs,comp) ->
                                let uu____4616 = lemma_or_sq comp  in
                                (match uu____4616 with
                                 | FStar_Pervasives_Native.None  ->
                                     fail "not a lemma or squashed function"
                                 | FStar_Pervasives_Native.Some (pre,post) ->
                                     let uu____4635 =
                                       FStar_List.fold_left
                                         (fun uu____4677  ->
                                            fun uu____4678  ->
                                              match (uu____4677, uu____4678)
                                              with
                                              | ((uvs,guard1,subst1),(b,aq))
                                                  ->
                                                  let b_t =
                                                    FStar_Syntax_Subst.subst
                                                      subst1
                                                      b.FStar_Syntax_Syntax.sort
                                                     in
                                                  let uu____4769 =
                                                    is_unit_t b_t  in
                                                  if uu____4769
                                                  then
                                                    (((FStar_Syntax_Util.exp_unit,
                                                        aq) :: uvs), guard1,
                                                      ((FStar_Syntax_Syntax.NT
                                                          (b,
                                                            FStar_Syntax_Util.exp_unit))
                                                      :: subst1))
                                                  else
                                                    (let uu____4799 =
                                                       let uu____4812 =
                                                         let uu____4813 =
                                                           FStar_Tactics_Types.goal_type
                                                             goal
                                                            in
                                                         uu____4813.FStar_Syntax_Syntax.pos
                                                          in
                                                       let uu____4816 =
                                                         FStar_Tactics_Types.goal_env
                                                           goal
                                                          in
                                                       FStar_TypeChecker_Util.new_implicit_var
                                                         "apply_lemma"
                                                         uu____4812
                                                         uu____4816 b_t
                                                        in
                                                     match uu____4799 with
                                                     | (u,uu____4832,g_u) ->
                                                         let uu____4846 =
                                                           FStar_TypeChecker_Env.conj_guard
                                                             guard1 g_u
                                                            in
                                                         (((u, aq) :: uvs),
                                                           uu____4846,
                                                           ((FStar_Syntax_Syntax.NT
                                                               (b, u)) ::
                                                           subst1))))
                                         ([], guard, []) bs
                                        in
                                     (match uu____4635 with
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
                                          let uu____4907 =
                                            let uu____4910 =
                                              FStar_Tactics_Types.goal_env
                                                goal
                                               in
                                            let uu____4911 =
                                              FStar_Syntax_Util.mk_squash
                                                FStar_Syntax_Syntax.U_zero
                                                post1
                                               in
                                            let uu____4912 =
                                              FStar_Tactics_Types.goal_type
                                                goal
                                               in
                                            do_unify uu____4910 uu____4911
                                              uu____4912
                                             in
                                          bind uu____4907
                                            (fun b  ->
                                               if Prims.op_Negation b
                                               then
                                                 let uu____4920 =
                                                   let uu____4921 =
                                                     FStar_Tactics_Types.goal_env
                                                       goal
                                                      in
                                                   tts uu____4921 tm1  in
                                                 let uu____4922 =
                                                   let uu____4923 =
                                                     FStar_Tactics_Types.goal_env
                                                       goal
                                                      in
                                                   let uu____4924 =
                                                     FStar_Syntax_Util.mk_squash
                                                       FStar_Syntax_Syntax.U_zero
                                                       post1
                                                      in
                                                   tts uu____4923 uu____4924
                                                    in
                                                 let uu____4925 =
                                                   let uu____4926 =
                                                     FStar_Tactics_Types.goal_env
                                                       goal
                                                      in
                                                   let uu____4927 =
                                                     FStar_Tactics_Types.goal_type
                                                       goal
                                                      in
                                                   tts uu____4926 uu____4927
                                                    in
                                                 fail3
                                                   "Cannot instantiate lemma %s (with postcondition: %s) to match goal (%s)"
                                                   uu____4920 uu____4922
                                                   uu____4925
                                               else
                                                 (let uu____4929 =
                                                    add_implicits
                                                      implicits.FStar_TypeChecker_Env.implicits
                                                     in
                                                  bind uu____4929
                                                    (fun uu____4934  ->
                                                       let uu____4935 =
                                                         solve' goal
                                                           FStar_Syntax_Util.exp_unit
                                                          in
                                                       bind uu____4935
                                                         (fun uu____4943  ->
                                                            let is_free_uvar
                                                              uv t1 =
                                                              let free_uvars
                                                                =
                                                                let uu____4968
                                                                  =
                                                                  let uu____4971
                                                                    =
                                                                    FStar_Syntax_Free.uvars
                                                                    t1  in
                                                                  FStar_Util.set_elements
                                                                    uu____4971
                                                                   in
                                                                FStar_List.map
                                                                  (fun x  ->
                                                                    x.FStar_Syntax_Syntax.ctx_uvar_head)
                                                                  uu____4968
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
                                                                   let uu____5006
                                                                    =
                                                                    FStar_Tactics_Types.goal_type
                                                                    g'  in
                                                                   is_free_uvar
                                                                    uv
                                                                    uu____5006)
                                                                goals
                                                               in
                                                            let checkone t1
                                                              goals =
                                                              let uu____5022
                                                                =
                                                                FStar_Syntax_Util.head_and_args
                                                                  t1
                                                                 in
                                                              match uu____5022
                                                              with
                                                              | (hd1,uu____5038)
                                                                  ->
                                                                  (match 
                                                                    hd1.FStar_Syntax_Syntax.n
                                                                   with
                                                                   | 
                                                                   FStar_Syntax_Syntax.Tm_uvar
                                                                    (uv,uu____5060)
                                                                    ->
                                                                    appears
                                                                    uv.FStar_Syntax_Syntax.ctx_uvar_head
                                                                    goals
                                                                   | 
                                                                   uu____5077
                                                                    -> false)
                                                               in
                                                            let uu____5078 =
                                                              FStar_All.pipe_right
                                                                implicits.FStar_TypeChecker_Env.implicits
                                                                (mapM
                                                                   (fun
                                                                    uu____5141
                                                                     ->
                                                                    match uu____5141
                                                                    with
                                                                    | 
                                                                    (_msg,term,ctx_uvar,_range)
                                                                    ->
                                                                    let uu____5164
                                                                    =
                                                                    FStar_Syntax_Util.head_and_args
                                                                    term  in
                                                                    (match uu____5164
                                                                    with
                                                                    | 
                                                                    (hd1,uu____5190)
                                                                    ->
                                                                    let uu____5211
                                                                    =
                                                                    let uu____5212
                                                                    =
                                                                    FStar_Syntax_Subst.compress
                                                                    hd1  in
                                                                    uu____5212.FStar_Syntax_Syntax.n
                                                                     in
                                                                    (match uu____5211
                                                                    with
                                                                    | 
                                                                    FStar_Syntax_Syntax.Tm_uvar
                                                                    (ctx_uvar1,uu____5226)
                                                                    ->
                                                                    let goal1
                                                                    =
                                                                    bnorm_goal
                                                                    (let uu___377_5246
                                                                    = goal
                                                                     in
                                                                    {
                                                                    FStar_Tactics_Types.goal_main_env
                                                                    =
                                                                    (uu___377_5246.FStar_Tactics_Types.goal_main_env);
                                                                    FStar_Tactics_Types.goal_ctx_uvar
                                                                    =
                                                                    ctx_uvar1;
                                                                    FStar_Tactics_Types.opts
                                                                    =
                                                                    (uu___377_5246.FStar_Tactics_Types.opts);
                                                                    FStar_Tactics_Types.is_guard
                                                                    =
                                                                    (uu___377_5246.FStar_Tactics_Types.is_guard)
                                                                    })  in
                                                                    ret
                                                                    ([goal1],
                                                                    [])
                                                                    | 
                                                                    uu____5259
                                                                    ->
                                                                    let env =
                                                                    let uu___378_5261
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    goal  in
                                                                    {
                                                                    FStar_TypeChecker_Env.solver
                                                                    =
                                                                    (uu___378_5261.FStar_TypeChecker_Env.solver);
                                                                    FStar_TypeChecker_Env.range
                                                                    =
                                                                    (uu___378_5261.FStar_TypeChecker_Env.range);
                                                                    FStar_TypeChecker_Env.curmodule
                                                                    =
                                                                    (uu___378_5261.FStar_TypeChecker_Env.curmodule);
                                                                    FStar_TypeChecker_Env.gamma
                                                                    =
                                                                    (ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_gamma);
                                                                    FStar_TypeChecker_Env.gamma_sig
                                                                    =
                                                                    (uu___378_5261.FStar_TypeChecker_Env.gamma_sig);
                                                                    FStar_TypeChecker_Env.gamma_cache
                                                                    =
                                                                    (uu___378_5261.FStar_TypeChecker_Env.gamma_cache);
                                                                    FStar_TypeChecker_Env.modules
                                                                    =
                                                                    (uu___378_5261.FStar_TypeChecker_Env.modules);
                                                                    FStar_TypeChecker_Env.expected_typ
                                                                    =
                                                                    (uu___378_5261.FStar_TypeChecker_Env.expected_typ);
                                                                    FStar_TypeChecker_Env.sigtab
                                                                    =
                                                                    (uu___378_5261.FStar_TypeChecker_Env.sigtab);
                                                                    FStar_TypeChecker_Env.is_pattern
                                                                    =
                                                                    (uu___378_5261.FStar_TypeChecker_Env.is_pattern);
                                                                    FStar_TypeChecker_Env.instantiate_imp
                                                                    =
                                                                    (uu___378_5261.FStar_TypeChecker_Env.instantiate_imp);
                                                                    FStar_TypeChecker_Env.effects
                                                                    =
                                                                    (uu___378_5261.FStar_TypeChecker_Env.effects);
                                                                    FStar_TypeChecker_Env.generalize
                                                                    =
                                                                    (uu___378_5261.FStar_TypeChecker_Env.generalize);
                                                                    FStar_TypeChecker_Env.letrecs
                                                                    =
                                                                    (uu___378_5261.FStar_TypeChecker_Env.letrecs);
                                                                    FStar_TypeChecker_Env.top_level
                                                                    =
                                                                    (uu___378_5261.FStar_TypeChecker_Env.top_level);
                                                                    FStar_TypeChecker_Env.check_uvars
                                                                    =
                                                                    (uu___378_5261.FStar_TypeChecker_Env.check_uvars);
                                                                    FStar_TypeChecker_Env.use_eq
                                                                    =
                                                                    (uu___378_5261.FStar_TypeChecker_Env.use_eq);
                                                                    FStar_TypeChecker_Env.is_iface
                                                                    =
                                                                    (uu___378_5261.FStar_TypeChecker_Env.is_iface);
                                                                    FStar_TypeChecker_Env.admit
                                                                    =
                                                                    (uu___378_5261.FStar_TypeChecker_Env.admit);
                                                                    FStar_TypeChecker_Env.lax
                                                                    =
                                                                    (uu___378_5261.FStar_TypeChecker_Env.lax);
                                                                    FStar_TypeChecker_Env.lax_universes
                                                                    =
                                                                    (uu___378_5261.FStar_TypeChecker_Env.lax_universes);
                                                                    FStar_TypeChecker_Env.phase1
                                                                    =
                                                                    (uu___378_5261.FStar_TypeChecker_Env.phase1);
                                                                    FStar_TypeChecker_Env.failhard
                                                                    =
                                                                    (uu___378_5261.FStar_TypeChecker_Env.failhard);
                                                                    FStar_TypeChecker_Env.nosynth
                                                                    =
                                                                    (uu___378_5261.FStar_TypeChecker_Env.nosynth);
                                                                    FStar_TypeChecker_Env.uvar_subtyping
                                                                    =
                                                                    (uu___378_5261.FStar_TypeChecker_Env.uvar_subtyping);
                                                                    FStar_TypeChecker_Env.tc_term
                                                                    =
                                                                    (uu___378_5261.FStar_TypeChecker_Env.tc_term);
                                                                    FStar_TypeChecker_Env.type_of
                                                                    =
                                                                    (uu___378_5261.FStar_TypeChecker_Env.type_of);
                                                                    FStar_TypeChecker_Env.universe_of
                                                                    =
                                                                    (uu___378_5261.FStar_TypeChecker_Env.universe_of);
                                                                    FStar_TypeChecker_Env.check_type_of
                                                                    =
                                                                    (uu___378_5261.FStar_TypeChecker_Env.check_type_of);
                                                                    FStar_TypeChecker_Env.use_bv_sorts
                                                                    =
                                                                    (uu___378_5261.FStar_TypeChecker_Env.use_bv_sorts);
                                                                    FStar_TypeChecker_Env.qtbl_name_and_index
                                                                    =
                                                                    (uu___378_5261.FStar_TypeChecker_Env.qtbl_name_and_index);
                                                                    FStar_TypeChecker_Env.normalized_eff_names
                                                                    =
                                                                    (uu___378_5261.FStar_TypeChecker_Env.normalized_eff_names);
                                                                    FStar_TypeChecker_Env.proof_ns
                                                                    =
                                                                    (uu___378_5261.FStar_TypeChecker_Env.proof_ns);
                                                                    FStar_TypeChecker_Env.synth_hook
                                                                    =
                                                                    (uu___378_5261.FStar_TypeChecker_Env.synth_hook);
                                                                    FStar_TypeChecker_Env.splice
                                                                    =
                                                                    (uu___378_5261.FStar_TypeChecker_Env.splice);
                                                                    FStar_TypeChecker_Env.is_native_tactic
                                                                    =
                                                                    (uu___378_5261.FStar_TypeChecker_Env.is_native_tactic);
                                                                    FStar_TypeChecker_Env.identifier_info
                                                                    =
                                                                    (uu___378_5261.FStar_TypeChecker_Env.identifier_info);
                                                                    FStar_TypeChecker_Env.tc_hooks
                                                                    =
                                                                    (uu___378_5261.FStar_TypeChecker_Env.tc_hooks);
                                                                    FStar_TypeChecker_Env.dsenv
                                                                    =
                                                                    (uu___378_5261.FStar_TypeChecker_Env.dsenv);
                                                                    FStar_TypeChecker_Env.dep_graph
                                                                    =
                                                                    (uu___378_5261.FStar_TypeChecker_Env.dep_graph)
                                                                    }  in
                                                                    let g_typ
                                                                    =
                                                                    let uu____5263
                                                                    =
                                                                    FStar_Options.__temp_fast_implicits
                                                                    ()  in
                                                                    if
                                                                    uu____5263
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
                                                                    let uu____5266
                                                                    =
                                                                    let uu____5273
                                                                    =
                                                                    FStar_TypeChecker_Env.set_expected_typ
                                                                    env
                                                                    ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_typ
                                                                     in
                                                                    env.FStar_TypeChecker_Env.type_of
                                                                    uu____5273
                                                                    term1  in
                                                                    match uu____5266
                                                                    with
                                                                    | 
                                                                    (uu____5274,uu____5275,g_typ)
                                                                    -> g_typ)
                                                                     in
                                                                    let uu____5277
                                                                    =
                                                                    let uu____5282
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    goal  in
                                                                    goal_from_guard
                                                                    "apply_lemma solved arg"
                                                                    uu____5282
                                                                    g_typ
                                                                    goal.FStar_Tactics_Types.opts
                                                                     in
                                                                    bind
                                                                    uu____5277
                                                                    (fun
                                                                    uu___341_5294
                                                                     ->
                                                                    match uu___341_5294
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
                                                            bind uu____5078
                                                              (fun goals_  ->
                                                                 let sub_goals
                                                                   =
                                                                   let uu____5362
                                                                    =
                                                                    FStar_List.map
                                                                    FStar_Pervasives_Native.fst
                                                                    goals_
                                                                     in
                                                                   FStar_List.flatten
                                                                    uu____5362
                                                                    in
                                                                 let smt_goals
                                                                   =
                                                                   let uu____5384
                                                                    =
                                                                    FStar_List.map
                                                                    FStar_Pervasives_Native.snd
                                                                    goals_
                                                                     in
                                                                   FStar_List.flatten
                                                                    uu____5384
                                                                    in
                                                                 let rec filter'
                                                                   f xs =
                                                                   match xs
                                                                   with
                                                                   | 
                                                                   [] -> []
                                                                   | 
                                                                   x::xs1 ->
                                                                    let uu____5445
                                                                    = f x xs1
                                                                     in
                                                                    if
                                                                    uu____5445
                                                                    then
                                                                    let uu____5448
                                                                    =
                                                                    filter' f
                                                                    xs1  in x
                                                                    ::
                                                                    uu____5448
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
                                                                    let uu____5462
                                                                    =
                                                                    let uu____5463
                                                                    =
                                                                    FStar_Tactics_Types.goal_witness
                                                                    g  in
                                                                    checkone
                                                                    uu____5463
                                                                    goals  in
                                                                    Prims.op_Negation
                                                                    uu____5462)
                                                                    sub_goals
                                                                    in
                                                                 let uu____5464
                                                                   =
                                                                   let uu____5467
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    goal  in
                                                                   proc_guard
                                                                    "apply_lemma guard"
                                                                    uu____5467
                                                                    guard
                                                                    in
                                                                 bind
                                                                   uu____5464
                                                                   (fun
                                                                    uu____5470
                                                                     ->
                                                                    let uu____5471
                                                                    =
                                                                    let uu____5474
                                                                    =
                                                                    let uu____5475
                                                                    =
                                                                    let uu____5476
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    goal  in
                                                                    let uu____5477
                                                                    =
                                                                    FStar_Syntax_Util.mk_squash
                                                                    FStar_Syntax_Syntax.U_zero
                                                                    pre1  in
                                                                    istrivial
                                                                    uu____5476
                                                                    uu____5477
                                                                     in
                                                                    Prims.op_Negation
                                                                    uu____5475
                                                                     in
                                                                    if
                                                                    uu____5474
                                                                    then
                                                                    let uu____5480
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    goal  in
                                                                    add_irrelevant_goal
                                                                    "apply_lemma precondition"
                                                                    uu____5480
                                                                    pre1
                                                                    goal.FStar_Tactics_Types.opts
                                                                    else
                                                                    ret ()
                                                                     in
                                                                    bind
                                                                    uu____5471
                                                                    (fun
                                                                    uu____5484
                                                                     ->
                                                                    let uu____5485
                                                                    =
                                                                    add_smt_goals
                                                                    smt_goals
                                                                     in
                                                                    bind
                                                                    uu____5485
                                                                    (fun
                                                                    uu____5489
                                                                     ->
                                                                    add_goals
                                                                    sub_goals1))))))))))))))
         in
      focus uu____4524  in
    FStar_All.pipe_left (wrap_err "apply_lemma") uu____4521
  
let (destruct_eq' :
  FStar_Reflection_Data.typ ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun typ  ->
    let uu____5511 = FStar_Syntax_Util.destruct_typ_as_formula typ  in
    match uu____5511 with
    | FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn
        (l,uu____5521::(e1,uu____5523)::(e2,uu____5525)::[])) when
        FStar_Ident.lid_equals l FStar_Parser_Const.eq2_lid ->
        FStar_Pervasives_Native.Some (e1, e2)
    | uu____5568 -> FStar_Pervasives_Native.None
  
let (destruct_eq :
  FStar_Reflection_Data.typ ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun typ  ->
    let uu____5592 = destruct_eq' typ  in
    match uu____5592 with
    | FStar_Pervasives_Native.Some t -> FStar_Pervasives_Native.Some t
    | FStar_Pervasives_Native.None  ->
        let uu____5622 = FStar_Syntax_Util.un_squash typ  in
        (match uu____5622 with
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
        let uu____5684 = FStar_TypeChecker_Env.pop_bv e1  in
        match uu____5684 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (bv',e') ->
            if FStar_Syntax_Syntax.bv_eq bvar bv'
            then FStar_Pervasives_Native.Some (e', [])
            else
              (let uu____5732 = aux e'  in
               FStar_Util.map_opt uu____5732
                 (fun uu____5756  ->
                    match uu____5756 with | (e'',bvs) -> (e'', (bv' :: bvs))))
         in
      let uu____5777 = aux e  in
      FStar_Util.map_opt uu____5777
        (fun uu____5801  ->
           match uu____5801 with | (e',bvs) -> (e', (FStar_List.rev bvs)))
  
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
          let uu____5868 =
            let uu____5877 = FStar_Tactics_Types.goal_env g  in
            split_env b1 uu____5877  in
          FStar_Util.map_opt uu____5868
            (fun uu____5892  ->
               match uu____5892 with
               | (e0,bvs) ->
                   let s1 bv =
                     let uu___379_5911 = bv  in
                     let uu____5912 =
                       FStar_Syntax_Subst.subst s bv.FStar_Syntax_Syntax.sort
                        in
                     {
                       FStar_Syntax_Syntax.ppname =
                         (uu___379_5911.FStar_Syntax_Syntax.ppname);
                       FStar_Syntax_Syntax.index =
                         (uu___379_5911.FStar_Syntax_Syntax.index);
                       FStar_Syntax_Syntax.sort = uu____5912
                     }  in
                   let bvs1 = FStar_List.map s1 bvs  in
                   let new_env = push_bvs e0 (b2 :: bvs1)  in
                   let new_goal =
                     let uu___380_5920 = g.FStar_Tactics_Types.goal_ctx_uvar
                        in
                     let uu____5921 =
                       FStar_TypeChecker_Env.all_binders new_env  in
                     let uu____5928 =
                       let uu____5931 = FStar_Tactics_Types.goal_type g  in
                       FStar_Syntax_Subst.subst s uu____5931  in
                     {
                       FStar_Syntax_Syntax.ctx_uvar_head =
                         (uu___380_5920.FStar_Syntax_Syntax.ctx_uvar_head);
                       FStar_Syntax_Syntax.ctx_uvar_gamma =
                         (new_env.FStar_TypeChecker_Env.gamma);
                       FStar_Syntax_Syntax.ctx_uvar_binders = uu____5921;
                       FStar_Syntax_Syntax.ctx_uvar_typ = uu____5928;
                       FStar_Syntax_Syntax.ctx_uvar_reason =
                         (uu___380_5920.FStar_Syntax_Syntax.ctx_uvar_reason);
                       FStar_Syntax_Syntax.ctx_uvar_should_check =
                         (uu___380_5920.FStar_Syntax_Syntax.ctx_uvar_should_check);
                       FStar_Syntax_Syntax.ctx_uvar_range =
                         (uu___380_5920.FStar_Syntax_Syntax.ctx_uvar_range)
                     }  in
                   let uu___381_5932 = g  in
                   {
                     FStar_Tactics_Types.goal_main_env =
                       (uu___381_5932.FStar_Tactics_Types.goal_main_env);
                     FStar_Tactics_Types.goal_ctx_uvar = new_goal;
                     FStar_Tactics_Types.opts =
                       (uu___381_5932.FStar_Tactics_Types.opts);
                     FStar_Tactics_Types.is_guard =
                       (uu___381_5932.FStar_Tactics_Types.is_guard)
                   })
  
let (rewrite : FStar_Syntax_Syntax.binder -> unit tac) =
  fun h  ->
    let uu____5942 =
      let uu____5945 = cur_goal ()  in
      bind uu____5945
        (fun goal  ->
           let uu____5953 = h  in
           match uu____5953 with
           | (bv,uu____5957) ->
               mlog
                 (fun uu____5961  ->
                    let uu____5962 = FStar_Syntax_Print.bv_to_string bv  in
                    let uu____5963 =
                      FStar_Syntax_Print.term_to_string
                        bv.FStar_Syntax_Syntax.sort
                       in
                    FStar_Util.print2 "+++Rewrite %s : %s\n" uu____5962
                      uu____5963)
                 (fun uu____5966  ->
                    let uu____5967 =
                      let uu____5976 = FStar_Tactics_Types.goal_env goal  in
                      split_env bv uu____5976  in
                    match uu____5967 with
                    | FStar_Pervasives_Native.None  ->
                        fail "binder not found in environment"
                    | FStar_Pervasives_Native.Some (e0,bvs) ->
                        let uu____5997 =
                          destruct_eq bv.FStar_Syntax_Syntax.sort  in
                        (match uu____5997 with
                         | FStar_Pervasives_Native.Some (x,e) ->
                             let uu____6012 =
                               let uu____6013 = FStar_Syntax_Subst.compress x
                                  in
                               uu____6013.FStar_Syntax_Syntax.n  in
                             (match uu____6012 with
                              | FStar_Syntax_Syntax.Tm_name x1 ->
                                  let s = [FStar_Syntax_Syntax.NT (x1, e)]
                                     in
                                  let s1 bv1 =
                                    let uu___382_6030 = bv1  in
                                    let uu____6031 =
                                      FStar_Syntax_Subst.subst s
                                        bv1.FStar_Syntax_Syntax.sort
                                       in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___382_6030.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___382_6030.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = uu____6031
                                    }  in
                                  let bvs1 = FStar_List.map s1 bvs  in
                                  let new_env = push_bvs e0 (bv :: bvs1)  in
                                  let new_goal =
                                    let uu___383_6039 =
                                      goal.FStar_Tactics_Types.goal_ctx_uvar
                                       in
                                    let uu____6040 =
                                      FStar_TypeChecker_Env.all_binders
                                        new_env
                                       in
                                    let uu____6047 =
                                      let uu____6050 =
                                        FStar_Tactics_Types.goal_type goal
                                         in
                                      FStar_Syntax_Subst.subst s uu____6050
                                       in
                                    {
                                      FStar_Syntax_Syntax.ctx_uvar_head =
                                        (uu___383_6039.FStar_Syntax_Syntax.ctx_uvar_head);
                                      FStar_Syntax_Syntax.ctx_uvar_gamma =
                                        (new_env.FStar_TypeChecker_Env.gamma);
                                      FStar_Syntax_Syntax.ctx_uvar_binders =
                                        uu____6040;
                                      FStar_Syntax_Syntax.ctx_uvar_typ =
                                        uu____6047;
                                      FStar_Syntax_Syntax.ctx_uvar_reason =
                                        (uu___383_6039.FStar_Syntax_Syntax.ctx_uvar_reason);
                                      FStar_Syntax_Syntax.ctx_uvar_should_check
                                        =
                                        (uu___383_6039.FStar_Syntax_Syntax.ctx_uvar_should_check);
                                      FStar_Syntax_Syntax.ctx_uvar_range =
                                        (uu___383_6039.FStar_Syntax_Syntax.ctx_uvar_range)
                                    }  in
                                  replace_cur
                                    (let uu___384_6053 = goal  in
                                     {
                                       FStar_Tactics_Types.goal_main_env =
                                         (uu___384_6053.FStar_Tactics_Types.goal_main_env);
                                       FStar_Tactics_Types.goal_ctx_uvar =
                                         new_goal;
                                       FStar_Tactics_Types.opts =
                                         (uu___384_6053.FStar_Tactics_Types.opts);
                                       FStar_Tactics_Types.is_guard =
                                         (uu___384_6053.FStar_Tactics_Types.is_guard)
                                     })
                              | uu____6054 ->
                                  fail
                                    "Not an equality hypothesis with a variable on the LHS")
                         | uu____6055 -> fail "Not an equality hypothesis")))
       in
    FStar_All.pipe_left (wrap_err "rewrite") uu____5942
  
let (rename_to : FStar_Syntax_Syntax.binder -> Prims.string -> unit tac) =
  fun b  ->
    fun s  ->
      let uu____6080 =
        let uu____6083 = cur_goal ()  in
        bind uu____6083
          (fun goal  ->
             let uu____6094 = b  in
             match uu____6094 with
             | (bv,uu____6098) ->
                 let bv' =
                   let uu____6100 =
                     let uu___385_6101 = bv  in
                     let uu____6102 =
                       FStar_Ident.mk_ident
                         (s,
                           ((bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange))
                        in
                     {
                       FStar_Syntax_Syntax.ppname = uu____6102;
                       FStar_Syntax_Syntax.index =
                         (uu___385_6101.FStar_Syntax_Syntax.index);
                       FStar_Syntax_Syntax.sort =
                         (uu___385_6101.FStar_Syntax_Syntax.sort)
                     }  in
                   FStar_Syntax_Syntax.freshen_bv uu____6100  in
                 let s1 =
                   let uu____6106 =
                     let uu____6107 =
                       let uu____6114 = FStar_Syntax_Syntax.bv_to_name bv'
                          in
                       (bv, uu____6114)  in
                     FStar_Syntax_Syntax.NT uu____6107  in
                   [uu____6106]  in
                 let uu____6119 = subst_goal bv bv' s1 goal  in
                 (match uu____6119 with
                  | FStar_Pervasives_Native.None  ->
                      fail "binder not found in environment"
                  | FStar_Pervasives_Native.Some goal1 -> replace_cur goal1))
         in
      FStar_All.pipe_left (wrap_err "rename_to") uu____6080
  
let (binder_retype : FStar_Syntax_Syntax.binder -> unit tac) =
  fun b  ->
    let uu____6138 =
      let uu____6141 = cur_goal ()  in
      bind uu____6141
        (fun goal  ->
           let uu____6150 = b  in
           match uu____6150 with
           | (bv,uu____6154) ->
               let uu____6155 =
                 let uu____6164 = FStar_Tactics_Types.goal_env goal  in
                 split_env bv uu____6164  in
               (match uu____6155 with
                | FStar_Pervasives_Native.None  ->
                    fail "binder is not present in environment"
                | FStar_Pervasives_Native.Some (e0,bvs) ->
                    let uu____6185 = FStar_Syntax_Util.type_u ()  in
                    (match uu____6185 with
                     | (ty,u) ->
                         let uu____6194 = new_uvar "binder_retype" e0 ty  in
                         bind uu____6194
                           (fun uu____6212  ->
                              match uu____6212 with
                              | (t',u_t') ->
                                  let bv'' =
                                    let uu___386_6222 = bv  in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___386_6222.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___386_6222.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = t'
                                    }  in
                                  let s =
                                    let uu____6226 =
                                      let uu____6227 =
                                        let uu____6234 =
                                          FStar_Syntax_Syntax.bv_to_name bv''
                                           in
                                        (bv, uu____6234)  in
                                      FStar_Syntax_Syntax.NT uu____6227  in
                                    [uu____6226]  in
                                  let bvs1 =
                                    FStar_List.map
                                      (fun b1  ->
                                         let uu___387_6246 = b1  in
                                         let uu____6247 =
                                           FStar_Syntax_Subst.subst s
                                             b1.FStar_Syntax_Syntax.sort
                                            in
                                         {
                                           FStar_Syntax_Syntax.ppname =
                                             (uu___387_6246.FStar_Syntax_Syntax.ppname);
                                           FStar_Syntax_Syntax.index =
                                             (uu___387_6246.FStar_Syntax_Syntax.index);
                                           FStar_Syntax_Syntax.sort =
                                             uu____6247
                                         }) bvs
                                     in
                                  let env' = push_bvs e0 (bv'' :: bvs1)  in
                                  bind __dismiss
                                    (fun uu____6254  ->
                                       let new_goal =
                                         let uu____6256 =
                                           FStar_Tactics_Types.goal_with_env
                                             goal env'
                                            in
                                         let uu____6257 =
                                           let uu____6258 =
                                             FStar_Tactics_Types.goal_type
                                               goal
                                              in
                                           FStar_Syntax_Subst.subst s
                                             uu____6258
                                            in
                                         FStar_Tactics_Types.goal_with_type
                                           uu____6256 uu____6257
                                          in
                                       let uu____6259 = add_goals [new_goal]
                                          in
                                       bind uu____6259
                                         (fun uu____6264  ->
                                            let uu____6265 =
                                              FStar_Syntax_Util.mk_eq2
                                                (FStar_Syntax_Syntax.U_succ u)
                                                ty
                                                bv.FStar_Syntax_Syntax.sort
                                                t'
                                               in
                                            add_irrelevant_goal
                                              "binder_retype equation" e0
                                              uu____6265
                                              goal.FStar_Tactics_Types.opts))))))
       in
    FStar_All.pipe_left (wrap_err "binder_retype") uu____6138
  
let (norm_binder_type :
  FStar_Syntax_Embeddings.norm_step Prims.list ->
    FStar_Syntax_Syntax.binder -> unit tac)
  =
  fun s  ->
    fun b  ->
      let uu____6288 =
        let uu____6291 = cur_goal ()  in
        bind uu____6291
          (fun goal  ->
             let uu____6300 = b  in
             match uu____6300 with
             | (bv,uu____6304) ->
                 let uu____6305 =
                   let uu____6314 = FStar_Tactics_Types.goal_env goal  in
                   split_env bv uu____6314  in
                 (match uu____6305 with
                  | FStar_Pervasives_Native.None  ->
                      fail "binder is not present in environment"
                  | FStar_Pervasives_Native.Some (e0,bvs) ->
                      let steps =
                        let uu____6338 =
                          FStar_TypeChecker_Normalize.tr_norm_steps s  in
                        FStar_List.append
                          [FStar_TypeChecker_Normalize.Reify;
                          FStar_TypeChecker_Normalize.UnfoldTac] uu____6338
                         in
                      let sort' =
                        normalize steps e0 bv.FStar_Syntax_Syntax.sort  in
                      let bv' =
                        let uu___388_6343 = bv  in
                        {
                          FStar_Syntax_Syntax.ppname =
                            (uu___388_6343.FStar_Syntax_Syntax.ppname);
                          FStar_Syntax_Syntax.index =
                            (uu___388_6343.FStar_Syntax_Syntax.index);
                          FStar_Syntax_Syntax.sort = sort'
                        }  in
                      let env' = push_bvs e0 (bv' :: bvs)  in
                      let uu____6345 =
                        FStar_Tactics_Types.goal_with_env goal env'  in
                      replace_cur uu____6345))
         in
      FStar_All.pipe_left (wrap_err "norm_binder_type") uu____6288
  
let (revert : unit -> unit tac) =
  fun uu____6356  ->
    let uu____6359 = cur_goal ()  in
    bind uu____6359
      (fun goal  ->
         let uu____6365 =
           let uu____6372 = FStar_Tactics_Types.goal_env goal  in
           FStar_TypeChecker_Env.pop_bv uu____6372  in
         match uu____6365 with
         | FStar_Pervasives_Native.None  ->
             fail "Cannot revert; empty context"
         | FStar_Pervasives_Native.Some (x,env') ->
             let typ' =
               let uu____6388 =
                 let uu____6391 = FStar_Tactics_Types.goal_type goal  in
                 FStar_Syntax_Syntax.mk_Total uu____6391  in
               FStar_Syntax_Util.arrow [(x, FStar_Pervasives_Native.None)]
                 uu____6388
                in
             let uu____6400 = new_uvar "revert" env' typ'  in
             bind uu____6400
               (fun uu____6415  ->
                  match uu____6415 with
                  | (r,u_r) ->
                      let uu____6424 =
                        let uu____6427 =
                          let uu____6428 =
                            let uu____6429 =
                              FStar_Tactics_Types.goal_type goal  in
                            uu____6429.FStar_Syntax_Syntax.pos  in
                          let uu____6432 =
                            let uu____6437 =
                              let uu____6438 =
                                let uu____6445 =
                                  FStar_Syntax_Syntax.bv_to_name x  in
                                FStar_Syntax_Syntax.as_arg uu____6445  in
                              [uu____6438]  in
                            FStar_Syntax_Syntax.mk_Tm_app r uu____6437  in
                          uu____6432 FStar_Pervasives_Native.None uu____6428
                           in
                        set_solution goal uu____6427  in
                      bind uu____6424
                        (fun uu____6462  ->
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
      let uu____6474 = FStar_Syntax_Free.names t  in
      FStar_Util.set_mem bv uu____6474
  
let rec (clear : FStar_Syntax_Syntax.binder -> unit tac) =
  fun b  ->
    let bv = FStar_Pervasives_Native.fst b  in
    let uu____6487 = cur_goal ()  in
    bind uu____6487
      (fun goal  ->
         mlog
           (fun uu____6495  ->
              let uu____6496 = FStar_Syntax_Print.binder_to_string b  in
              let uu____6497 =
                let uu____6498 =
                  let uu____6499 =
                    let uu____6506 = FStar_Tactics_Types.goal_env goal  in
                    FStar_TypeChecker_Env.all_binders uu____6506  in
                  FStar_All.pipe_right uu____6499 FStar_List.length  in
                FStar_All.pipe_right uu____6498 FStar_Util.string_of_int  in
              FStar_Util.print2 "Clear of (%s), env has %s binders\n"
                uu____6496 uu____6497)
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
                (let uu___392_6749 = t  in
                 {
                   FStar_Syntax_Syntax.n = tn;
                   FStar_Syntax_Syntax.pos =
                     (uu___392_6749.FStar_Syntax_Syntax.pos);
                   FStar_Syntax_Syntax.vars =
                     (uu___392_6749.FStar_Syntax_Syntax.vars)
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
                     let uu____6793 = ff hd1  in
                     bind uu____6793
                       (fun hd2  ->
                          let fa uu____6815 =
                            match uu____6815 with
                            | (a,q) ->
                                let uu____6828 = ff a  in
                                bind uu____6828 (fun a1  -> ret (a1, q))
                             in
                          let uu____6841 = mapM fa args  in
                          bind uu____6841
                            (fun args1  ->
                               ret (FStar_Syntax_Syntax.Tm_app (hd2, args1))))
                 | FStar_Syntax_Syntax.Tm_abs (bs,t2,k) ->
                     let uu____6907 = FStar_Syntax_Subst.open_term bs t2  in
                     (match uu____6907 with
                      | (bs1,t') ->
                          let uu____6916 =
                            let uu____6919 =
                              FStar_TypeChecker_Env.push_binders env bs1  in
                            tac_fold_env d f uu____6919 t'  in
                          bind uu____6916
                            (fun t''  ->
                               let uu____6923 =
                                 let uu____6924 =
                                   let uu____6941 =
                                     FStar_Syntax_Subst.close_binders bs1  in
                                   let uu____6948 =
                                     FStar_Syntax_Subst.close bs1 t''  in
                                   (uu____6941, uu____6948, k)  in
                                 FStar_Syntax_Syntax.Tm_abs uu____6924  in
                               ret uu____6923))
                 | FStar_Syntax_Syntax.Tm_arrow (bs,k) -> ret tn
                 | FStar_Syntax_Syntax.Tm_match (hd1,brs) ->
                     let uu____7017 = ff hd1  in
                     bind uu____7017
                       (fun hd2  ->
                          let ffb br =
                            let uu____7032 =
                              FStar_Syntax_Subst.open_branch br  in
                            match uu____7032 with
                            | (pat,w,e) ->
                                let bvs = FStar_Syntax_Syntax.pat_bvs pat  in
                                let ff1 =
                                  let uu____7064 =
                                    FStar_TypeChecker_Env.push_bvs env bvs
                                     in
                                  tac_fold_env d f uu____7064  in
                                let uu____7065 = ff1 e  in
                                bind uu____7065
                                  (fun e1  ->
                                     let br1 =
                                       FStar_Syntax_Subst.close_branch
                                         (pat, w, e1)
                                        in
                                     ret br1)
                             in
                          let uu____7080 = mapM ffb brs  in
                          bind uu____7080
                            (fun brs1  ->
                               ret (FStar_Syntax_Syntax.Tm_match (hd2, brs1))))
                 | FStar_Syntax_Syntax.Tm_let
                     ((false
                       ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inl bv;
                          FStar_Syntax_Syntax.lbunivs = uu____7124;
                          FStar_Syntax_Syntax.lbtyp = uu____7125;
                          FStar_Syntax_Syntax.lbeff = uu____7126;
                          FStar_Syntax_Syntax.lbdef = def;
                          FStar_Syntax_Syntax.lbattrs = uu____7128;
                          FStar_Syntax_Syntax.lbpos = uu____7129;_}::[]),e)
                     ->
                     let lb =
                       let uu____7154 =
                         let uu____7155 = FStar_Syntax_Subst.compress t1  in
                         uu____7155.FStar_Syntax_Syntax.n  in
                       match uu____7154 with
                       | FStar_Syntax_Syntax.Tm_let
                           ((false ,lb::[]),uu____7159) -> lb
                       | uu____7172 -> failwith "impossible"  in
                     let fflb lb1 =
                       let uu____7181 = ff lb1.FStar_Syntax_Syntax.lbdef  in
                       bind uu____7181
                         (fun def1  ->
                            ret
                              (let uu___389_7187 = lb1  in
                               {
                                 FStar_Syntax_Syntax.lbname =
                                   (uu___389_7187.FStar_Syntax_Syntax.lbname);
                                 FStar_Syntax_Syntax.lbunivs =
                                   (uu___389_7187.FStar_Syntax_Syntax.lbunivs);
                                 FStar_Syntax_Syntax.lbtyp =
                                   (uu___389_7187.FStar_Syntax_Syntax.lbtyp);
                                 FStar_Syntax_Syntax.lbeff =
                                   (uu___389_7187.FStar_Syntax_Syntax.lbeff);
                                 FStar_Syntax_Syntax.lbdef = def1;
                                 FStar_Syntax_Syntax.lbattrs =
                                   (uu___389_7187.FStar_Syntax_Syntax.lbattrs);
                                 FStar_Syntax_Syntax.lbpos =
                                   (uu___389_7187.FStar_Syntax_Syntax.lbpos)
                               }))
                        in
                     let uu____7188 = fflb lb  in
                     bind uu____7188
                       (fun lb1  ->
                          let uu____7198 =
                            let uu____7203 =
                              let uu____7204 =
                                FStar_Syntax_Syntax.mk_binder bv  in
                              [uu____7204]  in
                            FStar_Syntax_Subst.open_term uu____7203 e  in
                          match uu____7198 with
                          | (bs,e1) ->
                              let ff1 =
                                let uu____7228 =
                                  FStar_TypeChecker_Env.push_binders env bs
                                   in
                                tac_fold_env d f uu____7228  in
                              let uu____7229 = ff1 e1  in
                              bind uu____7229
                                (fun e2  ->
                                   let e3 = FStar_Syntax_Subst.close bs e2
                                      in
                                   ret
                                     (FStar_Syntax_Syntax.Tm_let
                                        ((false, [lb1]), e3))))
                 | FStar_Syntax_Syntax.Tm_let ((true ,lbs),e) ->
                     let fflb lb =
                       let uu____7270 = ff lb.FStar_Syntax_Syntax.lbdef  in
                       bind uu____7270
                         (fun def  ->
                            ret
                              (let uu___390_7276 = lb  in
                               {
                                 FStar_Syntax_Syntax.lbname =
                                   (uu___390_7276.FStar_Syntax_Syntax.lbname);
                                 FStar_Syntax_Syntax.lbunivs =
                                   (uu___390_7276.FStar_Syntax_Syntax.lbunivs);
                                 FStar_Syntax_Syntax.lbtyp =
                                   (uu___390_7276.FStar_Syntax_Syntax.lbtyp);
                                 FStar_Syntax_Syntax.lbeff =
                                   (uu___390_7276.FStar_Syntax_Syntax.lbeff);
                                 FStar_Syntax_Syntax.lbdef = def;
                                 FStar_Syntax_Syntax.lbattrs =
                                   (uu___390_7276.FStar_Syntax_Syntax.lbattrs);
                                 FStar_Syntax_Syntax.lbpos =
                                   (uu___390_7276.FStar_Syntax_Syntax.lbpos)
                               }))
                        in
                     let uu____7277 = FStar_Syntax_Subst.open_let_rec lbs e
                        in
                     (match uu____7277 with
                      | (lbs1,e1) ->
                          let uu____7292 = mapM fflb lbs1  in
                          bind uu____7292
                            (fun lbs2  ->
                               let uu____7304 = ff e1  in
                               bind uu____7304
                                 (fun e2  ->
                                    let uu____7312 =
                                      FStar_Syntax_Subst.close_let_rec lbs2
                                        e2
                                       in
                                    match uu____7312 with
                                    | (lbs3,e3) ->
                                        ret
                                          (FStar_Syntax_Syntax.Tm_let
                                             ((true, lbs3), e3)))))
                 | FStar_Syntax_Syntax.Tm_ascribed (t2,asc,eff) ->
                     let uu____7380 = ff t2  in
                     bind uu____7380
                       (fun t3  ->
                          ret
                            (FStar_Syntax_Syntax.Tm_ascribed (t3, asc, eff)))
                 | FStar_Syntax_Syntax.Tm_meta (t2,m) ->
                     let uu____7411 = ff t2  in
                     bind uu____7411
                       (fun t3  -> ret (FStar_Syntax_Syntax.Tm_meta (t3, m)))
                 | uu____7418 -> ret tn  in
               bind tn1
                 (fun tn2  ->
                    let t' =
                      let uu___391_7425 = t1  in
                      {
                        FStar_Syntax_Syntax.n = tn2;
                        FStar_Syntax_Syntax.pos =
                          (uu___391_7425.FStar_Syntax_Syntax.pos);
                        FStar_Syntax_Syntax.vars =
                          (uu___391_7425.FStar_Syntax_Syntax.vars)
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
            let uu____7462 = FStar_TypeChecker_TcTerm.tc_term env t  in
            match uu____7462 with
            | (t1,lcomp,g) ->
                let uu____7474 =
                  (let uu____7477 =
                     FStar_Syntax_Util.is_pure_or_ghost_lcomp lcomp  in
                   Prims.op_Negation uu____7477) ||
                    (let uu____7479 = FStar_TypeChecker_Env.is_trivial g  in
                     Prims.op_Negation uu____7479)
                   in
                if uu____7474
                then ret t1
                else
                  (let rewrite_eq =
                     let typ = lcomp.FStar_Syntax_Syntax.res_typ  in
                     let uu____7487 = new_uvar "pointwise_rec" env typ  in
                     bind uu____7487
                       (fun uu____7503  ->
                          match uu____7503 with
                          | (ut,uvar_ut) ->
                              (log ps
                                 (fun uu____7516  ->
                                    let uu____7517 =
                                      FStar_Syntax_Print.term_to_string t1
                                       in
                                    let uu____7518 =
                                      FStar_Syntax_Print.term_to_string ut
                                       in
                                    FStar_Util.print2
                                      "Pointwise_rec: making equality\n\t%s ==\n\t%s\n"
                                      uu____7517 uu____7518);
                               (let uu____7519 =
                                  let uu____7522 =
                                    let uu____7523 =
                                      FStar_TypeChecker_TcTerm.universe_of
                                        env typ
                                       in
                                    FStar_Syntax_Util.mk_eq2 uu____7523 typ
                                      t1 ut
                                     in
                                  add_irrelevant_goal
                                    "pointwise_rec equation" env uu____7522
                                    opts
                                   in
                                bind uu____7519
                                  (fun uu____7526  ->
                                     let uu____7527 =
                                       bind tau
                                         (fun uu____7533  ->
                                            let ut1 =
                                              FStar_TypeChecker_Normalize.reduce_uvar_solutions
                                                env ut
                                               in
                                            log ps
                                              (fun uu____7539  ->
                                                 let uu____7540 =
                                                   FStar_Syntax_Print.term_to_string
                                                     t1
                                                    in
                                                 let uu____7541 =
                                                   FStar_Syntax_Print.term_to_string
                                                     ut1
                                                    in
                                                 FStar_Util.print2
                                                   "Pointwise_rec: succeeded rewriting\n\t%s to\n\t%s\n"
                                                   uu____7540 uu____7541);
                                            ret ut1)
                                        in
                                     focus uu____7527))))
                      in
                   let uu____7542 = trytac' rewrite_eq  in
                   bind uu____7542
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
          let uu____7740 = FStar_Syntax_Subst.compress t  in
          maybe_continue ctrl uu____7740
            (fun t1  ->
               let uu____7748 =
                 f env
                   (let uu___395_7757 = t1  in
                    {
                      FStar_Syntax_Syntax.n = (t1.FStar_Syntax_Syntax.n);
                      FStar_Syntax_Syntax.pos =
                        (uu___395_7757.FStar_Syntax_Syntax.pos);
                      FStar_Syntax_Syntax.vars =
                        (uu___395_7757.FStar_Syntax_Syntax.vars)
                    })
                  in
               bind uu____7748
                 (fun uu____7773  ->
                    match uu____7773 with
                    | (t2,ctrl1) ->
                        maybe_continue ctrl1 t2
                          (fun t3  ->
                             let uu____7796 =
                               let uu____7797 =
                                 FStar_Syntax_Subst.compress t3  in
                               uu____7797.FStar_Syntax_Syntax.n  in
                             match uu____7796 with
                             | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
                                 let uu____7830 =
                                   ctrl_tac_fold f env ctrl1 hd1  in
                                 bind uu____7830
                                   (fun uu____7855  ->
                                      match uu____7855 with
                                      | (hd2,ctrl2) ->
                                          let ctrl3 = keep_going ctrl2  in
                                          let uu____7871 =
                                            ctrl_tac_fold_args f env ctrl3
                                              args
                                             in
                                          bind uu____7871
                                            (fun uu____7898  ->
                                               match uu____7898 with
                                               | (args1,ctrl4) ->
                                                   ret
                                                     ((let uu___393_7928 = t3
                                                          in
                                                       {
                                                         FStar_Syntax_Syntax.n
                                                           =
                                                           (FStar_Syntax_Syntax.Tm_app
                                                              (hd2, args1));
                                                         FStar_Syntax_Syntax.pos
                                                           =
                                                           (uu___393_7928.FStar_Syntax_Syntax.pos);
                                                         FStar_Syntax_Syntax.vars
                                                           =
                                                           (uu___393_7928.FStar_Syntax_Syntax.vars)
                                                       }), ctrl4)))
                             | FStar_Syntax_Syntax.Tm_abs (bs,t4,k) ->
                                 let uu____7964 =
                                   FStar_Syntax_Subst.open_term bs t4  in
                                 (match uu____7964 with
                                  | (bs1,t') ->
                                      let uu____7979 =
                                        let uu____7986 =
                                          FStar_TypeChecker_Env.push_binders
                                            env bs1
                                           in
                                        ctrl_tac_fold f uu____7986 ctrl1 t'
                                         in
                                      bind uu____7979
                                        (fun uu____8004  ->
                                           match uu____8004 with
                                           | (t'',ctrl2) ->
                                               let uu____8019 =
                                                 let uu____8026 =
                                                   let uu___394_8029 = t4  in
                                                   let uu____8032 =
                                                     let uu____8033 =
                                                       let uu____8050 =
                                                         FStar_Syntax_Subst.close_binders
                                                           bs1
                                                          in
                                                       let uu____8057 =
                                                         FStar_Syntax_Subst.close
                                                           bs1 t''
                                                          in
                                                       (uu____8050,
                                                         uu____8057, k)
                                                        in
                                                     FStar_Syntax_Syntax.Tm_abs
                                                       uu____8033
                                                      in
                                                   {
                                                     FStar_Syntax_Syntax.n =
                                                       uu____8032;
                                                     FStar_Syntax_Syntax.pos
                                                       =
                                                       (uu___394_8029.FStar_Syntax_Syntax.pos);
                                                     FStar_Syntax_Syntax.vars
                                                       =
                                                       (uu___394_8029.FStar_Syntax_Syntax.vars)
                                                   }  in
                                                 (uu____8026, ctrl2)  in
                                               ret uu____8019))
                             | FStar_Syntax_Syntax.Tm_arrow (bs,k) ->
                                 ret (t3, ctrl1)
                             | uu____8104 -> ret (t3, ctrl1))))

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
              let uu____8147 = ctrl_tac_fold f env ctrl t  in
              bind uu____8147
                (fun uu____8171  ->
                   match uu____8171 with
                   | (t1,ctrl1) ->
                       let uu____8186 = ctrl_tac_fold_args f env ctrl1 ts1
                          in
                       bind uu____8186
                         (fun uu____8213  ->
                            match uu____8213 with
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
              let uu____8295 =
                let uu____8302 =
                  add_irrelevant_goal "dummy" env FStar_Syntax_Util.t_true
                    opts
                   in
                bind uu____8302
                  (fun uu____8311  ->
                     let uu____8312 = ctrl t1  in
                     bind uu____8312
                       (fun res  ->
                          let uu____8335 = trivial ()  in
                          bind uu____8335 (fun uu____8343  -> ret res)))
                 in
              bind uu____8295
                (fun uu____8359  ->
                   match uu____8359 with
                   | (should_rewrite,ctrl1) ->
                       if Prims.op_Negation should_rewrite
                       then ret (t1, ctrl1)
                       else
                         (let uu____8383 =
                            FStar_TypeChecker_TcTerm.tc_term env t1  in
                          match uu____8383 with
                          | (t2,lcomp,g) ->
                              let uu____8399 =
                                (let uu____8402 =
                                   FStar_Syntax_Util.is_pure_or_ghost_lcomp
                                     lcomp
                                    in
                                 Prims.op_Negation uu____8402) ||
                                  (let uu____8404 =
                                     FStar_TypeChecker_Env.is_trivial g  in
                                   Prims.op_Negation uu____8404)
                                 in
                              if uu____8399
                              then ret (t2, globalStop)
                              else
                                (let typ = lcomp.FStar_Syntax_Syntax.res_typ
                                    in
                                 let uu____8417 =
                                   new_uvar "pointwise_rec" env typ  in
                                 bind uu____8417
                                   (fun uu____8437  ->
                                      match uu____8437 with
                                      | (ut,uvar_ut) ->
                                          (log ps
                                             (fun uu____8454  ->
                                                let uu____8455 =
                                                  FStar_Syntax_Print.term_to_string
                                                    t2
                                                   in
                                                let uu____8456 =
                                                  FStar_Syntax_Print.term_to_string
                                                    ut
                                                   in
                                                FStar_Util.print2
                                                  "Pointwise_rec: making equality\n\t%s ==\n\t%s\n"
                                                  uu____8455 uu____8456);
                                           (let uu____8457 =
                                              let uu____8460 =
                                                let uu____8461 =
                                                  FStar_TypeChecker_TcTerm.universe_of
                                                    env typ
                                                   in
                                                FStar_Syntax_Util.mk_eq2
                                                  uu____8461 typ t2 ut
                                                 in
                                              add_irrelevant_goal
                                                "rewrite_rec equation" env
                                                uu____8460 opts
                                               in
                                            bind uu____8457
                                              (fun uu____8468  ->
                                                 let uu____8469 =
                                                   bind rewriter
                                                     (fun uu____8483  ->
                                                        let ut1 =
                                                          FStar_TypeChecker_Normalize.reduce_uvar_solutions
                                                            env ut
                                                           in
                                                        log ps
                                                          (fun uu____8489  ->
                                                             let uu____8490 =
                                                               FStar_Syntax_Print.term_to_string
                                                                 t2
                                                                in
                                                             let uu____8491 =
                                                               FStar_Syntax_Print.term_to_string
                                                                 ut1
                                                                in
                                                             FStar_Util.print2
                                                               "rewrite_rec: succeeded rewriting\n\t%s to\n\t%s\n"
                                                               uu____8490
                                                               uu____8491);
                                                        ret (ut1, ctrl1))
                                                    in
                                                 focus uu____8469)))))))
  
let (topdown_rewrite :
  (FStar_Syntax_Syntax.term ->
     (Prims.bool,FStar_BigInt.t) FStar_Pervasives_Native.tuple2 tac)
    -> unit tac -> unit tac)
  =
  fun ctrl  ->
    fun rewriter  ->
      let uu____8532 =
        bind get
          (fun ps  ->
             let uu____8542 =
               match ps.FStar_Tactics_Types.goals with
               | g::gs -> (g, gs)
               | [] -> failwith "no goals"  in
             match uu____8542 with
             | (g,gs) ->
                 let gt1 = FStar_Tactics_Types.goal_type g  in
                 (log ps
                    (fun uu____8579  ->
                       let uu____8580 = FStar_Syntax_Print.term_to_string gt1
                          in
                       FStar_Util.print1 "Topdown_rewrite starting with %s\n"
                         uu____8580);
                  bind dismiss_all
                    (fun uu____8583  ->
                       let uu____8584 =
                         let uu____8591 = FStar_Tactics_Types.goal_env g  in
                         ctrl_tac_fold
                           (rewrite_rec ps ctrl rewriter
                              g.FStar_Tactics_Types.opts) uu____8591
                           keepGoing gt1
                          in
                       bind uu____8584
                         (fun uu____8603  ->
                            match uu____8603 with
                            | (gt',uu____8611) ->
                                (log ps
                                   (fun uu____8615  ->
                                      let uu____8616 =
                                        FStar_Syntax_Print.term_to_string gt'
                                         in
                                      FStar_Util.print1
                                        "Topdown_rewrite seems to have succeded with %s\n"
                                        uu____8616);
                                 (let uu____8617 = push_goals gs  in
                                  bind uu____8617
                                    (fun uu____8622  ->
                                       let uu____8623 =
                                         let uu____8626 =
                                           FStar_Tactics_Types.goal_with_type
                                             g gt'
                                            in
                                         [uu____8626]  in
                                       add_goals uu____8623)))))))
         in
      FStar_All.pipe_left (wrap_err "topdown_rewrite") uu____8532
  
let (pointwise : FStar_Tactics_Types.direction -> unit tac -> unit tac) =
  fun d  ->
    fun tau  ->
      let uu____8649 =
        bind get
          (fun ps  ->
             let uu____8659 =
               match ps.FStar_Tactics_Types.goals with
               | g::gs -> (g, gs)
               | [] -> failwith "no goals"  in
             match uu____8659 with
             | (g,gs) ->
                 let gt1 = FStar_Tactics_Types.goal_type g  in
                 (log ps
                    (fun uu____8696  ->
                       let uu____8697 = FStar_Syntax_Print.term_to_string gt1
                          in
                       FStar_Util.print1 "Pointwise starting with %s\n"
                         uu____8697);
                  bind dismiss_all
                    (fun uu____8700  ->
                       let uu____8701 =
                         let uu____8704 = FStar_Tactics_Types.goal_env g  in
                         tac_fold_env d
                           (pointwise_rec ps tau g.FStar_Tactics_Types.opts)
                           uu____8704 gt1
                          in
                       bind uu____8701
                         (fun gt'  ->
                            log ps
                              (fun uu____8712  ->
                                 let uu____8713 =
                                   FStar_Syntax_Print.term_to_string gt'  in
                                 FStar_Util.print1
                                   "Pointwise seems to have succeded with %s\n"
                                   uu____8713);
                            (let uu____8714 = push_goals gs  in
                             bind uu____8714
                               (fun uu____8719  ->
                                  let uu____8720 =
                                    let uu____8723 =
                                      FStar_Tactics_Types.goal_with_type g
                                        gt'
                                       in
                                    [uu____8723]  in
                                  add_goals uu____8720))))))
         in
      FStar_All.pipe_left (wrap_err "pointwise") uu____8649
  
let (trefl : unit -> unit tac) =
  fun uu____8734  ->
    let uu____8737 =
      let uu____8740 = cur_goal ()  in
      bind uu____8740
        (fun g  ->
           let uu____8758 =
             let uu____8763 = FStar_Tactics_Types.goal_type g  in
             FStar_Syntax_Util.un_squash uu____8763  in
           match uu____8758 with
           | FStar_Pervasives_Native.Some t ->
               let uu____8771 = FStar_Syntax_Util.head_and_args' t  in
               (match uu____8771 with
                | (hd1,args) ->
                    let uu____8804 =
                      let uu____8815 =
                        let uu____8816 = FStar_Syntax_Util.un_uinst hd1  in
                        uu____8816.FStar_Syntax_Syntax.n  in
                      (uu____8815, args)  in
                    (match uu____8804 with
                     | (FStar_Syntax_Syntax.Tm_fvar
                        fv,uu____8828::(l,uu____8830)::(r,uu____8832)::[])
                         when
                         FStar_Syntax_Syntax.fv_eq_lid fv
                           FStar_Parser_Const.eq2_lid
                         ->
                         let uu____8859 =
                           let uu____8862 = FStar_Tactics_Types.goal_env g
                              in
                           do_unify uu____8862 l r  in
                         bind uu____8859
                           (fun b  ->
                              if Prims.op_Negation b
                              then
                                let uu____8869 =
                                  let uu____8870 =
                                    FStar_Tactics_Types.goal_env g  in
                                  tts uu____8870 l  in
                                let uu____8871 =
                                  let uu____8872 =
                                    FStar_Tactics_Types.goal_env g  in
                                  tts uu____8872 r  in
                                fail2 "not a trivial equality (%s vs %s)"
                                  uu____8869 uu____8871
                              else solve' g FStar_Syntax_Util.exp_unit)
                     | (hd2,uu____8875) ->
                         let uu____8888 =
                           let uu____8889 = FStar_Tactics_Types.goal_env g
                              in
                           tts uu____8889 t  in
                         fail1 "trefl: not an equality (%s)" uu____8888))
           | FStar_Pervasives_Native.None  -> fail "not an irrelevant goal")
       in
    FStar_All.pipe_left (wrap_err "trefl") uu____8737
  
let (dup : unit -> unit tac) =
  fun uu____8902  ->
    let uu____8905 = cur_goal ()  in
    bind uu____8905
      (fun g  ->
         let uu____8911 =
           let uu____8918 = FStar_Tactics_Types.goal_env g  in
           let uu____8919 = FStar_Tactics_Types.goal_type g  in
           new_uvar "dup" uu____8918 uu____8919  in
         bind uu____8911
           (fun uu____8928  ->
              match uu____8928 with
              | (u,u_uvar) ->
                  let g' =
                    let uu___396_8938 = g  in
                    {
                      FStar_Tactics_Types.goal_main_env =
                        (uu___396_8938.FStar_Tactics_Types.goal_main_env);
                      FStar_Tactics_Types.goal_ctx_uvar = u_uvar;
                      FStar_Tactics_Types.opts =
                        (uu___396_8938.FStar_Tactics_Types.opts);
                      FStar_Tactics_Types.is_guard =
                        (uu___396_8938.FStar_Tactics_Types.is_guard)
                    }  in
                  bind __dismiss
                    (fun uu____8941  ->
                       let uu____8942 =
                         let uu____8945 = FStar_Tactics_Types.goal_env g  in
                         let uu____8946 =
                           let uu____8947 =
                             let uu____8948 = FStar_Tactics_Types.goal_env g
                                in
                             let uu____8949 = FStar_Tactics_Types.goal_type g
                                in
                             FStar_TypeChecker_TcTerm.universe_of uu____8948
                               uu____8949
                              in
                           let uu____8950 = FStar_Tactics_Types.goal_type g
                              in
                           let uu____8951 =
                             FStar_Tactics_Types.goal_witness g  in
                           FStar_Syntax_Util.mk_eq2 uu____8947 uu____8950 u
                             uu____8951
                            in
                         add_irrelevant_goal "dup equation" uu____8945
                           uu____8946 g.FStar_Tactics_Types.opts
                          in
                       bind uu____8942
                         (fun uu____8954  ->
                            let uu____8955 = add_goals [g']  in
                            bind uu____8955 (fun uu____8959  -> ret ())))))
  
let (flip : unit -> unit tac) =
  fun uu____8966  ->
    bind get
      (fun ps  ->
         match ps.FStar_Tactics_Types.goals with
         | g1::g2::gs ->
             set
               (let uu___397_8983 = ps  in
                {
                  FStar_Tactics_Types.main_context =
                    (uu___397_8983.FStar_Tactics_Types.main_context);
                  FStar_Tactics_Types.main_goal =
                    (uu___397_8983.FStar_Tactics_Types.main_goal);
                  FStar_Tactics_Types.all_implicits =
                    (uu___397_8983.FStar_Tactics_Types.all_implicits);
                  FStar_Tactics_Types.goals = (g2 :: g1 :: gs);
                  FStar_Tactics_Types.smt_goals =
                    (uu___397_8983.FStar_Tactics_Types.smt_goals);
                  FStar_Tactics_Types.depth =
                    (uu___397_8983.FStar_Tactics_Types.depth);
                  FStar_Tactics_Types.__dump =
                    (uu___397_8983.FStar_Tactics_Types.__dump);
                  FStar_Tactics_Types.psc =
                    (uu___397_8983.FStar_Tactics_Types.psc);
                  FStar_Tactics_Types.entry_range =
                    (uu___397_8983.FStar_Tactics_Types.entry_range);
                  FStar_Tactics_Types.guard_policy =
                    (uu___397_8983.FStar_Tactics_Types.guard_policy);
                  FStar_Tactics_Types.freshness =
                    (uu___397_8983.FStar_Tactics_Types.freshness);
                  FStar_Tactics_Types.tac_verb_dbg =
                    (uu___397_8983.FStar_Tactics_Types.tac_verb_dbg)
                })
         | uu____8984 -> fail "flip: less than 2 goals")
  
let (later : unit -> unit tac) =
  fun uu____8993  ->
    bind get
      (fun ps  ->
         match ps.FStar_Tactics_Types.goals with
         | [] -> ret ()
         | g::gs ->
             set
               (let uu___398_9006 = ps  in
                {
                  FStar_Tactics_Types.main_context =
                    (uu___398_9006.FStar_Tactics_Types.main_context);
                  FStar_Tactics_Types.main_goal =
                    (uu___398_9006.FStar_Tactics_Types.main_goal);
                  FStar_Tactics_Types.all_implicits =
                    (uu___398_9006.FStar_Tactics_Types.all_implicits);
                  FStar_Tactics_Types.goals = (FStar_List.append gs [g]);
                  FStar_Tactics_Types.smt_goals =
                    (uu___398_9006.FStar_Tactics_Types.smt_goals);
                  FStar_Tactics_Types.depth =
                    (uu___398_9006.FStar_Tactics_Types.depth);
                  FStar_Tactics_Types.__dump =
                    (uu___398_9006.FStar_Tactics_Types.__dump);
                  FStar_Tactics_Types.psc =
                    (uu___398_9006.FStar_Tactics_Types.psc);
                  FStar_Tactics_Types.entry_range =
                    (uu___398_9006.FStar_Tactics_Types.entry_range);
                  FStar_Tactics_Types.guard_policy =
                    (uu___398_9006.FStar_Tactics_Types.guard_policy);
                  FStar_Tactics_Types.freshness =
                    (uu___398_9006.FStar_Tactics_Types.freshness);
                  FStar_Tactics_Types.tac_verb_dbg =
                    (uu___398_9006.FStar_Tactics_Types.tac_verb_dbg)
                }))
  
let (qed : unit -> unit tac) =
  fun uu____9013  ->
    bind get
      (fun ps  ->
         match ps.FStar_Tactics_Types.goals with
         | [] -> ret ()
         | uu____9020 -> fail "Not done!")
  
let (cases :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 tac)
  =
  fun t  ->
    let uu____9040 =
      let uu____9047 = cur_goal ()  in
      bind uu____9047
        (fun g  ->
           let uu____9057 =
             let uu____9066 = FStar_Tactics_Types.goal_env g  in
             __tc uu____9066 t  in
           bind uu____9057
             (fun uu____9094  ->
                match uu____9094 with
                | (t1,typ,guard) ->
                    let uu____9110 = FStar_Syntax_Util.head_and_args typ  in
                    (match uu____9110 with
                     | (hd1,args) ->
                         let uu____9153 =
                           let uu____9166 =
                             let uu____9167 = FStar_Syntax_Util.un_uinst hd1
                                in
                             uu____9167.FStar_Syntax_Syntax.n  in
                           (uu____9166, args)  in
                         (match uu____9153 with
                          | (FStar_Syntax_Syntax.Tm_fvar
                             fv,(p,uu____9186)::(q,uu____9188)::[]) when
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
                                let uu____9226 =
                                  let uu____9227 =
                                    FStar_Tactics_Types.goal_env g  in
                                  FStar_TypeChecker_Env.push_bv uu____9227
                                    v_p
                                   in
                                FStar_Tactics_Types.goal_with_env g
                                  uu____9226
                                 in
                              let g2 =
                                let uu____9229 =
                                  let uu____9230 =
                                    FStar_Tactics_Types.goal_env g  in
                                  FStar_TypeChecker_Env.push_bv uu____9230
                                    v_q
                                   in
                                FStar_Tactics_Types.goal_with_env g
                                  uu____9229
                                 in
                              bind __dismiss
                                (fun uu____9237  ->
                                   let uu____9238 = add_goals [g1; g2]  in
                                   bind uu____9238
                                     (fun uu____9247  ->
                                        let uu____9248 =
                                          let uu____9253 =
                                            FStar_Syntax_Syntax.bv_to_name
                                              v_p
                                             in
                                          let uu____9254 =
                                            FStar_Syntax_Syntax.bv_to_name
                                              v_q
                                             in
                                          (uu____9253, uu____9254)  in
                                        ret uu____9248))
                          | uu____9259 ->
                              let uu____9272 =
                                let uu____9273 =
                                  FStar_Tactics_Types.goal_env g  in
                                tts uu____9273 typ  in
                              fail1 "Not a disjunction: %s" uu____9272))))
       in
    FStar_All.pipe_left (wrap_err "cases") uu____9040
  
let (set_options : Prims.string -> unit tac) =
  fun s  ->
    let uu____9303 =
      let uu____9306 = cur_goal ()  in
      bind uu____9306
        (fun g  ->
           FStar_Options.push ();
           (let uu____9319 = FStar_Util.smap_copy g.FStar_Tactics_Types.opts
               in
            FStar_Options.set uu____9319);
           (let res = FStar_Options.set_options FStar_Options.Set s  in
            let opts' = FStar_Options.peek ()  in
            FStar_Options.pop ();
            (match res with
             | FStar_Getopt.Success  ->
                 let g' =
                   let uu___399_9326 = g  in
                   {
                     FStar_Tactics_Types.goal_main_env =
                       (uu___399_9326.FStar_Tactics_Types.goal_main_env);
                     FStar_Tactics_Types.goal_ctx_uvar =
                       (uu___399_9326.FStar_Tactics_Types.goal_ctx_uvar);
                     FStar_Tactics_Types.opts = opts';
                     FStar_Tactics_Types.is_guard =
                       (uu___399_9326.FStar_Tactics_Types.is_guard)
                   }  in
                 replace_cur g'
             | FStar_Getopt.Error err ->
                 fail2 "Setting options `%s` failed: %s" s err
             | FStar_Getopt.Help  ->
                 fail1 "Setting options `%s` failed (got `Help`?)" s)))
       in
    FStar_All.pipe_left (wrap_err "set_options") uu____9303
  
let (top_env : unit -> env tac) =
  fun uu____9338  ->
    bind get
      (fun ps  -> FStar_All.pipe_left ret ps.FStar_Tactics_Types.main_context)
  
let (cur_env : unit -> env tac) =
  fun uu____9351  ->
    let uu____9354 = cur_goal ()  in
    bind uu____9354
      (fun g  ->
         let uu____9360 = FStar_Tactics_Types.goal_env g  in
         FStar_All.pipe_left ret uu____9360)
  
let (cur_goal' : unit -> FStar_Syntax_Syntax.term tac) =
  fun uu____9369  ->
    let uu____9372 = cur_goal ()  in
    bind uu____9372
      (fun g  ->
         let uu____9378 = FStar_Tactics_Types.goal_type g  in
         FStar_All.pipe_left ret uu____9378)
  
let (cur_witness : unit -> FStar_Syntax_Syntax.term tac) =
  fun uu____9387  ->
    let uu____9390 = cur_goal ()  in
    bind uu____9390
      (fun g  ->
         let uu____9396 = FStar_Tactics_Types.goal_witness g  in
         FStar_All.pipe_left ret uu____9396)
  
let (unquote :
  FStar_Reflection_Data.typ ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term tac)
  =
  fun ty  ->
    fun tm  ->
      let uu____9413 =
        mlog
          (fun uu____9418  ->
             let uu____9419 = FStar_Syntax_Print.term_to_string tm  in
             FStar_Util.print1 "unquote: tm = %s\n" uu____9419)
          (fun uu____9422  ->
             let uu____9423 = cur_goal ()  in
             bind uu____9423
               (fun goal  ->
                  let env =
                    let uu____9431 = FStar_Tactics_Types.goal_env goal  in
                    FStar_TypeChecker_Env.set_expected_typ uu____9431 ty  in
                  let uu____9432 = __tc env tm  in
                  bind uu____9432
                    (fun uu____9451  ->
                       match uu____9451 with
                       | (tm1,typ,guard) ->
                           mlog
                             (fun uu____9465  ->
                                let uu____9466 =
                                  FStar_Syntax_Print.term_to_string tm1  in
                                FStar_Util.print1 "unquote: tm' = %s\n"
                                  uu____9466)
                             (fun uu____9468  ->
                                mlog
                                  (fun uu____9471  ->
                                     let uu____9472 =
                                       FStar_Syntax_Print.term_to_string typ
                                        in
                                     FStar_Util.print1 "unquote: typ = %s\n"
                                       uu____9472)
                                  (fun uu____9475  ->
                                     let uu____9476 =
                                       proc_guard "unquote" env guard  in
                                     bind uu____9476
                                       (fun uu____9480  -> ret tm1))))))
         in
      FStar_All.pipe_left (wrap_err "unquote") uu____9413
  
let (uvar_env :
  env ->
    FStar_Reflection_Data.typ FStar_Pervasives_Native.option ->
      FStar_Syntax_Syntax.term tac)
  =
  fun env  ->
    fun ty  ->
      let uu____9503 =
        match ty with
        | FStar_Pervasives_Native.Some ty1 -> ret ty1
        | FStar_Pervasives_Native.None  ->
            let uu____9509 =
              let uu____9516 =
                let uu____9517 = FStar_Syntax_Util.type_u ()  in
                FStar_All.pipe_left FStar_Pervasives_Native.fst uu____9517
                 in
              new_uvar "uvar_env.2" env uu____9516  in
            bind uu____9509
              (fun uu____9533  ->
                 match uu____9533 with | (typ,uvar_typ) -> ret typ)
         in
      bind uu____9503
        (fun typ  ->
           let uu____9545 = new_uvar "uvar_env" env typ  in
           bind uu____9545
             (fun uu____9559  -> match uu____9559 with | (t,uvar_t) -> ret t))
  
let (unshelve : FStar_Syntax_Syntax.term -> unit tac) =
  fun t  ->
    let uu____9577 =
      bind get
        (fun ps  ->
           let env = ps.FStar_Tactics_Types.main_context  in
           let opts =
             match ps.FStar_Tactics_Types.goals with
             | g::uu____9596 -> g.FStar_Tactics_Types.opts
             | uu____9599 -> FStar_Options.peek ()  in
           let uu____9602 = FStar_Syntax_Util.head_and_args t  in
           match uu____9602 with
           | ({
                FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                  (ctx_uvar,uu____9620);
                FStar_Syntax_Syntax.pos = uu____9621;
                FStar_Syntax_Syntax.vars = uu____9622;_},uu____9623)
               ->
               let env1 =
                 let uu___400_9661 = env  in
                 {
                   FStar_TypeChecker_Env.solver =
                     (uu___400_9661.FStar_TypeChecker_Env.solver);
                   FStar_TypeChecker_Env.range =
                     (uu___400_9661.FStar_TypeChecker_Env.range);
                   FStar_TypeChecker_Env.curmodule =
                     (uu___400_9661.FStar_TypeChecker_Env.curmodule);
                   FStar_TypeChecker_Env.gamma =
                     (ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_gamma);
                   FStar_TypeChecker_Env.gamma_sig =
                     (uu___400_9661.FStar_TypeChecker_Env.gamma_sig);
                   FStar_TypeChecker_Env.gamma_cache =
                     (uu___400_9661.FStar_TypeChecker_Env.gamma_cache);
                   FStar_TypeChecker_Env.modules =
                     (uu___400_9661.FStar_TypeChecker_Env.modules);
                   FStar_TypeChecker_Env.expected_typ =
                     (uu___400_9661.FStar_TypeChecker_Env.expected_typ);
                   FStar_TypeChecker_Env.sigtab =
                     (uu___400_9661.FStar_TypeChecker_Env.sigtab);
                   FStar_TypeChecker_Env.is_pattern =
                     (uu___400_9661.FStar_TypeChecker_Env.is_pattern);
                   FStar_TypeChecker_Env.instantiate_imp =
                     (uu___400_9661.FStar_TypeChecker_Env.instantiate_imp);
                   FStar_TypeChecker_Env.effects =
                     (uu___400_9661.FStar_TypeChecker_Env.effects);
                   FStar_TypeChecker_Env.generalize =
                     (uu___400_9661.FStar_TypeChecker_Env.generalize);
                   FStar_TypeChecker_Env.letrecs =
                     (uu___400_9661.FStar_TypeChecker_Env.letrecs);
                   FStar_TypeChecker_Env.top_level =
                     (uu___400_9661.FStar_TypeChecker_Env.top_level);
                   FStar_TypeChecker_Env.check_uvars =
                     (uu___400_9661.FStar_TypeChecker_Env.check_uvars);
                   FStar_TypeChecker_Env.use_eq =
                     (uu___400_9661.FStar_TypeChecker_Env.use_eq);
                   FStar_TypeChecker_Env.is_iface =
                     (uu___400_9661.FStar_TypeChecker_Env.is_iface);
                   FStar_TypeChecker_Env.admit =
                     (uu___400_9661.FStar_TypeChecker_Env.admit);
                   FStar_TypeChecker_Env.lax =
                     (uu___400_9661.FStar_TypeChecker_Env.lax);
                   FStar_TypeChecker_Env.lax_universes =
                     (uu___400_9661.FStar_TypeChecker_Env.lax_universes);
                   FStar_TypeChecker_Env.phase1 =
                     (uu___400_9661.FStar_TypeChecker_Env.phase1);
                   FStar_TypeChecker_Env.failhard =
                     (uu___400_9661.FStar_TypeChecker_Env.failhard);
                   FStar_TypeChecker_Env.nosynth =
                     (uu___400_9661.FStar_TypeChecker_Env.nosynth);
                   FStar_TypeChecker_Env.uvar_subtyping =
                     (uu___400_9661.FStar_TypeChecker_Env.uvar_subtyping);
                   FStar_TypeChecker_Env.tc_term =
                     (uu___400_9661.FStar_TypeChecker_Env.tc_term);
                   FStar_TypeChecker_Env.type_of =
                     (uu___400_9661.FStar_TypeChecker_Env.type_of);
                   FStar_TypeChecker_Env.universe_of =
                     (uu___400_9661.FStar_TypeChecker_Env.universe_of);
                   FStar_TypeChecker_Env.check_type_of =
                     (uu___400_9661.FStar_TypeChecker_Env.check_type_of);
                   FStar_TypeChecker_Env.use_bv_sorts =
                     (uu___400_9661.FStar_TypeChecker_Env.use_bv_sorts);
                   FStar_TypeChecker_Env.qtbl_name_and_index =
                     (uu___400_9661.FStar_TypeChecker_Env.qtbl_name_and_index);
                   FStar_TypeChecker_Env.normalized_eff_names =
                     (uu___400_9661.FStar_TypeChecker_Env.normalized_eff_names);
                   FStar_TypeChecker_Env.proof_ns =
                     (uu___400_9661.FStar_TypeChecker_Env.proof_ns);
                   FStar_TypeChecker_Env.synth_hook =
                     (uu___400_9661.FStar_TypeChecker_Env.synth_hook);
                   FStar_TypeChecker_Env.splice =
                     (uu___400_9661.FStar_TypeChecker_Env.splice);
                   FStar_TypeChecker_Env.is_native_tactic =
                     (uu___400_9661.FStar_TypeChecker_Env.is_native_tactic);
                   FStar_TypeChecker_Env.identifier_info =
                     (uu___400_9661.FStar_TypeChecker_Env.identifier_info);
                   FStar_TypeChecker_Env.tc_hooks =
                     (uu___400_9661.FStar_TypeChecker_Env.tc_hooks);
                   FStar_TypeChecker_Env.dsenv =
                     (uu___400_9661.FStar_TypeChecker_Env.dsenv);
                   FStar_TypeChecker_Env.dep_graph =
                     (uu___400_9661.FStar_TypeChecker_Env.dep_graph)
                 }  in
               let g = FStar_Tactics_Types.mk_goal env1 ctx_uvar opts false
                  in
               let uu____9663 =
                 let uu____9666 = bnorm_goal g  in [uu____9666]  in
               add_goals uu____9663
           | uu____9667 -> fail "not a uvar")
       in
    FStar_All.pipe_left (wrap_err "unshelve") uu____9577
  
let (tac_and : Prims.bool tac -> Prims.bool tac -> Prims.bool tac) =
  fun t1  ->
    fun t2  ->
      let comp =
        bind t1
          (fun b  ->
             let uu____9714 = if b then t2 else ret false  in
             bind uu____9714 (fun b'  -> if b' then ret b' else fail ""))
         in
      let uu____9725 = trytac comp  in
      bind uu____9725
        (fun uu___342_9733  ->
           match uu___342_9733 with
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
        let uu____9759 =
          bind get
            (fun ps  ->
               let uu____9765 = __tc e t1  in
               bind uu____9765
                 (fun uu____9785  ->
                    match uu____9785 with
                    | (t11,ty1,g1) ->
                        let uu____9797 = __tc e t2  in
                        bind uu____9797
                          (fun uu____9817  ->
                             match uu____9817 with
                             | (t21,ty2,g2) ->
                                 let uu____9829 =
                                   proc_guard "unify_env g1" e g1  in
                                 bind uu____9829
                                   (fun uu____9834  ->
                                      let uu____9835 =
                                        proc_guard "unify_env g2" e g2  in
                                      bind uu____9835
                                        (fun uu____9841  ->
                                           let uu____9842 =
                                             do_unify e ty1 ty2  in
                                           let uu____9845 =
                                             do_unify e t11 t21  in
                                           tac_and uu____9842 uu____9845)))))
           in
        FStar_All.pipe_left (wrap_err "unify_env") uu____9759
  
let (launch_process :
  Prims.string -> Prims.string Prims.list -> Prims.string -> Prims.string tac)
  =
  fun prog  ->
    fun args  ->
      fun input  ->
        bind idtac
          (fun uu____9878  ->
             let uu____9879 = FStar_Options.unsafe_tactic_exec ()  in
             if uu____9879
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
        (fun uu____9900  ->
           let uu____9901 =
             FStar_Syntax_Syntax.gen_bv nm FStar_Pervasives_Native.None t  in
           ret uu____9901)
  
let (change : FStar_Reflection_Data.typ -> unit tac) =
  fun ty  ->
    let uu____9911 =
      mlog
        (fun uu____9916  ->
           let uu____9917 = FStar_Syntax_Print.term_to_string ty  in
           FStar_Util.print1 "change: ty = %s\n" uu____9917)
        (fun uu____9920  ->
           let uu____9921 = cur_goal ()  in
           bind uu____9921
             (fun g  ->
                let uu____9927 =
                  let uu____9936 = FStar_Tactics_Types.goal_env g  in
                  __tc uu____9936 ty  in
                bind uu____9927
                  (fun uu____9948  ->
                     match uu____9948 with
                     | (ty1,uu____9958,guard) ->
                         let uu____9960 =
                           let uu____9963 = FStar_Tactics_Types.goal_env g
                              in
                           proc_guard "change" uu____9963 guard  in
                         bind uu____9960
                           (fun uu____9966  ->
                              let uu____9967 =
                                let uu____9970 =
                                  FStar_Tactics_Types.goal_env g  in
                                let uu____9971 =
                                  FStar_Tactics_Types.goal_type g  in
                                do_unify uu____9970 uu____9971 ty1  in
                              bind uu____9967
                                (fun bb  ->
                                   if bb
                                   then
                                     let uu____9977 =
                                       FStar_Tactics_Types.goal_with_type g
                                         ty1
                                        in
                                     replace_cur uu____9977
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
                                        let uu____9983 =
                                          FStar_Tactics_Types.goal_env g  in
                                        let uu____9984 =
                                          FStar_Tactics_Types.goal_type g  in
                                        normalize steps uu____9983 uu____9984
                                         in
                                      let nty =
                                        let uu____9986 =
                                          FStar_Tactics_Types.goal_env g  in
                                        normalize steps uu____9986 ty1  in
                                      let uu____9987 =
                                        let uu____9990 =
                                          FStar_Tactics_Types.goal_env g  in
                                        do_unify uu____9990 ng nty  in
                                      bind uu____9987
                                        (fun b  ->
                                           if b
                                           then
                                             let uu____9996 =
                                               FStar_Tactics_Types.goal_with_type
                                                 g ty1
                                                in
                                             replace_cur uu____9996
                                           else fail "not convertible")))))))
       in
    FStar_All.pipe_left (wrap_err "change") uu____9911
  
let rec last : 'a . 'a Prims.list -> 'a =
  fun l  ->
    match l with
    | [] -> failwith "last: empty list"
    | x::[] -> x
    | uu____10018::xs -> last xs
  
let rec init : 'a . 'a Prims.list -> 'a Prims.list =
  fun l  ->
    match l with
    | [] -> failwith "init: empty list"
    | x::[] -> []
    | x::xs -> let uu____10046 = init xs  in x :: uu____10046
  
let rec (inspect :
  FStar_Syntax_Syntax.term -> FStar_Reflection_Data.term_view tac) =
  fun t  ->
    let uu____10058 =
      let t1 = FStar_Syntax_Util.unascribe t  in
      let t2 = FStar_Syntax_Util.un_uinst t1  in
      match t2.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_meta (t3,uu____10066) -> inspect t3
      | FStar_Syntax_Syntax.Tm_name bv ->
          FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_Var bv)
      | FStar_Syntax_Syntax.Tm_bvar bv ->
          FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_BVar bv)
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_FVar fv)
      | FStar_Syntax_Syntax.Tm_app (hd1,[]) ->
          failwith "empty arguments on Tm_app"
      | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
          let uu____10123 = last args  in
          (match uu____10123 with
           | (a,q) ->
               let q' = FStar_Reflection_Basic.inspect_aqual q  in
               let uu____10145 =
                 let uu____10146 =
                   let uu____10151 =
                     let uu____10152 =
                       let uu____10157 = init args  in
                       FStar_Syntax_Syntax.mk_Tm_app hd1 uu____10157  in
                     uu____10152 FStar_Pervasives_Native.None
                       t2.FStar_Syntax_Syntax.pos
                      in
                   (uu____10151, (a, q'))  in
                 FStar_Reflection_Data.Tv_App uu____10146  in
               FStar_All.pipe_left ret uu____10145)
      | FStar_Syntax_Syntax.Tm_abs ([],uu____10168,uu____10169) ->
          failwith "empty arguments on Tm_abs"
      | FStar_Syntax_Syntax.Tm_abs (bs,t3,k) ->
          let uu____10213 = FStar_Syntax_Subst.open_term bs t3  in
          (match uu____10213 with
           | (bs1,t4) ->
               (match bs1 with
                | [] -> failwith "impossible"
                | b::bs2 ->
                    let uu____10246 =
                      let uu____10247 =
                        let uu____10252 = FStar_Syntax_Util.abs bs2 t4 k  in
                        (b, uu____10252)  in
                      FStar_Reflection_Data.Tv_Abs uu____10247  in
                    FStar_All.pipe_left ret uu____10246))
      | FStar_Syntax_Syntax.Tm_type uu____10255 ->
          FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_Type ())
      | FStar_Syntax_Syntax.Tm_arrow ([],k) ->
          failwith "empty binders on arrow"
      | FStar_Syntax_Syntax.Tm_arrow uu____10275 ->
          let uu____10288 = FStar_Syntax_Util.arrow_one t2  in
          (match uu____10288 with
           | FStar_Pervasives_Native.Some (b,c) ->
               FStar_All.pipe_left ret
                 (FStar_Reflection_Data.Tv_Arrow (b, c))
           | FStar_Pervasives_Native.None  -> failwith "impossible")
      | FStar_Syntax_Syntax.Tm_refine (bv,t3) ->
          let b = FStar_Syntax_Syntax.mk_binder bv  in
          let uu____10318 = FStar_Syntax_Subst.open_term [b] t3  in
          (match uu____10318 with
           | (b',t4) ->
               let b1 =
                 match b' with
                 | b'1::[] -> b'1
                 | uu____10357 -> failwith "impossible"  in
               FStar_All.pipe_left ret
                 (FStar_Reflection_Data.Tv_Refine
                    ((FStar_Pervasives_Native.fst b1), t4)))
      | FStar_Syntax_Syntax.Tm_constant c ->
          let uu____10365 =
            let uu____10366 = FStar_Reflection_Basic.inspect_const c  in
            FStar_Reflection_Data.Tv_Const uu____10366  in
          FStar_All.pipe_left ret uu____10365
      | FStar_Syntax_Syntax.Tm_uvar (ctx_u,s) ->
          let uu____10387 =
            let uu____10388 =
              let uu____10393 =
                let uu____10394 =
                  FStar_Syntax_Unionfind.uvar_id
                    ctx_u.FStar_Syntax_Syntax.ctx_uvar_head
                   in
                FStar_BigInt.of_int_fs uu____10394  in
              (uu____10393, (ctx_u, s))  in
            FStar_Reflection_Data.Tv_Uvar uu____10388  in
          FStar_All.pipe_left ret uu____10387
      | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),t21) ->
          if lb.FStar_Syntax_Syntax.lbunivs <> []
          then FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown
          else
            (match lb.FStar_Syntax_Syntax.lbname with
             | FStar_Util.Inr uu____10428 ->
                 FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown
             | FStar_Util.Inl bv ->
                 let b = FStar_Syntax_Syntax.mk_binder bv  in
                 let uu____10433 = FStar_Syntax_Subst.open_term [b] t21  in
                 (match uu____10433 with
                  | (bs,t22) ->
                      let b1 =
                        match bs with
                        | b1::[] -> b1
                        | uu____10472 ->
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
             | FStar_Util.Inr uu____10502 ->
                 FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown
             | FStar_Util.Inl bv ->
                 let uu____10506 = FStar_Syntax_Subst.open_let_rec [lb] t21
                    in
                 (match uu____10506 with
                  | (lbs,t22) ->
                      (match lbs with
                       | lb1::[] ->
                           (match lb1.FStar_Syntax_Syntax.lbname with
                            | FStar_Util.Inr uu____10526 ->
                                ret FStar_Reflection_Data.Tv_Unknown
                            | FStar_Util.Inl bv1 ->
                                FStar_All.pipe_left ret
                                  (FStar_Reflection_Data.Tv_Let
                                     (true, bv1,
                                       (lb1.FStar_Syntax_Syntax.lbdef), t22)))
                       | uu____10530 ->
                           failwith
                             "impossible: open_term returned different amount of binders")))
      | FStar_Syntax_Syntax.Tm_match (t3,brs) ->
          let rec inspect_pat p =
            match p.FStar_Syntax_Syntax.v with
            | FStar_Syntax_Syntax.Pat_constant c ->
                let uu____10584 = FStar_Reflection_Basic.inspect_const c  in
                FStar_Reflection_Data.Pat_Constant uu____10584
            | FStar_Syntax_Syntax.Pat_cons (fv,ps) ->
                let uu____10603 =
                  let uu____10610 =
                    FStar_List.map
                      (fun uu____10622  ->
                         match uu____10622 with
                         | (p1,uu____10630) -> inspect_pat p1) ps
                     in
                  (fv, uu____10610)  in
                FStar_Reflection_Data.Pat_Cons uu____10603
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
              (fun uu___343_10724  ->
                 match uu___343_10724 with
                 | (pat,uu____10746,t4) ->
                     let uu____10764 = inspect_pat pat  in (uu____10764, t4))
              brs1
             in
          FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_Match (t3, brs2))
      | FStar_Syntax_Syntax.Tm_unknown  ->
          FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown
      | uu____10773 ->
          ((let uu____10775 =
              let uu____10780 =
                let uu____10781 = FStar_Syntax_Print.tag_of_term t2  in
                let uu____10782 = FStar_Syntax_Print.term_to_string t2  in
                FStar_Util.format2
                  "inspect: outside of expected syntax (%s, %s)\n"
                  uu____10781 uu____10782
                 in
              (FStar_Errors.Warning_CantInspect, uu____10780)  in
            FStar_Errors.log_issue t2.FStar_Syntax_Syntax.pos uu____10775);
           FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown)
       in
    wrap_err "inspect" uu____10058
  
let (pack : FStar_Reflection_Data.term_view -> FStar_Syntax_Syntax.term tac)
  =
  fun tv  ->
    match tv with
    | FStar_Reflection_Data.Tv_Var bv ->
        let uu____10795 = FStar_Syntax_Syntax.bv_to_name bv  in
        FStar_All.pipe_left ret uu____10795
    | FStar_Reflection_Data.Tv_BVar bv ->
        let uu____10799 = FStar_Syntax_Syntax.bv_to_tm bv  in
        FStar_All.pipe_left ret uu____10799
    | FStar_Reflection_Data.Tv_FVar fv ->
        let uu____10803 = FStar_Syntax_Syntax.fv_to_tm fv  in
        FStar_All.pipe_left ret uu____10803
    | FStar_Reflection_Data.Tv_App (l,(r,q)) ->
        let q' = FStar_Reflection_Basic.pack_aqual q  in
        let uu____10810 = FStar_Syntax_Util.mk_app l [(r, q')]  in
        FStar_All.pipe_left ret uu____10810
    | FStar_Reflection_Data.Tv_Abs (b,t) ->
        let uu____10829 =
          FStar_Syntax_Util.abs [b] t FStar_Pervasives_Native.None  in
        FStar_All.pipe_left ret uu____10829
    | FStar_Reflection_Data.Tv_Arrow (b,c) ->
        let uu____10842 = FStar_Syntax_Util.arrow [b] c  in
        FStar_All.pipe_left ret uu____10842
    | FStar_Reflection_Data.Tv_Type () ->
        FStar_All.pipe_left ret FStar_Syntax_Util.ktype
    | FStar_Reflection_Data.Tv_Refine (bv,t) ->
        let uu____10857 = FStar_Syntax_Util.refine bv t  in
        FStar_All.pipe_left ret uu____10857
    | FStar_Reflection_Data.Tv_Const c ->
        let uu____10861 =
          let uu____10862 =
            let uu____10869 =
              let uu____10870 = FStar_Reflection_Basic.pack_const c  in
              FStar_Syntax_Syntax.Tm_constant uu____10870  in
            FStar_Syntax_Syntax.mk uu____10869  in
          uu____10862 FStar_Pervasives_Native.None FStar_Range.dummyRange  in
        FStar_All.pipe_left ret uu____10861
    | FStar_Reflection_Data.Tv_Uvar (_u,ctx_u_s) ->
        let uu____10878 =
          FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_uvar ctx_u_s)
            FStar_Pervasives_Native.None FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____10878
    | FStar_Reflection_Data.Tv_Let (false ,bv,t1,t2) ->
        let lb =
          FStar_Syntax_Util.mk_letbinding (FStar_Util.Inl bv) []
            bv.FStar_Syntax_Syntax.sort FStar_Parser_Const.effect_Tot_lid t1
            [] FStar_Range.dummyRange
           in
        let uu____10887 =
          let uu____10888 =
            let uu____10895 =
              let uu____10896 =
                let uu____10909 =
                  let uu____10912 =
                    let uu____10913 = FStar_Syntax_Syntax.mk_binder bv  in
                    [uu____10913]  in
                  FStar_Syntax_Subst.close uu____10912 t2  in
                ((false, [lb]), uu____10909)  in
              FStar_Syntax_Syntax.Tm_let uu____10896  in
            FStar_Syntax_Syntax.mk uu____10895  in
          uu____10888 FStar_Pervasives_Native.None FStar_Range.dummyRange  in
        FStar_All.pipe_left ret uu____10887
    | FStar_Reflection_Data.Tv_Let (true ,bv,t1,t2) ->
        let lb =
          FStar_Syntax_Util.mk_letbinding (FStar_Util.Inl bv) []
            bv.FStar_Syntax_Syntax.sort FStar_Parser_Const.effect_Tot_lid t1
            [] FStar_Range.dummyRange
           in
        let uu____10947 = FStar_Syntax_Subst.close_let_rec [lb] t2  in
        (match uu____10947 with
         | (lbs,body) ->
             let uu____10962 =
               FStar_Syntax_Syntax.mk
                 (FStar_Syntax_Syntax.Tm_let ((true, lbs), body))
                 FStar_Pervasives_Native.None FStar_Range.dummyRange
                in
             FStar_All.pipe_left ret uu____10962)
    | FStar_Reflection_Data.Tv_Match (t,brs) ->
        let wrap v1 =
          {
            FStar_Syntax_Syntax.v = v1;
            FStar_Syntax_Syntax.p = FStar_Range.dummyRange
          }  in
        let rec pack_pat p =
          match p with
          | FStar_Reflection_Data.Pat_Constant c ->
              let uu____10996 =
                let uu____10997 = FStar_Reflection_Basic.pack_const c  in
                FStar_Syntax_Syntax.Pat_constant uu____10997  in
              FStar_All.pipe_left wrap uu____10996
          | FStar_Reflection_Data.Pat_Cons (fv,ps) ->
              let uu____11004 =
                let uu____11005 =
                  let uu____11018 =
                    FStar_List.map
                      (fun p1  ->
                         let uu____11034 = pack_pat p1  in
                         (uu____11034, false)) ps
                     in
                  (fv, uu____11018)  in
                FStar_Syntax_Syntax.Pat_cons uu____11005  in
              FStar_All.pipe_left wrap uu____11004
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
            (fun uu___344_11080  ->
               match uu___344_11080 with
               | (pat,t1) ->
                   let uu____11097 = pack_pat pat  in
                   (uu____11097, FStar_Pervasives_Native.None, t1)) brs
           in
        let brs2 = FStar_List.map FStar_Syntax_Subst.close_branch brs1  in
        let uu____11145 =
          FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_match (t, brs2))
            FStar_Pervasives_Native.None FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____11145
    | FStar_Reflection_Data.Tv_AscribedT (e,t,tacopt) ->
        let uu____11173 =
          FStar_Syntax_Syntax.mk
            (FStar_Syntax_Syntax.Tm_ascribed
               (e, ((FStar_Util.Inl t), tacopt),
                 FStar_Pervasives_Native.None)) FStar_Pervasives_Native.None
            FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____11173
    | FStar_Reflection_Data.Tv_AscribedC (e,c,tacopt) ->
        let uu____11219 =
          FStar_Syntax_Syntax.mk
            (FStar_Syntax_Syntax.Tm_ascribed
               (e, ((FStar_Util.Inr c), tacopt),
                 FStar_Pervasives_Native.None)) FStar_Pervasives_Native.None
            FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____11219
    | FStar_Reflection_Data.Tv_Unknown  ->
        let uu____11258 =
          FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown
            FStar_Pervasives_Native.None FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____11258
  
let (goal_of_goal_ty :
  env ->
    FStar_Reflection_Data.typ ->
      (FStar_Tactics_Types.goal,FStar_TypeChecker_Env.guard_t)
        FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun typ  ->
      let uu____11279 =
        FStar_TypeChecker_Util.new_implicit_var "proofstate_of_goal_ty"
          typ.FStar_Syntax_Syntax.pos env typ
         in
      match uu____11279 with
      | (u,ctx_uvars,g_u) ->
          let uu____11311 = FStar_List.hd ctx_uvars  in
          (match uu____11311 with
           | (ctx_uvar,uu____11325) ->
               let g =
                 let uu____11327 = FStar_Options.peek ()  in
                 FStar_Tactics_Types.mk_goal env ctx_uvar uu____11327 false
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
        let uu____11347 = goal_of_goal_ty env typ  in
        match uu____11347 with
        | (g,g_u) ->
            let ps =
              let uu____11359 =
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
                FStar_Tactics_Types.tac_verb_dbg = uu____11359
              }  in
            let uu____11364 = FStar_Tactics_Types.goal_witness g  in
            (ps, uu____11364)
  