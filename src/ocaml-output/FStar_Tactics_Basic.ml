open Prims
type goal = FStar_Tactics_Types.goal[@@deriving show]
type name = FStar_Syntax_Syntax.bv[@@deriving show]
type env = FStar_TypeChecker_Env.env[@@deriving show]
type implicits = FStar_TypeChecker_Env.implicits[@@deriving show]
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
type 'a tac =
  {
  tac_f: FStar_Tactics_Types.proofstate -> 'a FStar_Tactics_Result.__result }
[@@deriving show]
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
let ret : 'a . 'a -> 'a tac =
  fun x  -> mk_tac (fun p  -> FStar_Tactics_Result.Success (x, p)) 
let bind : 'a 'b . 'a tac -> ('a -> 'b tac) -> 'b tac =
  fun t1  ->
    fun t2  ->
      mk_tac
        (fun p  ->
           let uu____140 = run t1 p  in
           match uu____140 with
           | FStar_Tactics_Result.Success (a,q) ->
               let uu____147 = t2 a  in run uu____147 q
           | FStar_Tactics_Result.Failed (msg,q) ->
               FStar_Tactics_Result.Failed (msg, q))
  
let (get : FStar_Tactics_Types.proofstate tac) =
  mk_tac (fun p  -> FStar_Tactics_Result.Success (p, p)) 
let (idtac : Prims.unit tac) = ret () 
let (goal_to_string : FStar_Tactics_Types.goal -> Prims.string) =
  fun g  ->
    let g_binders =
      let uu____164 =
        FStar_TypeChecker_Env.all_binders g.FStar_Tactics_Types.context  in
      FStar_All.pipe_right uu____164
        (FStar_Syntax_Print.binders_to_string ", ")
       in
    let w = bnorm g.FStar_Tactics_Types.context g.FStar_Tactics_Types.witness
       in
    let t = bnorm g.FStar_Tactics_Types.context g.FStar_Tactics_Types.goal_ty
       in
    let uu____167 = tts g.FStar_Tactics_Types.context w  in
    let uu____168 = tts g.FStar_Tactics_Types.context t  in
    FStar_Util.format3 "%s |- %s : %s" g_binders uu____167 uu____168
  
let (tacprint : Prims.string -> Prims.unit) =
  fun s  -> FStar_Util.print1 "TAC>> %s\n" s 
let (tacprint1 : Prims.string -> Prims.string -> Prims.unit) =
  fun s  ->
    fun x  ->
      let uu____178 = FStar_Util.format1 s x  in
      FStar_Util.print1 "TAC>> %s\n" uu____178
  
let (tacprint2 : Prims.string -> Prims.string -> Prims.string -> Prims.unit)
  =
  fun s  ->
    fun x  ->
      fun y  ->
        let uu____188 = FStar_Util.format2 s x y  in
        FStar_Util.print1 "TAC>> %s\n" uu____188
  
let (tacprint3 :
  Prims.string -> Prims.string -> Prims.string -> Prims.string -> Prims.unit)
  =
  fun s  ->
    fun x  ->
      fun y  ->
        fun z  ->
          let uu____201 = FStar_Util.format3 s x y z  in
          FStar_Util.print1 "TAC>> %s\n" uu____201
  
let (comp_to_typ : FStar_Syntax_Syntax.comp -> FStar_Reflection_Data.typ) =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Total (t,uu____206) -> t
    | FStar_Syntax_Syntax.GTotal (t,uu____216) -> t
    | FStar_Syntax_Syntax.Comp ct -> ct.FStar_Syntax_Syntax.result_typ
  
let (is_irrelevant : FStar_Tactics_Types.goal -> Prims.bool) =
  fun g  ->
    let uu____229 =
      let uu____234 =
        FStar_TypeChecker_Normalize.unfold_whnf g.FStar_Tactics_Types.context
          g.FStar_Tactics_Types.goal_ty
         in
      FStar_Syntax_Util.un_squash uu____234  in
    match uu____229 with
    | FStar_Pervasives_Native.Some t -> true
    | uu____240 -> false
  
let (print : Prims.string -> Prims.unit tac) =
  fun msg  -> tacprint msg; ret () 
let (debug : Prims.string -> Prims.unit tac) =
  fun msg  ->
    bind get
      (fun ps  ->
         (let uu____264 =
            let uu____265 =
              FStar_Ident.string_of_lid
                (ps.FStar_Tactics_Types.main_context).FStar_TypeChecker_Env.curmodule
               in
            FStar_Options.debug_module uu____265  in
          if uu____264 then tacprint msg else ());
         ret ())
  
let dump_goal :
  'Auu____270 . 'Auu____270 -> FStar_Tactics_Types.goal -> Prims.unit =
  fun ps  ->
    fun goal  -> let uu____280 = goal_to_string goal  in tacprint uu____280
  
let (dump_cur : FStar_Tactics_Types.proofstate -> Prims.string -> Prims.unit)
  =
  fun ps  ->
    fun msg  ->
      match ps.FStar_Tactics_Types.goals with
      | [] -> tacprint1 "No more goals (%s)" msg
      | h::uu____288 ->
          (tacprint1 "Current goal (%s):" msg;
           (let uu____292 = FStar_List.hd ps.FStar_Tactics_Types.goals  in
            dump_goal ps uu____292))
  
let (ps_to_string :
  (Prims.string,FStar_Tactics_Types.proofstate)
    FStar_Pervasives_Native.tuple2 -> Prims.string)
  =
  fun uu____299  ->
    match uu____299 with
    | (msg,ps) ->
        let uu____306 =
          let uu____309 =
            let uu____310 =
              FStar_Util.string_of_int ps.FStar_Tactics_Types.depth  in
            FStar_Util.format2 "State dump @ depth %s (%s):\n" uu____310 msg
             in
          let uu____311 =
            let uu____314 =
              let uu____315 =
                FStar_Range.string_of_range
                  ps.FStar_Tactics_Types.entry_range
                 in
              FStar_Util.format1 "Location: %s\n" uu____315  in
            let uu____316 =
              let uu____319 =
                let uu____320 =
                  FStar_Util.string_of_int
                    (FStar_List.length ps.FStar_Tactics_Types.goals)
                   in
                let uu____321 =
                  let uu____322 =
                    FStar_List.map goal_to_string
                      ps.FStar_Tactics_Types.goals
                     in
                  FStar_String.concat "\n" uu____322  in
                FStar_Util.format2 "ACTIVE goals (%s):\n%s\n" uu____320
                  uu____321
                 in
              let uu____325 =
                let uu____328 =
                  let uu____329 =
                    FStar_Util.string_of_int
                      (FStar_List.length ps.FStar_Tactics_Types.smt_goals)
                     in
                  let uu____330 =
                    let uu____331 =
                      FStar_List.map goal_to_string
                        ps.FStar_Tactics_Types.smt_goals
                       in
                    FStar_String.concat "\n" uu____331  in
                  FStar_Util.format2 "SMT goals (%s):\n%s\n" uu____329
                    uu____330
                   in
                [uu____328]  in
              uu____319 :: uu____325  in
            uu____314 :: uu____316  in
          uu____309 :: uu____311  in
        FStar_String.concat "" uu____306
  
let (goal_to_json : FStar_Tactics_Types.goal -> FStar_Util.json) =
  fun g  ->
    let g_binders =
      let uu____338 =
        FStar_TypeChecker_Env.all_binders g.FStar_Tactics_Types.context  in
      let uu____339 =
        let uu____342 =
          FStar_TypeChecker_Env.dsenv g.FStar_Tactics_Types.context  in
        FStar_Syntax_Print.binders_to_json uu____342  in
      FStar_All.pipe_right uu____338 uu____339  in
    let uu____343 =
      let uu____350 =
        let uu____357 =
          let uu____362 =
            let uu____363 =
              let uu____370 =
                let uu____375 =
                  let uu____376 =
                    tts g.FStar_Tactics_Types.context
                      g.FStar_Tactics_Types.witness
                     in
                  FStar_Util.JsonStr uu____376  in
                ("witness", uu____375)  in
              let uu____377 =
                let uu____384 =
                  let uu____389 =
                    let uu____390 =
                      tts g.FStar_Tactics_Types.context
                        g.FStar_Tactics_Types.goal_ty
                       in
                    FStar_Util.JsonStr uu____390  in
                  ("type", uu____389)  in
                [uu____384]  in
              uu____370 :: uu____377  in
            FStar_Util.JsonAssoc uu____363  in
          ("goal", uu____362)  in
        [uu____357]  in
      ("hyps", g_binders) :: uu____350  in
    FStar_Util.JsonAssoc uu____343
  
let (ps_to_json :
  (Prims.string,FStar_Tactics_Types.proofstate)
    FStar_Pervasives_Native.tuple2 -> FStar_Util.json)
  =
  fun uu____421  ->
    match uu____421 with
    | (msg,ps) ->
        let uu____428 =
          let uu____435 =
            let uu____442 =
              let uu____449 =
                let uu____456 =
                  let uu____461 =
                    let uu____462 =
                      FStar_List.map goal_to_json
                        ps.FStar_Tactics_Types.goals
                       in
                    FStar_Util.JsonList uu____462  in
                  ("goals", uu____461)  in
                let uu____465 =
                  let uu____472 =
                    let uu____477 =
                      let uu____478 =
                        FStar_List.map goal_to_json
                          ps.FStar_Tactics_Types.smt_goals
                         in
                      FStar_Util.JsonList uu____478  in
                    ("smt-goals", uu____477)  in
                  [uu____472]  in
                uu____456 :: uu____465  in
              ("depth", (FStar_Util.JsonInt (ps.FStar_Tactics_Types.depth)))
                :: uu____449
               in
            ("label", (FStar_Util.JsonStr msg)) :: uu____442  in
          let uu____501 =
            if ps.FStar_Tactics_Types.entry_range <> FStar_Range.dummyRange
            then
              let uu____514 =
                let uu____519 =
                  FStar_Range.json_of_def_range
                    ps.FStar_Tactics_Types.entry_range
                   in
                ("location", uu____519)  in
              [uu____514]
            else []  in
          FStar_List.append uu____435 uu____501  in
        FStar_Util.JsonAssoc uu____428
  
let (dump_proofstate :
  FStar_Tactics_Types.proofstate -> Prims.string -> Prims.unit) =
  fun ps  ->
    fun msg  ->
      FStar_Options.with_saved_options
        (fun uu____545  ->
           FStar_Options.set_option "print_effect_args"
             (FStar_Options.Bool true);
           FStar_Util.print_generic "proof-state" ps_to_string ps_to_json
             (msg, ps))
  
let (print_proof_state1 : Prims.string -> Prims.unit tac) =
  fun msg  ->
    mk_tac
      (fun ps  ->
         let psc = ps.FStar_Tactics_Types.psc  in
         let subst1 = FStar_TypeChecker_Normalize.psc_subst psc  in
         (let uu____566 = FStar_Tactics_Types.subst_proof_state subst1 ps  in
          dump_cur uu____566 msg);
         FStar_Tactics_Result.Success ((), ps))
  
let (print_proof_state : Prims.string -> Prims.unit tac) =
  fun msg  ->
    mk_tac
      (fun ps  ->
         let psc = ps.FStar_Tactics_Types.psc  in
         let subst1 = FStar_TypeChecker_Normalize.psc_subst psc  in
         (let uu____582 = FStar_Tactics_Types.subst_proof_state subst1 ps  in
          dump_proofstate uu____582 msg);
         FStar_Tactics_Result.Success ((), ps))
  
let (tac_verb_dbg : Prims.bool FStar_Pervasives_Native.option FStar_ST.ref) =
  FStar_Util.mk_ref FStar_Pervasives_Native.None 
let rec (log :
  FStar_Tactics_Types.proofstate -> (Prims.unit -> Prims.unit) -> Prims.unit)
  =
  fun ps  ->
    fun f  ->
      let uu____611 = FStar_ST.op_Bang tac_verb_dbg  in
      match uu____611 with
      | FStar_Pervasives_Native.None  ->
          ((let uu____638 =
              let uu____641 =
                FStar_TypeChecker_Env.debug
                  ps.FStar_Tactics_Types.main_context
                  (FStar_Options.Other "TacVerbose")
                 in
              FStar_Pervasives_Native.Some uu____641  in
            FStar_ST.op_Colon_Equals tac_verb_dbg uu____638);
           log ps f)
      | FStar_Pervasives_Native.Some (true ) -> f ()
      | FStar_Pervasives_Native.Some (false ) -> ()
  
let mlog :
  'a . (Prims.unit -> Prims.unit) -> (Prims.unit -> 'a tac) -> 'a tac =
  fun f  -> fun cont  -> bind get (fun ps  -> log ps f; cont ()) 
let fail : 'a . Prims.string -> 'a tac =
  fun msg  ->
    mk_tac
      (fun ps  ->
         (let uu____710 =
            FStar_TypeChecker_Env.debug ps.FStar_Tactics_Types.main_context
              (FStar_Options.Other "TacFail")
             in
          if uu____710
          then dump_proofstate ps (Prims.strcat "TACTIC FAILING: " msg)
          else ());
         FStar_Tactics_Result.Failed (msg, ps))
  
let fail1 : 'Auu____715 . Prims.string -> Prims.string -> 'Auu____715 tac =
  fun msg  ->
    fun x  -> let uu____726 = FStar_Util.format1 msg x  in fail uu____726
  
let fail2 :
  'Auu____731 .
    Prims.string -> Prims.string -> Prims.string -> 'Auu____731 tac
  =
  fun msg  ->
    fun x  ->
      fun y  -> let uu____746 = FStar_Util.format2 msg x y  in fail uu____746
  
let fail3 :
  'Auu____752 .
    Prims.string ->
      Prims.string -> Prims.string -> Prims.string -> 'Auu____752 tac
  =
  fun msg  ->
    fun x  ->
      fun y  ->
        fun z  ->
          let uu____771 = FStar_Util.format3 msg x y z  in fail uu____771
  
let fail4 :
  'Auu____778 .
    Prims.string ->
      Prims.string ->
        Prims.string -> Prims.string -> Prims.string -> 'Auu____778 tac
  =
  fun msg  ->
    fun x  ->
      fun y  ->
        fun z  ->
          fun w  ->
            let uu____801 = FStar_Util.format4 msg x y z w  in fail uu____801
  
let trytac' : 'a . 'a tac -> (Prims.string,'a) FStar_Util.either tac =
  fun t  ->
    mk_tac
      (fun ps  ->
         let tx = FStar_Syntax_Unionfind.new_transaction ()  in
         let uu____831 = run t ps  in
         match uu____831 with
         | FStar_Tactics_Result.Success (a,q) ->
             (FStar_Syntax_Unionfind.commit tx;
              FStar_Tactics_Result.Success ((FStar_Util.Inr a), q))
         | FStar_Tactics_Result.Failed (m,q) ->
             (FStar_Syntax_Unionfind.rollback tx;
              (let ps1 =
                 let uu___65_855 = ps  in
                 {
                   FStar_Tactics_Types.main_context =
                     (uu___65_855.FStar_Tactics_Types.main_context);
                   FStar_Tactics_Types.main_goal =
                     (uu___65_855.FStar_Tactics_Types.main_goal);
                   FStar_Tactics_Types.all_implicits =
                     (uu___65_855.FStar_Tactics_Types.all_implicits);
                   FStar_Tactics_Types.goals =
                     (uu___65_855.FStar_Tactics_Types.goals);
                   FStar_Tactics_Types.smt_goals =
                     (uu___65_855.FStar_Tactics_Types.smt_goals);
                   FStar_Tactics_Types.depth =
                     (uu___65_855.FStar_Tactics_Types.depth);
                   FStar_Tactics_Types.__dump =
                     (uu___65_855.FStar_Tactics_Types.__dump);
                   FStar_Tactics_Types.psc =
                     (uu___65_855.FStar_Tactics_Types.psc);
                   FStar_Tactics_Types.entry_range =
                     (uu___65_855.FStar_Tactics_Types.entry_range);
                   FStar_Tactics_Types.guard_policy =
                     (uu___65_855.FStar_Tactics_Types.guard_policy);
                   FStar_Tactics_Types.freshness =
                     (q.FStar_Tactics_Types.freshness)
                 }  in
               FStar_Tactics_Result.Success ((FStar_Util.Inl m), ps1))))
  
let trytac : 'a . 'a tac -> 'a FStar_Pervasives_Native.option tac =
  fun t  ->
    let uu____879 = trytac' t  in
    bind uu____879
      (fun r  ->
         match r with
         | FStar_Util.Inr v1 -> ret (FStar_Pervasives_Native.Some v1)
         | FStar_Util.Inl uu____906 -> ret FStar_Pervasives_Native.None)
  
let trytac_exn : 'a . 'a tac -> 'a FStar_Pervasives_Native.option tac =
  fun t  ->
    mk_tac
      (fun ps  ->
         try let uu____939 = trytac t  in run uu____939 ps
         with
         | FStar_Errors.Err (uu____955,msg) ->
             (log ps
                (fun uu____959  ->
                   FStar_Util.print1 "trytac_exn error: (%s)" msg);
              FStar_Tactics_Result.Success (FStar_Pervasives_Native.None, ps))
         | FStar_Errors.Error (uu____964,msg,uu____966) ->
             (log ps
                (fun uu____969  ->
                   FStar_Util.print1 "trytac_exn error: (%s)" msg);
              FStar_Tactics_Result.Success (FStar_Pervasives_Native.None, ps)))
  
let wrap_err : 'a . Prims.string -> 'a tac -> 'a tac =
  fun pref  ->
    fun t  ->
      mk_tac
        (fun ps  ->
           let uu____997 = run t ps  in
           match uu____997 with
           | FStar_Tactics_Result.Success (a,q) ->
               FStar_Tactics_Result.Success (a, q)
           | FStar_Tactics_Result.Failed (msg,q) ->
               FStar_Tactics_Result.Failed
                 ((Prims.strcat pref (Prims.strcat ": " msg)), q))
  
let (set : FStar_Tactics_Types.proofstate -> Prims.unit tac) =
  fun p  -> mk_tac (fun uu____1014  -> FStar_Tactics_Result.Success ((), p)) 
let (__do_unify :
  env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.bool tac)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let debug_on uu____1031 =
          let uu____1032 =
            FStar_Options.set_options FStar_Options.Set
              "--debug_level Rel --debug_level RelCheck"
             in
          ()  in
        let debug_off uu____1036 =
          let uu____1037 = FStar_Options.set_options FStar_Options.Reset ""
             in
          ()  in
        (let uu____1039 =
           FStar_TypeChecker_Env.debug env (FStar_Options.Other "1346")  in
         if uu____1039
         then
           (debug_on ();
            (let uu____1041 = FStar_Syntax_Print.term_to_string t1  in
             let uu____1042 = FStar_Syntax_Print.term_to_string t2  in
             FStar_Util.print2 "%%%%%%%%do_unify %s =? %s\n" uu____1041
               uu____1042))
         else ());
        (try
           let res = FStar_TypeChecker_Rel.teq_nosmt env t1 t2  in
           debug_off ();
           (let uu____1056 =
              FStar_TypeChecker_Env.debug env (FStar_Options.Other "1346")
               in
            if uu____1056
            then
              let uu____1057 = FStar_Util.string_of_bool res  in
              let uu____1058 = FStar_Syntax_Print.term_to_string t1  in
              let uu____1059 = FStar_Syntax_Print.term_to_string t2  in
              FStar_Util.print3 "%%%%%%%%do_unify (RESULT %s) %s =? %s\n"
                uu____1057 uu____1058 uu____1059
            else ());
           ret res
         with
         | FStar_Errors.Err (uu____1068,msg) ->
             (debug_off ();
              mlog
                (fun uu____1072  ->
                   FStar_Util.print1 ">> do_unify error, (%s)\n" msg)
                (fun uu____1074  -> ret false))
         | FStar_Errors.Error (uu____1075,msg,r) ->
             (debug_off ();
              mlog
                (fun uu____1081  ->
                   let uu____1082 = FStar_Range.string_of_range r  in
                   FStar_Util.print2 ">> do_unify error, (%s) at (%s)\n" msg
                     uu____1082) (fun uu____1084  -> ret false)))
  
let (do_unify :
  env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.bool tac)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____1098 = __do_unify env t1 t2  in
        bind uu____1098
          (fun b  ->
             if Prims.op_Negation b
             then
               let t11 = FStar_TypeChecker_Normalize.normalize [] env t1  in
               let t21 = FStar_TypeChecker_Normalize.normalize [] env t2  in
               __do_unify env t11 t21
             else ret b)
  
let (trysolve :
  FStar_Tactics_Types.goal -> FStar_Syntax_Syntax.term -> Prims.bool tac) =
  fun goal  ->
    fun solution  ->
      do_unify goal.FStar_Tactics_Types.context solution
        goal.FStar_Tactics_Types.witness
  
let (__dismiss : Prims.unit tac) =
  bind get
    (fun p  ->
       let uu____1125 =
         let uu___70_1126 = p  in
         let uu____1127 = FStar_List.tl p.FStar_Tactics_Types.goals  in
         {
           FStar_Tactics_Types.main_context =
             (uu___70_1126.FStar_Tactics_Types.main_context);
           FStar_Tactics_Types.main_goal =
             (uu___70_1126.FStar_Tactics_Types.main_goal);
           FStar_Tactics_Types.all_implicits =
             (uu___70_1126.FStar_Tactics_Types.all_implicits);
           FStar_Tactics_Types.goals = uu____1127;
           FStar_Tactics_Types.smt_goals =
             (uu___70_1126.FStar_Tactics_Types.smt_goals);
           FStar_Tactics_Types.depth =
             (uu___70_1126.FStar_Tactics_Types.depth);
           FStar_Tactics_Types.__dump =
             (uu___70_1126.FStar_Tactics_Types.__dump);
           FStar_Tactics_Types.psc = (uu___70_1126.FStar_Tactics_Types.psc);
           FStar_Tactics_Types.entry_range =
             (uu___70_1126.FStar_Tactics_Types.entry_range);
           FStar_Tactics_Types.guard_policy =
             (uu___70_1126.FStar_Tactics_Types.guard_policy);
           FStar_Tactics_Types.freshness =
             (uu___70_1126.FStar_Tactics_Types.freshness)
         }  in
       set uu____1125)
  
let (dismiss : Prims.unit -> Prims.unit tac) =
  fun uu____1134  ->
    bind get
      (fun p  ->
         match p.FStar_Tactics_Types.goals with
         | [] -> fail "dismiss: no more goals"
         | uu____1141 -> __dismiss)
  
let (solve :
  FStar_Tactics_Types.goal -> FStar_Syntax_Syntax.term -> Prims.unit tac) =
  fun goal  ->
    fun solution  ->
      let uu____1154 = trysolve goal solution  in
      bind uu____1154
        (fun b  ->
           if b
           then __dismiss
           else
             (let uu____1162 =
                let uu____1163 =
                  tts goal.FStar_Tactics_Types.context solution  in
                let uu____1164 =
                  tts goal.FStar_Tactics_Types.context
                    goal.FStar_Tactics_Types.witness
                   in
                let uu____1165 =
                  tts goal.FStar_Tactics_Types.context
                    goal.FStar_Tactics_Types.goal_ty
                   in
                FStar_Util.format3 "%s does not solve %s : %s" uu____1163
                  uu____1164 uu____1165
                 in
              fail uu____1162))
  
let (dismiss_all : Prims.unit tac) =
  bind get
    (fun p  ->
       set
         (let uu___71_1172 = p  in
          {
            FStar_Tactics_Types.main_context =
              (uu___71_1172.FStar_Tactics_Types.main_context);
            FStar_Tactics_Types.main_goal =
              (uu___71_1172.FStar_Tactics_Types.main_goal);
            FStar_Tactics_Types.all_implicits =
              (uu___71_1172.FStar_Tactics_Types.all_implicits);
            FStar_Tactics_Types.goals = [];
            FStar_Tactics_Types.smt_goals =
              (uu___71_1172.FStar_Tactics_Types.smt_goals);
            FStar_Tactics_Types.depth =
              (uu___71_1172.FStar_Tactics_Types.depth);
            FStar_Tactics_Types.__dump =
              (uu___71_1172.FStar_Tactics_Types.__dump);
            FStar_Tactics_Types.psc = (uu___71_1172.FStar_Tactics_Types.psc);
            FStar_Tactics_Types.entry_range =
              (uu___71_1172.FStar_Tactics_Types.entry_range);
            FStar_Tactics_Types.guard_policy =
              (uu___71_1172.FStar_Tactics_Types.guard_policy);
            FStar_Tactics_Types.freshness =
              (uu___71_1172.FStar_Tactics_Types.freshness)
          }))
  
let (nwarn : Prims.int FStar_ST.ref) =
  FStar_Util.mk_ref (Prims.parse_int "0") 
let (check_valid_goal : FStar_Tactics_Types.goal -> Prims.unit) =
  fun g  ->
    let uu____1189 = FStar_Options.defensive ()  in
    if uu____1189
    then
      let b = true  in
      let env = g.FStar_Tactics_Types.context  in
      let b1 =
        b && (FStar_TypeChecker_Env.closed env g.FStar_Tactics_Types.witness)
         in
      let b2 =
        b1 &&
          (FStar_TypeChecker_Env.closed env g.FStar_Tactics_Types.goal_ty)
         in
      let rec aux b3 e =
        let uu____1201 = FStar_TypeChecker_Env.pop_bv e  in
        match uu____1201 with
        | FStar_Pervasives_Native.None  -> b3
        | FStar_Pervasives_Native.Some (bv,e1) ->
            let b4 =
              b3 &&
                (FStar_TypeChecker_Env.closed e1 bv.FStar_Syntax_Syntax.sort)
               in
            aux b4 e1
         in
      let uu____1219 =
        (let uu____1222 = aux b2 env  in Prims.op_Negation uu____1222) &&
          (let uu____1224 = FStar_ST.op_Bang nwarn  in
           uu____1224 < (Prims.parse_int "5"))
         in
      (if uu____1219
       then
         ((let uu____1245 =
             let uu____1250 =
               let uu____1251 = goal_to_string g  in
               FStar_Util.format1
                 "The following goal is ill-formed. Keeping calm and carrying on...\n<%s>\n\n"
                 uu____1251
                in
             (FStar_Errors.Warning_IllFormedGoal, uu____1250)  in
           FStar_Errors.log_issue
             (g.FStar_Tactics_Types.goal_ty).FStar_Syntax_Syntax.pos
             uu____1245);
          (let uu____1252 =
             let uu____1253 = FStar_ST.op_Bang nwarn  in
             uu____1253 + (Prims.parse_int "1")  in
           FStar_ST.op_Colon_Equals nwarn uu____1252))
       else ())
    else ()
  
let (add_goals : FStar_Tactics_Types.goal Prims.list -> Prims.unit tac) =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___72_1311 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___72_1311.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___72_1311.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___72_1311.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (FStar_List.append gs p.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (uu___72_1311.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___72_1311.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___72_1311.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___72_1311.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___72_1311.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___72_1311.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___72_1311.FStar_Tactics_Types.freshness)
            }))
  
let (add_smt_goals : FStar_Tactics_Types.goal Prims.list -> Prims.unit tac) =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___73_1329 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___73_1329.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___73_1329.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___73_1329.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___73_1329.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (FStar_List.append gs p.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___73_1329.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___73_1329.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___73_1329.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___73_1329.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___73_1329.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___73_1329.FStar_Tactics_Types.freshness)
            }))
  
let (push_goals : FStar_Tactics_Types.goal Prims.list -> Prims.unit tac) =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___74_1347 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___74_1347.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___74_1347.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___74_1347.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (FStar_List.append p.FStar_Tactics_Types.goals gs);
              FStar_Tactics_Types.smt_goals =
                (uu___74_1347.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___74_1347.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___74_1347.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___74_1347.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___74_1347.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___74_1347.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___74_1347.FStar_Tactics_Types.freshness)
            }))
  
let (push_smt_goals : FStar_Tactics_Types.goal Prims.list -> Prims.unit tac)
  =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___75_1365 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___75_1365.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___75_1365.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___75_1365.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___75_1365.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (FStar_List.append p.FStar_Tactics_Types.smt_goals gs);
              FStar_Tactics_Types.depth =
                (uu___75_1365.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___75_1365.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___75_1365.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___75_1365.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___75_1365.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___75_1365.FStar_Tactics_Types.freshness)
            }))
  
let (replace_cur : FStar_Tactics_Types.goal -> Prims.unit tac) =
  fun g  -> bind __dismiss (fun uu____1374  -> add_goals [g]) 
let (add_implicits : implicits -> Prims.unit tac) =
  fun i  ->
    bind get
      (fun p  ->
         set
           (let uu___76_1386 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___76_1386.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___76_1386.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (FStar_List.append i p.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___76_1386.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (uu___76_1386.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___76_1386.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___76_1386.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___76_1386.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___76_1386.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___76_1386.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___76_1386.FStar_Tactics_Types.freshness)
            }))
  
let (new_uvar :
  Prims.string ->
    env -> FStar_Reflection_Data.typ -> FStar_Syntax_Syntax.term tac)
  =
  fun reason  ->
    fun env  ->
      fun typ  ->
        let uu____1412 =
          FStar_TypeChecker_Util.new_implicit_var reason
            typ.FStar_Syntax_Syntax.pos env typ
           in
        match uu____1412 with
        | (u,uu____1428,g_u) ->
            let uu____1442 =
              add_implicits g_u.FStar_TypeChecker_Env.implicits  in
            bind uu____1442 (fun uu____1446  -> ret u)
  
let (is_true : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____1450 = FStar_Syntax_Util.un_squash t  in
    match uu____1450 with
    | FStar_Pervasives_Native.Some t' ->
        let uu____1460 =
          let uu____1461 = FStar_Syntax_Subst.compress t'  in
          uu____1461.FStar_Syntax_Syntax.n  in
        (match uu____1460 with
         | FStar_Syntax_Syntax.Tm_fvar fv ->
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.true_lid
         | uu____1465 -> false)
    | uu____1466 -> false
  
let (is_false : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____1474 = FStar_Syntax_Util.un_squash t  in
    match uu____1474 with
    | FStar_Pervasives_Native.Some t' ->
        let uu____1484 =
          let uu____1485 = FStar_Syntax_Subst.compress t'  in
          uu____1485.FStar_Syntax_Syntax.n  in
        (match uu____1484 with
         | FStar_Syntax_Syntax.Tm_fvar fv ->
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.false_lid
         | uu____1489 -> false)
    | uu____1490 -> false
  
let (cur_goal : Prims.unit -> FStar_Tactics_Types.goal tac) =
  fun uu____1499  ->
    bind get
      (fun p  ->
         match p.FStar_Tactics_Types.goals with
         | [] -> fail "No more goals (1)"
         | hd1::tl1 -> ret hd1)
  
let (tadmit : Prims.unit -> Prims.unit tac) =
  fun uu____1514  ->
    let uu____1517 =
      let uu____1520 = cur_goal ()  in
      bind uu____1520
        (fun g  ->
           (let uu____1527 =
              let uu____1532 =
                let uu____1533 = goal_to_string g  in
                FStar_Util.format1 "Tactics admitted goal <%s>\n\n"
                  uu____1533
                 in
              (FStar_Errors.Warning_TacAdmit, uu____1532)  in
            FStar_Errors.log_issue
              (g.FStar_Tactics_Types.goal_ty).FStar_Syntax_Syntax.pos
              uu____1527);
           solve g FStar_Syntax_Util.exp_unit)
       in
    FStar_All.pipe_left (wrap_err "tadmit") uu____1517
  
let (fresh : Prims.unit -> FStar_BigInt.t tac) =
  fun uu____1542  ->
    bind get
      (fun ps  ->
         let n1 = ps.FStar_Tactics_Types.freshness  in
         let ps1 =
           let uu___77_1552 = ps  in
           {
             FStar_Tactics_Types.main_context =
               (uu___77_1552.FStar_Tactics_Types.main_context);
             FStar_Tactics_Types.main_goal =
               (uu___77_1552.FStar_Tactics_Types.main_goal);
             FStar_Tactics_Types.all_implicits =
               (uu___77_1552.FStar_Tactics_Types.all_implicits);
             FStar_Tactics_Types.goals =
               (uu___77_1552.FStar_Tactics_Types.goals);
             FStar_Tactics_Types.smt_goals =
               (uu___77_1552.FStar_Tactics_Types.smt_goals);
             FStar_Tactics_Types.depth =
               (uu___77_1552.FStar_Tactics_Types.depth);
             FStar_Tactics_Types.__dump =
               (uu___77_1552.FStar_Tactics_Types.__dump);
             FStar_Tactics_Types.psc = (uu___77_1552.FStar_Tactics_Types.psc);
             FStar_Tactics_Types.entry_range =
               (uu___77_1552.FStar_Tactics_Types.entry_range);
             FStar_Tactics_Types.guard_policy =
               (uu___77_1552.FStar_Tactics_Types.guard_policy);
             FStar_Tactics_Types.freshness = (n1 + (Prims.parse_int "1"))
           }  in
         let uu____1553 = set ps1  in
         bind uu____1553
           (fun uu____1558  ->
              let uu____1559 = FStar_BigInt.of_int_fs n1  in ret uu____1559))
  
let (ngoals : Prims.unit -> FStar_BigInt.t tac) =
  fun uu____1564  ->
    bind get
      (fun ps  ->
         let n1 = FStar_List.length ps.FStar_Tactics_Types.goals  in
         let uu____1572 = FStar_BigInt.of_int_fs n1  in ret uu____1572)
  
let (ngoals_smt : Prims.unit -> FStar_BigInt.t tac) =
  fun uu____1583  ->
    bind get
      (fun ps  ->
         let n1 = FStar_List.length ps.FStar_Tactics_Types.smt_goals  in
         let uu____1591 = FStar_BigInt.of_int_fs n1  in ret uu____1591)
  
let (is_guard : Prims.unit -> Prims.bool tac) =
  fun uu____1602  ->
    let uu____1605 = cur_goal ()  in
    bind uu____1605 (fun g  -> ret g.FStar_Tactics_Types.is_guard)
  
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
            let uu____1629 = env.FStar_TypeChecker_Env.universe_of env phi
               in
            FStar_Syntax_Util.mk_squash uu____1629 phi  in
          let uu____1630 = new_uvar reason env typ  in
          bind uu____1630
            (fun u  ->
               let goal =
                 {
                   FStar_Tactics_Types.context = env;
                   FStar_Tactics_Types.witness = u;
                   FStar_Tactics_Types.goal_ty = typ;
                   FStar_Tactics_Types.opts = opts;
                   FStar_Tactics_Types.is_guard = false
                 }  in
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
             (fun uu____1675  ->
                let uu____1676 = tts e t  in
                FStar_Util.print1 "Tac> __tc(%s)\n" uu____1676)
             (fun uu____1678  ->
                try
                  let uu____1698 =
                    (ps.FStar_Tactics_Types.main_context).FStar_TypeChecker_Env.type_of
                      e t
                     in
                  ret uu____1698
                with
                | FStar_Errors.Err (uu____1725,msg) ->
                    let uu____1727 = tts e t  in
                    let uu____1728 =
                      let uu____1729 = FStar_TypeChecker_Env.all_binders e
                         in
                      FStar_All.pipe_right uu____1729
                        (FStar_Syntax_Print.binders_to_string ", ")
                       in
                    fail3 "Cannot type %s in context (%s). Error = (%s)"
                      uu____1727 uu____1728 msg
                | FStar_Errors.Error (uu____1736,msg,uu____1738) ->
                    let uu____1739 = tts e t  in
                    let uu____1740 =
                      let uu____1741 = FStar_TypeChecker_Env.all_binders e
                         in
                      FStar_All.pipe_right uu____1741
                        (FStar_Syntax_Print.binders_to_string ", ")
                       in
                    fail3 "Cannot type %s in context (%s). Error = (%s)"
                      uu____1739 uu____1740 msg))
  
let (istrivial : env -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun e  ->
    fun t  ->
      let steps =
        [FStar_TypeChecker_Normalize.Reify;
        FStar_TypeChecker_Normalize.UnfoldUntil
          FStar_Syntax_Syntax.Delta_constant;
        FStar_TypeChecker_Normalize.Primops;
        FStar_TypeChecker_Normalize.Simplify;
        FStar_TypeChecker_Normalize.UnfoldTac;
        FStar_TypeChecker_Normalize.Unmeta]  in
      let t1 = normalize steps e t  in is_true t1
  
let (get_guard_policy : Prims.unit -> FStar_Tactics_Types.guard_policy tac) =
  fun uu____1762  ->
    bind get (fun ps  -> ret ps.FStar_Tactics_Types.guard_policy)
  
let (set_guard_policy : FStar_Tactics_Types.guard_policy -> Prims.unit tac) =
  fun pol  ->
    bind get
      (fun ps  ->
         set
           (let uu___80_1778 = ps  in
            {
              FStar_Tactics_Types.main_context =
                (uu___80_1778.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___80_1778.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___80_1778.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___80_1778.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (uu___80_1778.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___80_1778.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___80_1778.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___80_1778.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___80_1778.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy = pol;
              FStar_Tactics_Types.freshness =
                (uu___80_1778.FStar_Tactics_Types.freshness)
            }))
  
let with_policy : 'a . FStar_Tactics_Types.guard_policy -> 'a tac -> 'a tac =
  fun pol  ->
    fun t  ->
      let uu____1797 = get_guard_policy ()  in
      bind uu____1797
        (fun old_pol  ->
           let uu____1803 = set_guard_policy pol  in
           bind uu____1803
             (fun uu____1807  ->
                bind t
                  (fun r  ->
                     let uu____1811 = set_guard_policy old_pol  in
                     bind uu____1811 (fun uu____1815  -> ret r))))
  
let (proc_guard :
  Prims.string ->
    env ->
      FStar_TypeChecker_Env.guard_t ->
        FStar_Options.optionstate -> Prims.unit tac)
  =
  fun reason  ->
    fun e  ->
      fun g  ->
        fun opts  ->
          let uu____1832 =
            let uu____1833 = FStar_TypeChecker_Rel.simplify_guard e g  in
            uu____1833.FStar_TypeChecker_Env.guard_f  in
          match uu____1832 with
          | FStar_TypeChecker_Common.Trivial  -> ret ()
          | FStar_TypeChecker_Common.NonTrivial f ->
              let uu____1837 = istrivial e f  in
              if uu____1837
              then ret ()
              else
                bind get
                  (fun ps  ->
                     match ps.FStar_Tactics_Types.guard_policy with
                     | FStar_Tactics_Types.Drop  -> ret ()
                     | FStar_Tactics_Types.Goal  ->
                         let uu____1845 = mk_irrelevant_goal reason e f opts
                            in
                         bind uu____1845
                           (fun goal  ->
                              let goal1 =
                                let uu___81_1852 = goal  in
                                {
                                  FStar_Tactics_Types.context =
                                    (uu___81_1852.FStar_Tactics_Types.context);
                                  FStar_Tactics_Types.witness =
                                    (uu___81_1852.FStar_Tactics_Types.witness);
                                  FStar_Tactics_Types.goal_ty =
                                    (uu___81_1852.FStar_Tactics_Types.goal_ty);
                                  FStar_Tactics_Types.opts =
                                    (uu___81_1852.FStar_Tactics_Types.opts);
                                  FStar_Tactics_Types.is_guard = true
                                }  in
                              push_goals [goal1])
                     | FStar_Tactics_Types.SMT  ->
                         let uu____1853 = mk_irrelevant_goal reason e f opts
                            in
                         bind uu____1853
                           (fun goal  ->
                              let goal1 =
                                let uu___82_1860 = goal  in
                                {
                                  FStar_Tactics_Types.context =
                                    (uu___82_1860.FStar_Tactics_Types.context);
                                  FStar_Tactics_Types.witness =
                                    (uu___82_1860.FStar_Tactics_Types.witness);
                                  FStar_Tactics_Types.goal_ty =
                                    (uu___82_1860.FStar_Tactics_Types.goal_ty);
                                  FStar_Tactics_Types.opts =
                                    (uu___82_1860.FStar_Tactics_Types.opts);
                                  FStar_Tactics_Types.is_guard = true
                                }  in
                              push_smt_goals [goal1])
                     | FStar_Tactics_Types.Force  ->
                         (try
                            let uu____1868 =
                              let uu____1869 =
                                let uu____1870 =
                                  FStar_TypeChecker_Rel.discharge_guard_no_smt
                                    e g
                                   in
                                FStar_All.pipe_left
                                  FStar_TypeChecker_Rel.is_trivial uu____1870
                                 in
                              Prims.op_Negation uu____1869  in
                            if uu____1868
                            then
                              mlog
                                (fun uu____1875  ->
                                   let uu____1876 =
                                     FStar_TypeChecker_Rel.guard_to_string e
                                       g
                                      in
                                   FStar_Util.print1 "guard = %s\n"
                                     uu____1876)
                                (fun uu____1878  ->
                                   fail1 "Forcing the guard failed %s)"
                                     reason)
                            else ret ()
                          with
                          | uu____1885 ->
                              mlog
                                (fun uu____1888  ->
                                   let uu____1889 =
                                     FStar_TypeChecker_Rel.guard_to_string e
                                       g
                                      in
                                   FStar_Util.print1 "guard = %s\n"
                                     uu____1889)
                                (fun uu____1891  ->
                                   fail1 "Forcing the guard failed (%s)"
                                     reason)))
  
let (tc : FStar_Syntax_Syntax.term -> FStar_Reflection_Data.typ tac) =
  fun t  ->
    let uu____1899 =
      let uu____1902 = cur_goal ()  in
      bind uu____1902
        (fun goal  ->
           let uu____1908 = __tc goal.FStar_Tactics_Types.context t  in
           bind uu____1908
             (fun uu____1928  ->
                match uu____1928 with
                | (t1,typ,guard) ->
                    let uu____1940 =
                      proc_guard "tc" goal.FStar_Tactics_Types.context guard
                        goal.FStar_Tactics_Types.opts
                       in
                    bind uu____1940 (fun uu____1944  -> ret typ)))
       in
    FStar_All.pipe_left (wrap_err "tc") uu____1899
  
let (add_irrelevant_goal :
  Prims.string ->
    env ->
      FStar_Reflection_Data.typ ->
        FStar_Options.optionstate -> Prims.unit tac)
  =
  fun reason  ->
    fun env  ->
      fun phi  ->
        fun opts  ->
          let uu____1965 = mk_irrelevant_goal reason env phi opts  in
          bind uu____1965 (fun goal  -> add_goals [goal])
  
let (trivial : Prims.unit -> Prims.unit tac) =
  fun uu____1974  ->
    let uu____1977 = cur_goal ()  in
    bind uu____1977
      (fun goal  ->
         let uu____1983 =
           istrivial goal.FStar_Tactics_Types.context
             goal.FStar_Tactics_Types.goal_ty
            in
         if uu____1983
         then solve goal FStar_Syntax_Util.exp_unit
         else
           (let uu____1987 =
              tts goal.FStar_Tactics_Types.context
                goal.FStar_Tactics_Types.goal_ty
               in
            fail1 "Not a trivial goal: %s" uu____1987))
  
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
          let uu____2008 =
            let uu____2009 = FStar_TypeChecker_Rel.simplify_guard e g  in
            uu____2009.FStar_TypeChecker_Env.guard_f  in
          match uu____2008 with
          | FStar_TypeChecker_Common.Trivial  ->
              ret FStar_Pervasives_Native.None
          | FStar_TypeChecker_Common.NonTrivial f ->
              let uu____2017 = istrivial e f  in
              if uu____2017
              then ret FStar_Pervasives_Native.None
              else
                (let uu____2025 = mk_irrelevant_goal reason e f opts  in
                 bind uu____2025
                   (fun goal  ->
                      ret
                        (FStar_Pervasives_Native.Some
                           (let uu___85_2035 = goal  in
                            {
                              FStar_Tactics_Types.context =
                                (uu___85_2035.FStar_Tactics_Types.context);
                              FStar_Tactics_Types.witness =
                                (uu___85_2035.FStar_Tactics_Types.witness);
                              FStar_Tactics_Types.goal_ty =
                                (uu___85_2035.FStar_Tactics_Types.goal_ty);
                              FStar_Tactics_Types.opts =
                                (uu___85_2035.FStar_Tactics_Types.opts);
                              FStar_Tactics_Types.is_guard = true
                            }))))
  
let (smt : Prims.unit -> Prims.unit tac) =
  fun uu____2040  ->
    let uu____2043 = cur_goal ()  in
    bind uu____2043
      (fun g  ->
         let uu____2049 = is_irrelevant g  in
         if uu____2049
         then bind __dismiss (fun uu____2053  -> add_smt_goals [g])
         else
           (let uu____2055 =
              tts g.FStar_Tactics_Types.context g.FStar_Tactics_Types.goal_ty
               in
            fail1 "goal is not irrelevant: cannot dispatch to smt (%s)"
              uu____2055))
  
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
             let uu____2096 =
               try
                 let uu____2130 =
                   let uu____2139 = FStar_BigInt.to_int_fs n1  in
                   FStar_List.splitAt uu____2139 p.FStar_Tactics_Types.goals
                    in
                 ret uu____2130
               with | uu____2161 -> fail "divide: not enough goals"  in
             bind uu____2096
               (fun uu____2188  ->
                  match uu____2188 with
                  | (lgs,rgs) ->
                      let lp =
                        let uu___86_2214 = p  in
                        {
                          FStar_Tactics_Types.main_context =
                            (uu___86_2214.FStar_Tactics_Types.main_context);
                          FStar_Tactics_Types.main_goal =
                            (uu___86_2214.FStar_Tactics_Types.main_goal);
                          FStar_Tactics_Types.all_implicits =
                            (uu___86_2214.FStar_Tactics_Types.all_implicits);
                          FStar_Tactics_Types.goals = lgs;
                          FStar_Tactics_Types.smt_goals = [];
                          FStar_Tactics_Types.depth =
                            (uu___86_2214.FStar_Tactics_Types.depth);
                          FStar_Tactics_Types.__dump =
                            (uu___86_2214.FStar_Tactics_Types.__dump);
                          FStar_Tactics_Types.psc =
                            (uu___86_2214.FStar_Tactics_Types.psc);
                          FStar_Tactics_Types.entry_range =
                            (uu___86_2214.FStar_Tactics_Types.entry_range);
                          FStar_Tactics_Types.guard_policy =
                            (uu___86_2214.FStar_Tactics_Types.guard_policy);
                          FStar_Tactics_Types.freshness =
                            (uu___86_2214.FStar_Tactics_Types.freshness)
                        }  in
                      let rp =
                        let uu___87_2216 = p  in
                        {
                          FStar_Tactics_Types.main_context =
                            (uu___87_2216.FStar_Tactics_Types.main_context);
                          FStar_Tactics_Types.main_goal =
                            (uu___87_2216.FStar_Tactics_Types.main_goal);
                          FStar_Tactics_Types.all_implicits =
                            (uu___87_2216.FStar_Tactics_Types.all_implicits);
                          FStar_Tactics_Types.goals = rgs;
                          FStar_Tactics_Types.smt_goals = [];
                          FStar_Tactics_Types.depth =
                            (uu___87_2216.FStar_Tactics_Types.depth);
                          FStar_Tactics_Types.__dump =
                            (uu___87_2216.FStar_Tactics_Types.__dump);
                          FStar_Tactics_Types.psc =
                            (uu___87_2216.FStar_Tactics_Types.psc);
                          FStar_Tactics_Types.entry_range =
                            (uu___87_2216.FStar_Tactics_Types.entry_range);
                          FStar_Tactics_Types.guard_policy =
                            (uu___87_2216.FStar_Tactics_Types.guard_policy);
                          FStar_Tactics_Types.freshness =
                            (uu___87_2216.FStar_Tactics_Types.freshness)
                        }  in
                      let uu____2217 = set lp  in
                      bind uu____2217
                        (fun uu____2225  ->
                           bind l
                             (fun a  ->
                                bind get
                                  (fun lp'  ->
                                     let uu____2239 = set rp  in
                                     bind uu____2239
                                       (fun uu____2247  ->
                                          bind r
                                            (fun b  ->
                                               bind get
                                                 (fun rp'  ->
                                                    let p' =
                                                      let uu___88_2263 = p
                                                         in
                                                      {
                                                        FStar_Tactics_Types.main_context
                                                          =
                                                          (uu___88_2263.FStar_Tactics_Types.main_context);
                                                        FStar_Tactics_Types.main_goal
                                                          =
                                                          (uu___88_2263.FStar_Tactics_Types.main_goal);
                                                        FStar_Tactics_Types.all_implicits
                                                          =
                                                          (uu___88_2263.FStar_Tactics_Types.all_implicits);
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
                                                          (uu___88_2263.FStar_Tactics_Types.depth);
                                                        FStar_Tactics_Types.__dump
                                                          =
                                                          (uu___88_2263.FStar_Tactics_Types.__dump);
                                                        FStar_Tactics_Types.psc
                                                          =
                                                          (uu___88_2263.FStar_Tactics_Types.psc);
                                                        FStar_Tactics_Types.entry_range
                                                          =
                                                          (uu___88_2263.FStar_Tactics_Types.entry_range);
                                                        FStar_Tactics_Types.guard_policy
                                                          =
                                                          (uu___88_2263.FStar_Tactics_Types.guard_policy);
                                                        FStar_Tactics_Types.freshness
                                                          =
                                                          (uu___88_2263.FStar_Tactics_Types.freshness)
                                                      }  in
                                                    let uu____2264 = set p'
                                                       in
                                                    bind uu____2264
                                                      (fun uu____2272  ->
                                                         ret (a, b))))))))))
  
let focus : 'a . 'a tac -> 'a tac =
  fun f  ->
    let uu____2290 = divide FStar_BigInt.one f idtac  in
    bind uu____2290
      (fun uu____2303  -> match uu____2303 with | (a,()) -> ret a)
  
let rec map : 'a . 'a tac -> 'a Prims.list tac =
  fun tau  ->
    bind get
      (fun p  ->
         match p.FStar_Tactics_Types.goals with
         | [] -> ret []
         | uu____2337::uu____2338 ->
             let uu____2341 =
               let uu____2350 = map tau  in
               divide FStar_BigInt.one tau uu____2350  in
             bind uu____2341
               (fun uu____2368  ->
                  match uu____2368 with | (h,t) -> ret (h :: t)))
  
let (seq : Prims.unit tac -> Prims.unit tac -> Prims.unit tac) =
  fun t1  ->
    fun t2  ->
      let uu____2405 =
        bind t1
          (fun uu____2410  ->
             let uu____2411 = map t2  in
             bind uu____2411 (fun uu____2419  -> ret ()))
         in
      focus uu____2405
  
let (intro : Prims.unit -> FStar_Syntax_Syntax.binder tac) =
  fun uu____2426  ->
    let uu____2429 =
      let uu____2432 = cur_goal ()  in
      bind uu____2432
        (fun goal  ->
           let uu____2441 =
             FStar_Syntax_Util.arrow_one goal.FStar_Tactics_Types.goal_ty  in
           match uu____2441 with
           | FStar_Pervasives_Native.Some (b,c) ->
               let uu____2456 =
                 let uu____2457 = FStar_Syntax_Util.is_total_comp c  in
                 Prims.op_Negation uu____2457  in
               if uu____2456
               then fail "Codomain is effectful"
               else
                 (let env' =
                    FStar_TypeChecker_Env.push_binders
                      goal.FStar_Tactics_Types.context [b]
                     in
                  let typ' = comp_to_typ c  in
                  let uu____2463 = new_uvar "intro" env' typ'  in
                  bind uu____2463
                    (fun u  ->
                       let uu____2469 =
                         let uu____2472 =
                           FStar_Syntax_Util.abs [b] u
                             FStar_Pervasives_Native.None
                            in
                         trysolve goal uu____2472  in
                       bind uu____2469
                         (fun bb  ->
                            if bb
                            then
                              let uu____2478 =
                                let uu____2481 =
                                  let uu___91_2482 = goal  in
                                  let uu____2483 = bnorm env' u  in
                                  let uu____2484 = bnorm env' typ'  in
                                  {
                                    FStar_Tactics_Types.context = env';
                                    FStar_Tactics_Types.witness = uu____2483;
                                    FStar_Tactics_Types.goal_ty = uu____2484;
                                    FStar_Tactics_Types.opts =
                                      (uu___91_2482.FStar_Tactics_Types.opts);
                                    FStar_Tactics_Types.is_guard =
                                      (uu___91_2482.FStar_Tactics_Types.is_guard)
                                  }  in
                                replace_cur uu____2481  in
                              bind uu____2478 (fun uu____2486  -> ret b)
                            else fail "unification failed")))
           | FStar_Pervasives_Native.None  ->
               let uu____2492 =
                 tts goal.FStar_Tactics_Types.context
                   goal.FStar_Tactics_Types.goal_ty
                  in
               fail1 "goal is not an arrow (%s)" uu____2492)
       in
    FStar_All.pipe_left (wrap_err "intro") uu____2429
  
let (intro_rec :
  Prims.unit ->
    (FStar_Syntax_Syntax.binder,FStar_Syntax_Syntax.binder)
      FStar_Pervasives_Native.tuple2 tac)
  =
  fun uu____2505  ->
    let uu____2512 = cur_goal ()  in
    bind uu____2512
      (fun goal  ->
         FStar_Util.print_string
           "WARNING (intro_rec): calling this is known to cause normalizer loops\n";
         FStar_Util.print_string
           "WARNING (intro_rec): proceed at your own risk...\n";
         (let uu____2529 =
            FStar_Syntax_Util.arrow_one goal.FStar_Tactics_Types.goal_ty  in
          match uu____2529 with
          | FStar_Pervasives_Native.Some (b,c) ->
              let uu____2548 =
                let uu____2549 = FStar_Syntax_Util.is_total_comp c  in
                Prims.op_Negation uu____2549  in
              if uu____2548
              then fail "Codomain is effectful"
              else
                (let bv =
                   FStar_Syntax_Syntax.gen_bv "__recf"
                     FStar_Pervasives_Native.None
                     goal.FStar_Tactics_Types.goal_ty
                    in
                 let bs =
                   let uu____2565 = FStar_Syntax_Syntax.mk_binder bv  in
                   [uu____2565; b]  in
                 let env' =
                   FStar_TypeChecker_Env.push_binders
                     goal.FStar_Tactics_Types.context bs
                    in
                 let uu____2567 =
                   let uu____2570 = comp_to_typ c  in
                   new_uvar "intro_rec" env' uu____2570  in
                 bind uu____2567
                   (fun u  ->
                      let lb =
                        let uu____2585 =
                          FStar_Syntax_Util.abs [b] u
                            FStar_Pervasives_Native.None
                           in
                        FStar_Syntax_Util.mk_letbinding (FStar_Util.Inl bv)
                          [] goal.FStar_Tactics_Types.goal_ty
                          FStar_Parser_Const.effect_Tot_lid uu____2585 []
                          FStar_Range.dummyRange
                         in
                      let body = FStar_Syntax_Syntax.bv_to_name bv  in
                      let uu____2591 =
                        FStar_Syntax_Subst.close_let_rec [lb] body  in
                      match uu____2591 with
                      | (lbs,body1) ->
                          let tm =
                            FStar_Syntax_Syntax.mk
                              (FStar_Syntax_Syntax.Tm_let
                                 ((true, lbs), body1))
                              FStar_Pervasives_Native.None
                              (goal.FStar_Tactics_Types.witness).FStar_Syntax_Syntax.pos
                             in
                          let uu____2621 = trysolve goal tm  in
                          bind uu____2621
                            (fun bb  ->
                               if bb
                               then
                                 let uu____2637 =
                                   let uu____2640 =
                                     let uu___92_2641 = goal  in
                                     let uu____2642 = bnorm env' u  in
                                     let uu____2643 =
                                       let uu____2644 = comp_to_typ c  in
                                       bnorm env' uu____2644  in
                                     {
                                       FStar_Tactics_Types.context = env';
                                       FStar_Tactics_Types.witness =
                                         uu____2642;
                                       FStar_Tactics_Types.goal_ty =
                                         uu____2643;
                                       FStar_Tactics_Types.opts =
                                         (uu___92_2641.FStar_Tactics_Types.opts);
                                       FStar_Tactics_Types.is_guard =
                                         (uu___92_2641.FStar_Tactics_Types.is_guard)
                                     }  in
                                   replace_cur uu____2640  in
                                 bind uu____2637
                                   (fun uu____2651  ->
                                      let uu____2652 =
                                        let uu____2657 =
                                          FStar_Syntax_Syntax.mk_binder bv
                                           in
                                        (uu____2657, b)  in
                                      ret uu____2652)
                               else fail "intro_rec: unification failed")))
          | FStar_Pervasives_Native.None  ->
              let uu____2671 =
                tts goal.FStar_Tactics_Types.context
                  goal.FStar_Tactics_Types.goal_ty
                 in
              fail1 "intro_rec: goal is not an arrow (%s)" uu____2671))
  
let (norm : FStar_Syntax_Embeddings.norm_step Prims.list -> Prims.unit tac) =
  fun s  ->
    let uu____2687 = cur_goal ()  in
    bind uu____2687
      (fun goal  ->
         mlog
           (fun uu____2694  ->
              let uu____2695 =
                FStar_Syntax_Print.term_to_string
                  goal.FStar_Tactics_Types.witness
                 in
              FStar_Util.print1 "norm: witness = %s\n" uu____2695)
           (fun uu____2700  ->
              let steps =
                let uu____2704 = FStar_TypeChecker_Normalize.tr_norm_steps s
                   in
                FStar_List.append
                  [FStar_TypeChecker_Normalize.Reify;
                  FStar_TypeChecker_Normalize.UnfoldTac] uu____2704
                 in
              let w =
                normalize steps goal.FStar_Tactics_Types.context
                  goal.FStar_Tactics_Types.witness
                 in
              let t =
                normalize steps goal.FStar_Tactics_Types.context
                  goal.FStar_Tactics_Types.goal_ty
                 in
              replace_cur
                (let uu___93_2711 = goal  in
                 {
                   FStar_Tactics_Types.context =
                     (uu___93_2711.FStar_Tactics_Types.context);
                   FStar_Tactics_Types.witness = w;
                   FStar_Tactics_Types.goal_ty = t;
                   FStar_Tactics_Types.opts =
                     (uu___93_2711.FStar_Tactics_Types.opts);
                   FStar_Tactics_Types.is_guard =
                     (uu___93_2711.FStar_Tactics_Types.is_guard)
                 })))
  
let (norm_term_env :
  env ->
    FStar_Syntax_Embeddings.norm_step Prims.list ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term tac)
  =
  fun e  ->
    fun s  ->
      fun t  ->
        let uu____2729 =
          mlog
            (fun uu____2734  ->
               let uu____2735 = FStar_Syntax_Print.term_to_string t  in
               FStar_Util.print1 "norm_term: tm = %s\n" uu____2735)
            (fun uu____2737  ->
               bind get
                 (fun ps  ->
                    let opts =
                      match ps.FStar_Tactics_Types.goals with
                      | g::uu____2743 -> g.FStar_Tactics_Types.opts
                      | uu____2746 -> FStar_Options.peek ()  in
                    mlog
                      (fun uu____2751  ->
                         let uu____2752 =
                           tts ps.FStar_Tactics_Types.main_context t  in
                         FStar_Util.print1 "norm_term_env: t = %s\n"
                           uu____2752)
                      (fun uu____2755  ->
                         let uu____2756 = __tc e t  in
                         bind uu____2756
                           (fun uu____2777  ->
                              match uu____2777 with
                              | (t1,uu____2787,uu____2788) ->
                                  let steps =
                                    let uu____2792 =
                                      FStar_TypeChecker_Normalize.tr_norm_steps
                                        s
                                       in
                                    FStar_List.append
                                      [FStar_TypeChecker_Normalize.Reify;
                                      FStar_TypeChecker_Normalize.UnfoldTac]
                                      uu____2792
                                     in
                                  let t2 =
                                    normalize steps
                                      ps.FStar_Tactics_Types.main_context t1
                                     in
                                  ret t2))))
           in
        FStar_All.pipe_left (wrap_err "norm_term") uu____2729
  
let (refine_intro : Prims.unit -> Prims.unit tac) =
  fun uu____2804  ->
    let uu____2807 =
      let uu____2810 = cur_goal ()  in
      bind uu____2810
        (fun g  ->
           let uu____2817 =
             FStar_TypeChecker_Rel.base_and_refinement
               g.FStar_Tactics_Types.context g.FStar_Tactics_Types.goal_ty
              in
           match uu____2817 with
           | (uu____2830,FStar_Pervasives_Native.None ) ->
               fail "not a refinement"
           | (t,FStar_Pervasives_Native.Some (bv,phi)) ->
               let g1 =
                 let uu___94_2855 = g  in
                 {
                   FStar_Tactics_Types.context =
                     (uu___94_2855.FStar_Tactics_Types.context);
                   FStar_Tactics_Types.witness =
                     (uu___94_2855.FStar_Tactics_Types.witness);
                   FStar_Tactics_Types.goal_ty = t;
                   FStar_Tactics_Types.opts =
                     (uu___94_2855.FStar_Tactics_Types.opts);
                   FStar_Tactics_Types.is_guard =
                     (uu___94_2855.FStar_Tactics_Types.is_guard)
                 }  in
               let uu____2856 =
                 let uu____2861 =
                   let uu____2866 =
                     let uu____2867 = FStar_Syntax_Syntax.mk_binder bv  in
                     [uu____2867]  in
                   FStar_Syntax_Subst.open_term uu____2866 phi  in
                 match uu____2861 with
                 | (bvs,phi1) ->
                     let uu____2874 =
                       let uu____2875 = FStar_List.hd bvs  in
                       FStar_Pervasives_Native.fst uu____2875  in
                     (uu____2874, phi1)
                  in
               (match uu____2856 with
                | (bv1,phi1) ->
                    let uu____2888 =
                      let uu____2891 =
                        FStar_Syntax_Subst.subst
                          [FStar_Syntax_Syntax.NT
                             (bv1, (g.FStar_Tactics_Types.witness))] phi1
                         in
                      mk_irrelevant_goal "refine_intro refinement"
                        g.FStar_Tactics_Types.context uu____2891
                        g.FStar_Tactics_Types.opts
                       in
                    bind uu____2888
                      (fun g2  ->
                         bind __dismiss
                           (fun uu____2895  -> add_goals [g1; g2]))))
       in
    FStar_All.pipe_left (wrap_err "refine_intro") uu____2807
  
let (__exact_now : Prims.bool -> FStar_Syntax_Syntax.term -> Prims.unit tac)
  =
  fun set_expected_typ1  ->
    fun t  ->
      let uu____2910 = cur_goal ()  in
      bind uu____2910
        (fun goal  ->
           let env =
             if set_expected_typ1
             then
               FStar_TypeChecker_Env.set_expected_typ
                 goal.FStar_Tactics_Types.context
                 goal.FStar_Tactics_Types.goal_ty
             else goal.FStar_Tactics_Types.context  in
           let uu____2919 = __tc env t  in
           bind uu____2919
             (fun uu____2938  ->
                match uu____2938 with
                | (t1,typ,guard) ->
                    mlog
                      (fun uu____2953  ->
                         let uu____2954 =
                           tts goal.FStar_Tactics_Types.context typ  in
                         let uu____2955 =
                           FStar_TypeChecker_Rel.guard_to_string
                             goal.FStar_Tactics_Types.context guard
                            in
                         FStar_Util.print2
                           "__exact_now: got type %s\n__exact_now and guard %s\n"
                           uu____2954 uu____2955)
                      (fun uu____2958  ->
                         let uu____2959 =
                           proc_guard "__exact typing"
                             goal.FStar_Tactics_Types.context guard
                             goal.FStar_Tactics_Types.opts
                            in
                         bind uu____2959
                           (fun uu____2963  ->
                              mlog
                                (fun uu____2967  ->
                                   let uu____2968 =
                                     tts goal.FStar_Tactics_Types.context typ
                                      in
                                   let uu____2969 =
                                     tts goal.FStar_Tactics_Types.context
                                       goal.FStar_Tactics_Types.goal_ty
                                      in
                                   FStar_Util.print2
                                     "__exact_now: unifying %s and %s\n"
                                     uu____2968 uu____2969)
                                (fun uu____2972  ->
                                   let uu____2973 =
                                     do_unify
                                       goal.FStar_Tactics_Types.context typ
                                       goal.FStar_Tactics_Types.goal_ty
                                      in
                                   bind uu____2973
                                     (fun b  ->
                                        if b
                                        then solve goal t1
                                        else
                                          (let uu____2981 =
                                             tts
                                               goal.FStar_Tactics_Types.context
                                               t1
                                              in
                                           let uu____2982 =
                                             tts
                                               goal.FStar_Tactics_Types.context
                                               typ
                                              in
                                           let uu____2983 =
                                             tts
                                               goal.FStar_Tactics_Types.context
                                               goal.FStar_Tactics_Types.goal_ty
                                              in
                                           let uu____2984 =
                                             tts
                                               goal.FStar_Tactics_Types.context
                                               goal.FStar_Tactics_Types.witness
                                              in
                                           fail4
                                             "%s : %s does not exactly solve the goal %s (witness = %s)"
                                             uu____2981 uu____2982 uu____2983
                                             uu____2984)))))))
  
let (t_exact : Prims.bool -> FStar_Syntax_Syntax.term -> Prims.unit tac) =
  fun set_expected_typ1  ->
    fun tm  ->
      let uu____2995 =
        mlog
          (fun uu____3000  ->
             let uu____3001 = FStar_Syntax_Print.term_to_string tm  in
             FStar_Util.print1 "t_exact: tm = %s\n" uu____3001)
          (fun uu____3004  ->
             let uu____3005 =
               let uu____3012 = __exact_now set_expected_typ1 tm  in
               trytac' uu____3012  in
             bind uu____3005
               (fun uu___60_3021  ->
                  match uu___60_3021 with
                  | FStar_Util.Inr r -> ret ()
                  | FStar_Util.Inl e ->
                      let uu____3030 =
                        let uu____3037 =
                          let uu____3040 =
                            norm [FStar_Syntax_Embeddings.Delta]  in
                          bind uu____3040
                            (fun uu____3045  ->
                               let uu____3046 = refine_intro ()  in
                               bind uu____3046
                                 (fun uu____3050  ->
                                    __exact_now set_expected_typ1 tm))
                           in
                        trytac' uu____3037  in
                      bind uu____3030
                        (fun uu___59_3057  ->
                           match uu___59_3057 with
                           | FStar_Util.Inr r -> ret ()
                           | FStar_Util.Inl uu____3065 -> fail e)))
         in
      FStar_All.pipe_left (wrap_err "exact") uu____2995
  
let (uvar_free_in_goal :
  FStar_Syntax_Syntax.uvar -> FStar_Tactics_Types.goal -> Prims.bool) =
  fun u  ->
    fun g  ->
      if g.FStar_Tactics_Types.is_guard
      then false
      else
        (let free_uvars =
           let uu____3080 =
             let uu____3087 =
               FStar_Syntax_Free.uvars g.FStar_Tactics_Types.goal_ty  in
             FStar_Util.set_elements uu____3087  in
           FStar_List.map FStar_Pervasives_Native.fst uu____3080  in
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
          let uu____3147 = f x  in
          bind uu____3147
            (fun y  ->
               let uu____3155 = mapM f xs  in
               bind uu____3155 (fun ys  -> ret (y :: ys)))
  
exception NoUnif 
let (uu___is_NoUnif : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with | NoUnif  -> true | uu____3173 -> false
  
let rec (__apply :
  Prims.bool ->
    FStar_Syntax_Syntax.term -> FStar_Reflection_Data.typ -> Prims.unit tac)
  =
  fun uopt  ->
    fun tm  ->
      fun typ  ->
        let uu____3187 = cur_goal ()  in
        bind uu____3187
          (fun goal  ->
             mlog
               (fun uu____3194  ->
                  let uu____3195 = FStar_Syntax_Print.term_to_string tm  in
                  FStar_Util.print1 ">>> Calling __exact(%s)\n" uu____3195)
               (fun uu____3198  ->
                  let uu____3199 =
                    let uu____3204 =
                      let uu____3207 = t_exact false tm  in
                      with_policy FStar_Tactics_Types.Force uu____3207  in
                    trytac_exn uu____3204  in
                  bind uu____3199
                    (fun uu___61_3214  ->
                       match uu___61_3214 with
                       | FStar_Pervasives_Native.Some r -> ret ()
                       | FStar_Pervasives_Native.None  ->
                           mlog
                             (fun uu____3222  ->
                                let uu____3223 =
                                  FStar_Syntax_Print.term_to_string typ  in
                                FStar_Util.print1 ">>> typ = %s\n" uu____3223)
                             (fun uu____3226  ->
                                let uu____3227 =
                                  FStar_Syntax_Util.arrow_one typ  in
                                match uu____3227 with
                                | FStar_Pervasives_Native.None  ->
                                    FStar_Exn.raise NoUnif
                                | FStar_Pervasives_Native.Some ((bv,aq),c) ->
                                    mlog
                                      (fun uu____3259  ->
                                         let uu____3260 =
                                           FStar_Syntax_Print.binder_to_string
                                             (bv, aq)
                                            in
                                         FStar_Util.print1
                                           "__apply: pushing binder %s\n"
                                           uu____3260)
                                      (fun uu____3263  ->
                                         let uu____3264 =
                                           let uu____3265 =
                                             FStar_Syntax_Util.is_total_comp
                                               c
                                              in
                                           Prims.op_Negation uu____3265  in
                                         if uu____3264
                                         then
                                           fail "apply: not total codomain"
                                         else
                                           (let uu____3269 =
                                              new_uvar "apply"
                                                goal.FStar_Tactics_Types.context
                                                bv.FStar_Syntax_Syntax.sort
                                               in
                                            bind uu____3269
                                              (fun u  ->
                                                 let tm' =
                                                   FStar_Syntax_Syntax.mk_Tm_app
                                                     tm [(u, aq)]
                                                     FStar_Pervasives_Native.None
                                                     tm.FStar_Syntax_Syntax.pos
                                                    in
                                                 let typ' =
                                                   let uu____3289 =
                                                     comp_to_typ c  in
                                                   FStar_All.pipe_left
                                                     (FStar_Syntax_Subst.subst
                                                        [FStar_Syntax_Syntax.NT
                                                           (bv, u)])
                                                     uu____3289
                                                    in
                                                 let uu____3290 =
                                                   __apply uopt tm' typ'  in
                                                 bind uu____3290
                                                   (fun uu____3298  ->
                                                      let u1 =
                                                        bnorm
                                                          goal.FStar_Tactics_Types.context
                                                          u
                                                         in
                                                      let uu____3300 =
                                                        let uu____3301 =
                                                          let uu____3304 =
                                                            let uu____3305 =
                                                              FStar_Syntax_Util.head_and_args
                                                                u1
                                                               in
                                                            FStar_Pervasives_Native.fst
                                                              uu____3305
                                                             in
                                                          FStar_Syntax_Subst.compress
                                                            uu____3304
                                                           in
                                                        uu____3301.FStar_Syntax_Syntax.n
                                                         in
                                                      match uu____3300 with
                                                      | FStar_Syntax_Syntax.Tm_uvar
                                                          (uvar,uu____3333)
                                                          ->
                                                          bind get
                                                            (fun ps  ->
                                                               let uu____3361
                                                                 =
                                                                 uopt &&
                                                                   (uvar_free
                                                                    uvar ps)
                                                                  in
                                                               if uu____3361
                                                               then ret ()
                                                               else
                                                                 (let uu____3365
                                                                    =
                                                                    let uu____3368
                                                                    =
                                                                    let uu___95_3369
                                                                    = goal
                                                                     in
                                                                    let uu____3370
                                                                    =
                                                                    bnorm
                                                                    goal.FStar_Tactics_Types.context
                                                                    u1  in
                                                                    let uu____3371
                                                                    =
                                                                    bnorm
                                                                    goal.FStar_Tactics_Types.context
                                                                    bv.FStar_Syntax_Syntax.sort
                                                                     in
                                                                    {
                                                                    FStar_Tactics_Types.context
                                                                    =
                                                                    (uu___95_3369.FStar_Tactics_Types.context);
                                                                    FStar_Tactics_Types.witness
                                                                    =
                                                                    uu____3370;
                                                                    FStar_Tactics_Types.goal_ty
                                                                    =
                                                                    uu____3371;
                                                                    FStar_Tactics_Types.opts
                                                                    =
                                                                    (uu___95_3369.FStar_Tactics_Types.opts);
                                                                    FStar_Tactics_Types.is_guard
                                                                    = false
                                                                    }  in
                                                                    [uu____3368]
                                                                     in
                                                                  add_goals
                                                                    uu____3365))
                                                      | t -> ret ()))))))))
  
let try_unif : 'a . 'a tac -> 'a tac -> 'a tac =
  fun t  ->
    fun t'  -> mk_tac (fun ps  -> try run t ps with | NoUnif  -> run t' ps)
  
let (apply : Prims.bool -> FStar_Syntax_Syntax.term -> Prims.unit tac) =
  fun uopt  ->
    fun tm  ->
      let uu____3417 =
        mlog
          (fun uu____3422  ->
             let uu____3423 = FStar_Syntax_Print.term_to_string tm  in
             FStar_Util.print1 "apply: tm = %s\n" uu____3423)
          (fun uu____3426  ->
             let uu____3427 = cur_goal ()  in
             bind uu____3427
               (fun goal  ->
                  let uu____3433 = __tc goal.FStar_Tactics_Types.context tm
                     in
                  bind uu____3433
                    (fun uu____3455  ->
                       match uu____3455 with
                       | (tm1,typ,guard) ->
                           let typ1 =
                             bnorm goal.FStar_Tactics_Types.context typ  in
                           let uu____3468 =
                             let uu____3471 =
                               let uu____3474 = __apply uopt tm1 typ1  in
                               bind uu____3474
                                 (fun uu____3478  ->
                                    proc_guard "apply guard"
                                      goal.FStar_Tactics_Types.context guard
                                      goal.FStar_Tactics_Types.opts)
                                in
                             focus uu____3471  in
                           let uu____3479 =
                             let uu____3482 =
                               tts goal.FStar_Tactics_Types.context tm1  in
                             let uu____3483 =
                               tts goal.FStar_Tactics_Types.context typ1  in
                             let uu____3484 =
                               tts goal.FStar_Tactics_Types.context
                                 goal.FStar_Tactics_Types.goal_ty
                                in
                             fail3
                               "Cannot instantiate %s (of type %s) to match goal (%s)"
                               uu____3482 uu____3483 uu____3484
                              in
                           try_unif uu____3468 uu____3479)))
         in
      FStar_All.pipe_left (wrap_err "apply") uu____3417
  
let (lemma_or_sq :
  FStar_Syntax_Syntax.comp ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun c  ->
    let ct = FStar_Syntax_Util.comp_to_comp_typ_nouniv c  in
    if
      FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
        FStar_Parser_Const.effect_Lemma_lid
    then
      let uu____3511 =
        match ct.FStar_Syntax_Syntax.effect_args with
        | pre::post::uu____3530 ->
            ((FStar_Pervasives_Native.fst pre),
              (FStar_Pervasives_Native.fst post))
        | uu____3571 -> failwith "apply_lemma: impossible: not a lemma"  in
      match uu____3511 with
      | (pre,post) ->
          let post1 =
            let uu____3607 =
              let uu____3616 =
                FStar_Syntax_Syntax.as_arg FStar_Syntax_Util.exp_unit  in
              [uu____3616]  in
            FStar_Syntax_Util.mk_app post uu____3607  in
          FStar_Pervasives_Native.Some (pre, post1)
    else
      if FStar_Syntax_Util.is_pure_effect ct.FStar_Syntax_Syntax.effect_name
      then
        (let uu____3636 =
           FStar_Syntax_Util.un_squash ct.FStar_Syntax_Syntax.result_typ  in
         FStar_Util.map_opt uu____3636
           (fun post  -> (FStar_Syntax_Util.t_true, post)))
      else FStar_Pervasives_Native.None
  
let (apply_lemma : FStar_Syntax_Syntax.term -> Prims.unit tac) =
  fun tm  ->
    let uu____3667 =
      let uu____3670 =
        mlog
          (fun uu____3675  ->
             let uu____3676 = FStar_Syntax_Print.term_to_string tm  in
             FStar_Util.print1 "apply_lemma: tm = %s\n" uu____3676)
          (fun uu____3680  ->
             let is_unit_t t =
               let uu____3685 =
                 let uu____3686 = FStar_Syntax_Subst.compress t  in
                 uu____3686.FStar_Syntax_Syntax.n  in
               match uu____3685 with
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.unit_lid
                   -> true
               | uu____3690 -> false  in
             let uu____3691 = cur_goal ()  in
             bind uu____3691
               (fun goal  ->
                  let uu____3697 = __tc goal.FStar_Tactics_Types.context tm
                     in
                  bind uu____3697
                    (fun uu____3720  ->
                       match uu____3720 with
                       | (tm1,t,guard) ->
                           let uu____3732 =
                             FStar_Syntax_Util.arrow_formals_comp t  in
                           (match uu____3732 with
                            | (bs,comp) ->
                                let uu____3759 = lemma_or_sq comp  in
                                (match uu____3759 with
                                 | FStar_Pervasives_Native.None  ->
                                     fail "not a lemma or squashed function"
                                 | FStar_Pervasives_Native.Some (pre,post) ->
                                     let uu____3778 =
                                       FStar_List.fold_left
                                         (fun uu____3824  ->
                                            fun uu____3825  ->
                                              match (uu____3824, uu____3825)
                                              with
                                              | ((uvs,guard1,subst1),(b,aq))
                                                  ->
                                                  let b_t =
                                                    FStar_Syntax_Subst.subst
                                                      subst1
                                                      b.FStar_Syntax_Syntax.sort
                                                     in
                                                  let uu____3928 =
                                                    is_unit_t b_t  in
                                                  if uu____3928
                                                  then
                                                    (((FStar_Syntax_Util.exp_unit,
                                                        aq) :: uvs), guard1,
                                                      ((FStar_Syntax_Syntax.NT
                                                          (b,
                                                            FStar_Syntax_Util.exp_unit))
                                                      :: subst1))
                                                  else
                                                    (let uu____3966 =
                                                       FStar_TypeChecker_Util.new_implicit_var
                                                         "apply_lemma"
                                                         (goal.FStar_Tactics_Types.goal_ty).FStar_Syntax_Syntax.pos
                                                         goal.FStar_Tactics_Types.context
                                                         b_t
                                                        in
                                                     match uu____3966 with
                                                     | (u,uu____3996,g_u) ->
                                                         let uu____4010 =
                                                           FStar_TypeChecker_Rel.conj_guard
                                                             guard1 g_u
                                                            in
                                                         (((u, aq) :: uvs),
                                                           uu____4010,
                                                           ((FStar_Syntax_Syntax.NT
                                                               (b, u)) ::
                                                           subst1))))
                                         ([], guard, []) bs
                                        in
                                     (match uu____3778 with
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
                                          let uu____4081 =
                                            let uu____4084 =
                                              FStar_Syntax_Util.mk_squash
                                                FStar_Syntax_Syntax.U_zero
                                                post1
                                               in
                                            do_unify
                                              goal.FStar_Tactics_Types.context
                                              uu____4084
                                              goal.FStar_Tactics_Types.goal_ty
                                             in
                                          bind uu____4081
                                            (fun b  ->
                                               if Prims.op_Negation b
                                               then
                                                 let uu____4092 =
                                                   tts
                                                     goal.FStar_Tactics_Types.context
                                                     tm1
                                                    in
                                                 let uu____4093 =
                                                   let uu____4094 =
                                                     FStar_Syntax_Util.mk_squash
                                                       FStar_Syntax_Syntax.U_zero
                                                       post1
                                                      in
                                                   tts
                                                     goal.FStar_Tactics_Types.context
                                                     uu____4094
                                                    in
                                                 let uu____4095 =
                                                   tts
                                                     goal.FStar_Tactics_Types.context
                                                     goal.FStar_Tactics_Types.goal_ty
                                                    in
                                                 fail3
                                                   "Cannot instantiate lemma %s (with postcondition: %s) to match goal (%s)"
                                                   uu____4092 uu____4093
                                                   uu____4095
                                               else
                                                 (let uu____4097 =
                                                    add_implicits
                                                      implicits.FStar_TypeChecker_Env.implicits
                                                     in
                                                  bind uu____4097
                                                    (fun uu____4102  ->
                                                       let uu____4103 =
                                                         solve goal
                                                           FStar_Syntax_Util.exp_unit
                                                          in
                                                       bind uu____4103
                                                         (fun uu____4111  ->
                                                            let is_free_uvar
                                                              uv t1 =
                                                              let free_uvars
                                                                =
                                                                let uu____4122
                                                                  =
                                                                  let uu____4129
                                                                    =
                                                                    FStar_Syntax_Free.uvars
                                                                    t1  in
                                                                  FStar_Util.set_elements
                                                                    uu____4129
                                                                   in
                                                                FStar_List.map
                                                                  FStar_Pervasives_Native.fst
                                                                  uu____4122
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
                                                                   is_free_uvar
                                                                    uv
                                                                    g'.FStar_Tactics_Types.goal_ty)
                                                                goals
                                                               in
                                                            let checkone t1
                                                              goals =
                                                              let uu____4170
                                                                =
                                                                FStar_Syntax_Util.head_and_args
                                                                  t1
                                                                 in
                                                              match uu____4170
                                                              with
                                                              | (hd1,uu____4186)
                                                                  ->
                                                                  (match 
                                                                    hd1.FStar_Syntax_Syntax.n
                                                                   with
                                                                   | 
                                                                   FStar_Syntax_Syntax.Tm_uvar
                                                                    (uv,uu____4208)
                                                                    ->
                                                                    appears
                                                                    uv goals
                                                                   | 
                                                                   uu____4233
                                                                    -> false)
                                                               in
                                                            let uu____4234 =
                                                              FStar_All.pipe_right
                                                                implicits.FStar_TypeChecker_Env.implicits
                                                                (mapM
                                                                   (fun
                                                                    uu____4306
                                                                     ->
                                                                    match uu____4306
                                                                    with
                                                                    | 
                                                                    (_msg,env,_uvar,term,typ,uu____4334)
                                                                    ->
                                                                    let uu____4335
                                                                    =
                                                                    FStar_Syntax_Util.head_and_args
                                                                    term  in
                                                                    (match uu____4335
                                                                    with
                                                                    | 
                                                                    (hd1,uu____4361)
                                                                    ->
                                                                    let uu____4382
                                                                    =
                                                                    let uu____4383
                                                                    =
                                                                    FStar_Syntax_Subst.compress
                                                                    hd1  in
                                                                    uu____4383.FStar_Syntax_Syntax.n
                                                                     in
                                                                    (match uu____4382
                                                                    with
                                                                    | 
                                                                    FStar_Syntax_Syntax.Tm_uvar
                                                                    uu____4396
                                                                    ->
                                                                    let uu____4413
                                                                    =
                                                                    let uu____4422
                                                                    =
                                                                    let uu____4425
                                                                    =
                                                                    let uu___98_4426
                                                                    = goal
                                                                     in
                                                                    let uu____4427
                                                                    =
                                                                    bnorm
                                                                    goal.FStar_Tactics_Types.context
                                                                    term  in
                                                                    let uu____4428
                                                                    =
                                                                    bnorm
                                                                    goal.FStar_Tactics_Types.context
                                                                    typ  in
                                                                    {
                                                                    FStar_Tactics_Types.context
                                                                    =
                                                                    (uu___98_4426.FStar_Tactics_Types.context);
                                                                    FStar_Tactics_Types.witness
                                                                    =
                                                                    uu____4427;
                                                                    FStar_Tactics_Types.goal_ty
                                                                    =
                                                                    uu____4428;
                                                                    FStar_Tactics_Types.opts
                                                                    =
                                                                    (uu___98_4426.FStar_Tactics_Types.opts);
                                                                    FStar_Tactics_Types.is_guard
                                                                    =
                                                                    (uu___98_4426.FStar_Tactics_Types.is_guard)
                                                                    }  in
                                                                    [uu____4425]
                                                                     in
                                                                    (uu____4422,
                                                                    [])  in
                                                                    ret
                                                                    uu____4413
                                                                    | 
                                                                    uu____4441
                                                                    ->
                                                                    let g_typ
                                                                    =
                                                                    let uu____4443
                                                                    =
                                                                    FStar_Options.__temp_fast_implicits
                                                                    ()  in
                                                                    if
                                                                    uu____4443
                                                                    then
                                                                    FStar_TypeChecker_TcTerm.check_type_of_well_typed_term
                                                                    false env
                                                                    term typ
                                                                    else
                                                                    (let term1
                                                                    =
                                                                    bnorm env
                                                                    term  in
                                                                    let uu____4446
                                                                    =
                                                                    let uu____4453
                                                                    =
                                                                    FStar_TypeChecker_Env.set_expected_typ
                                                                    env typ
                                                                     in
                                                                    env.FStar_TypeChecker_Env.type_of
                                                                    uu____4453
                                                                    term1  in
                                                                    match uu____4446
                                                                    with
                                                                    | 
                                                                    (uu____4454,uu____4455,g_typ)
                                                                    -> g_typ)
                                                                     in
                                                                    let uu____4457
                                                                    =
                                                                    goal_from_guard
                                                                    "apply_lemma solved arg"
                                                                    goal.FStar_Tactics_Types.context
                                                                    g_typ
                                                                    goal.FStar_Tactics_Types.opts
                                                                     in
                                                                    bind
                                                                    uu____4457
                                                                    (fun
                                                                    uu___62_4473
                                                                     ->
                                                                    match uu___62_4473
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
                                                            bind uu____4234
                                                              (fun goals_  ->
                                                                 let sub_goals
                                                                   =
                                                                   let uu____4541
                                                                    =
                                                                    FStar_List.map
                                                                    FStar_Pervasives_Native.fst
                                                                    goals_
                                                                     in
                                                                   FStar_List.flatten
                                                                    uu____4541
                                                                    in
                                                                 let smt_goals
                                                                   =
                                                                   let uu____4563
                                                                    =
                                                                    FStar_List.map
                                                                    FStar_Pervasives_Native.snd
                                                                    goals_
                                                                     in
                                                                   FStar_List.flatten
                                                                    uu____4563
                                                                    in
                                                                 let rec filter'
                                                                   a f xs =
                                                                   match xs
                                                                   with
                                                                   | 
                                                                   [] -> []
                                                                   | 
                                                                   x::xs1 ->
                                                                    let uu____4618
                                                                    = f x xs1
                                                                     in
                                                                    if
                                                                    uu____4618
                                                                    then
                                                                    let uu____4621
                                                                    =
                                                                    filter'
                                                                    () f xs1
                                                                     in x ::
                                                                    uu____4621
                                                                    else
                                                                    filter'
                                                                    () f xs1
                                                                    in
                                                                 let sub_goals1
                                                                   =
                                                                   Obj.magic
                                                                    (filter'
                                                                    ()
                                                                    (fun a439
                                                                     ->
                                                                    fun a440 
                                                                    ->
                                                                    (Obj.magic
                                                                    (fun g 
                                                                    ->
                                                                    fun goals
                                                                     ->
                                                                    let uu____4635
                                                                    =
                                                                    checkone
                                                                    g.FStar_Tactics_Types.witness
                                                                    goals  in
                                                                    Prims.op_Negation
                                                                    uu____4635))
                                                                    a439 a440)
                                                                    (Obj.magic
                                                                    sub_goals))
                                                                    in
                                                                 let uu____4636
                                                                   =
                                                                   proc_guard
                                                                    "apply_lemma guard"
                                                                    goal.FStar_Tactics_Types.context
                                                                    guard
                                                                    goal.FStar_Tactics_Types.opts
                                                                    in
                                                                 bind
                                                                   uu____4636
                                                                   (fun
                                                                    uu____4641
                                                                     ->
                                                                    let uu____4642
                                                                    =
                                                                    let uu____4645
                                                                    =
                                                                    let uu____4646
                                                                    =
                                                                    let uu____4647
                                                                    =
                                                                    FStar_Syntax_Util.mk_squash
                                                                    FStar_Syntax_Syntax.U_zero
                                                                    pre1  in
                                                                    istrivial
                                                                    goal.FStar_Tactics_Types.context
                                                                    uu____4647
                                                                     in
                                                                    Prims.op_Negation
                                                                    uu____4646
                                                                     in
                                                                    if
                                                                    uu____4645
                                                                    then
                                                                    add_irrelevant_goal
                                                                    "apply_lemma precondition"
                                                                    goal.FStar_Tactics_Types.context
                                                                    pre1
                                                                    goal.FStar_Tactics_Types.opts
                                                                    else
                                                                    ret ()
                                                                     in
                                                                    bind
                                                                    uu____4642
                                                                    (fun
                                                                    uu____4653
                                                                     ->
                                                                    let uu____4654
                                                                    =
                                                                    add_smt_goals
                                                                    smt_goals
                                                                     in
                                                                    bind
                                                                    uu____4654
                                                                    (fun
                                                                    uu____4658
                                                                     ->
                                                                    add_goals
                                                                    sub_goals1))))))))))))))
         in
      focus uu____3670  in
    FStar_All.pipe_left (wrap_err "apply_lemma") uu____3667
  
let (destruct_eq' :
  FStar_Reflection_Data.typ ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun typ  ->
    let uu____4678 = FStar_Syntax_Util.destruct_typ_as_formula typ  in
    match uu____4678 with
    | FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn
        (l,uu____4688::(e1,uu____4690)::(e2,uu____4692)::[])) when
        FStar_Ident.lid_equals l FStar_Parser_Const.eq2_lid ->
        FStar_Pervasives_Native.Some (e1, e2)
    | uu____4751 -> FStar_Pervasives_Native.None
  
let (destruct_eq :
  FStar_Reflection_Data.typ ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun typ  ->
    let uu____4773 = destruct_eq' typ  in
    match uu____4773 with
    | FStar_Pervasives_Native.Some t -> FStar_Pervasives_Native.Some t
    | FStar_Pervasives_Native.None  ->
        let uu____4803 = FStar_Syntax_Util.un_squash typ  in
        (match uu____4803 with
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
        let uu____4859 = FStar_TypeChecker_Env.pop_bv e1  in
        match uu____4859 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (bv',e') ->
            if FStar_Syntax_Syntax.bv_eq bvar bv'
            then FStar_Pervasives_Native.Some (e', [])
            else
              (let uu____4907 = aux e'  in
               FStar_Util.map_opt uu____4907
                 (fun uu____4931  ->
                    match uu____4931 with | (e'',bvs) -> (e'', (bv' :: bvs))))
         in
      let uu____4952 = aux e  in
      FStar_Util.map_opt uu____4952
        (fun uu____4976  ->
           match uu____4976 with | (e',bvs) -> (e', (FStar_List.rev bvs)))
  
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
          let uu____5031 = split_env b1 g.FStar_Tactics_Types.context  in
          FStar_Util.map_opt uu____5031
            (fun uu____5055  ->
               match uu____5055 with
               | (e0,bvs) ->
                   let s1 bv =
                     let uu___99_5072 = bv  in
                     let uu____5073 =
                       FStar_Syntax_Subst.subst s bv.FStar_Syntax_Syntax.sort
                        in
                     {
                       FStar_Syntax_Syntax.ppname =
                         (uu___99_5072.FStar_Syntax_Syntax.ppname);
                       FStar_Syntax_Syntax.index =
                         (uu___99_5072.FStar_Syntax_Syntax.index);
                       FStar_Syntax_Syntax.sort = uu____5073
                     }  in
                   let bvs1 = FStar_List.map s1 bvs  in
                   let c = push_bvs e0 (b2 :: bvs1)  in
                   let w =
                     FStar_Syntax_Subst.subst s g.FStar_Tactics_Types.witness
                      in
                   let t =
                     FStar_Syntax_Subst.subst s g.FStar_Tactics_Types.goal_ty
                      in
                   let uu___100_5082 = g  in
                   {
                     FStar_Tactics_Types.context = c;
                     FStar_Tactics_Types.witness = w;
                     FStar_Tactics_Types.goal_ty = t;
                     FStar_Tactics_Types.opts =
                       (uu___100_5082.FStar_Tactics_Types.opts);
                     FStar_Tactics_Types.is_guard =
                       (uu___100_5082.FStar_Tactics_Types.is_guard)
                   })
  
let (rewrite : FStar_Syntax_Syntax.binder -> Prims.unit tac) =
  fun h  ->
    let uu____5090 = cur_goal ()  in
    bind uu____5090
      (fun goal  ->
         let uu____5098 = h  in
         match uu____5098 with
         | (bv,uu____5102) ->
             mlog
               (fun uu____5106  ->
                  let uu____5107 = FStar_Syntax_Print.bv_to_string bv  in
                  let uu____5108 =
                    tts goal.FStar_Tactics_Types.context
                      bv.FStar_Syntax_Syntax.sort
                     in
                  FStar_Util.print2 "+++Rewrite %s : %s\n" uu____5107
                    uu____5108)
               (fun uu____5111  ->
                  let uu____5112 =
                    split_env bv goal.FStar_Tactics_Types.context  in
                  match uu____5112 with
                  | FStar_Pervasives_Native.None  ->
                      fail "rewrite: binder not found in environment"
                  | FStar_Pervasives_Native.Some (e0,bvs) ->
                      let uu____5141 =
                        destruct_eq bv.FStar_Syntax_Syntax.sort  in
                      (match uu____5141 with
                       | FStar_Pervasives_Native.Some (x,e) ->
                           let uu____5156 =
                             let uu____5157 = FStar_Syntax_Subst.compress x
                                in
                             uu____5157.FStar_Syntax_Syntax.n  in
                           (match uu____5156 with
                            | FStar_Syntax_Syntax.Tm_name x1 ->
                                let s = [FStar_Syntax_Syntax.NT (x1, e)]  in
                                let s1 bv1 =
                                  let uu___101_5170 = bv1  in
                                  let uu____5171 =
                                    FStar_Syntax_Subst.subst s
                                      bv1.FStar_Syntax_Syntax.sort
                                     in
                                  {
                                    FStar_Syntax_Syntax.ppname =
                                      (uu___101_5170.FStar_Syntax_Syntax.ppname);
                                    FStar_Syntax_Syntax.index =
                                      (uu___101_5170.FStar_Syntax_Syntax.index);
                                    FStar_Syntax_Syntax.sort = uu____5171
                                  }  in
                                let bvs1 = FStar_List.map s1 bvs  in
                                let uu____5177 =
                                  let uu___102_5178 = goal  in
                                  let uu____5179 = push_bvs e0 (bv :: bvs1)
                                     in
                                  let uu____5180 =
                                    FStar_Syntax_Subst.subst s
                                      goal.FStar_Tactics_Types.witness
                                     in
                                  let uu____5181 =
                                    FStar_Syntax_Subst.subst s
                                      goal.FStar_Tactics_Types.goal_ty
                                     in
                                  {
                                    FStar_Tactics_Types.context = uu____5179;
                                    FStar_Tactics_Types.witness = uu____5180;
                                    FStar_Tactics_Types.goal_ty = uu____5181;
                                    FStar_Tactics_Types.opts =
                                      (uu___102_5178.FStar_Tactics_Types.opts);
                                    FStar_Tactics_Types.is_guard =
                                      (uu___102_5178.FStar_Tactics_Types.is_guard)
                                  }  in
                                replace_cur uu____5177
                            | uu____5182 ->
                                fail
                                  "rewrite: Not an equality hypothesis with a variable on the LHS")
                       | uu____5183 ->
                           fail "rewrite: Not an equality hypothesis")))
  
let (rename_to :
  FStar_Syntax_Syntax.binder -> Prims.string -> Prims.unit tac) =
  fun b  ->
    fun s  ->
      let uu____5200 = cur_goal ()  in
      bind uu____5200
        (fun goal  ->
           let uu____5211 = b  in
           match uu____5211 with
           | (bv,uu____5215) ->
               let bv' =
                 FStar_Syntax_Syntax.freshen_bv
                   (let uu___103_5219 = bv  in
                    {
                      FStar_Syntax_Syntax.ppname =
                        (FStar_Ident.mk_ident
                           (s,
                             ((bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange)));
                      FStar_Syntax_Syntax.index =
                        (uu___103_5219.FStar_Syntax_Syntax.index);
                      FStar_Syntax_Syntax.sort =
                        (uu___103_5219.FStar_Syntax_Syntax.sort)
                    })
                  in
               let s1 =
                 let uu____5223 =
                   let uu____5224 =
                     let uu____5231 = FStar_Syntax_Syntax.bv_to_name bv'  in
                     (bv, uu____5231)  in
                   FStar_Syntax_Syntax.NT uu____5224  in
                 [uu____5223]  in
               let uu____5232 = subst_goal bv bv' s1 goal  in
               (match uu____5232 with
                | FStar_Pervasives_Native.None  ->
                    fail "rename_to: binder not found in environment"
                | FStar_Pervasives_Native.Some goal1 -> replace_cur goal1))
  
let (binder_retype : FStar_Syntax_Syntax.binder -> Prims.unit tac) =
  fun b  ->
    let uu____5245 = cur_goal ()  in
    bind uu____5245
      (fun goal  ->
         let uu____5254 = b  in
         match uu____5254 with
         | (bv,uu____5258) ->
             let uu____5259 = split_env bv goal.FStar_Tactics_Types.context
                in
             (match uu____5259 with
              | FStar_Pervasives_Native.None  ->
                  fail "binder_retype: binder is not present in environment"
              | FStar_Pervasives_Native.Some (e0,bvs) ->
                  let uu____5288 = FStar_Syntax_Util.type_u ()  in
                  (match uu____5288 with
                   | (ty,u) ->
                       let uu____5297 = new_uvar "binder_retype" e0 ty  in
                       bind uu____5297
                         (fun t'  ->
                            let bv'' =
                              let uu___104_5307 = bv  in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___104_5307.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___104_5307.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = t'
                              }  in
                            let s =
                              let uu____5311 =
                                let uu____5312 =
                                  let uu____5319 =
                                    FStar_Syntax_Syntax.bv_to_name bv''  in
                                  (bv, uu____5319)  in
                                FStar_Syntax_Syntax.NT uu____5312  in
                              [uu____5311]  in
                            let bvs1 =
                              FStar_List.map
                                (fun b1  ->
                                   let uu___105_5327 = b1  in
                                   let uu____5328 =
                                     FStar_Syntax_Subst.subst s
                                       b1.FStar_Syntax_Syntax.sort
                                      in
                                   {
                                     FStar_Syntax_Syntax.ppname =
                                       (uu___105_5327.FStar_Syntax_Syntax.ppname);
                                     FStar_Syntax_Syntax.index =
                                       (uu___105_5327.FStar_Syntax_Syntax.index);
                                     FStar_Syntax_Syntax.sort = uu____5328
                                   }) bvs
                               in
                            let env' = push_bvs e0 (bv'' :: bvs1)  in
                            bind __dismiss
                              (fun uu____5334  ->
                                 let uu____5335 =
                                   let uu____5338 =
                                     let uu____5341 =
                                       let uu___106_5342 = goal  in
                                       let uu____5343 =
                                         FStar_Syntax_Subst.subst s
                                           goal.FStar_Tactics_Types.witness
                                          in
                                       let uu____5344 =
                                         FStar_Syntax_Subst.subst s
                                           goal.FStar_Tactics_Types.goal_ty
                                          in
                                       {
                                         FStar_Tactics_Types.context = env';
                                         FStar_Tactics_Types.witness =
                                           uu____5343;
                                         FStar_Tactics_Types.goal_ty =
                                           uu____5344;
                                         FStar_Tactics_Types.opts =
                                           (uu___106_5342.FStar_Tactics_Types.opts);
                                         FStar_Tactics_Types.is_guard =
                                           (uu___106_5342.FStar_Tactics_Types.is_guard)
                                       }  in
                                     [uu____5341]  in
                                   add_goals uu____5338  in
                                 bind uu____5335
                                   (fun uu____5347  ->
                                      let uu____5348 =
                                        FStar_Syntax_Util.mk_eq2
                                          (FStar_Syntax_Syntax.U_succ u) ty
                                          bv.FStar_Syntax_Syntax.sort t'
                                         in
                                      add_irrelevant_goal
                                        "binder_retype equation" e0
                                        uu____5348
                                        goal.FStar_Tactics_Types.opts))))))
  
let (norm_binder_type :
  FStar_Syntax_Embeddings.norm_step Prims.list ->
    FStar_Syntax_Syntax.binder -> Prims.unit tac)
  =
  fun s  ->
    fun b  ->
      let uu____5363 = cur_goal ()  in
      bind uu____5363
        (fun goal  ->
           let uu____5372 = b  in
           match uu____5372 with
           | (bv,uu____5376) ->
               let uu____5377 = split_env bv goal.FStar_Tactics_Types.context
                  in
               (match uu____5377 with
                | FStar_Pervasives_Native.None  ->
                    fail
                      "binder_retype: binder is not present in environment"
                | FStar_Pervasives_Native.Some (e0,bvs) ->
                    let steps =
                      let uu____5409 =
                        FStar_TypeChecker_Normalize.tr_norm_steps s  in
                      FStar_List.append
                        [FStar_TypeChecker_Normalize.Reify;
                        FStar_TypeChecker_Normalize.UnfoldTac] uu____5409
                       in
                    let sort' =
                      normalize steps e0 bv.FStar_Syntax_Syntax.sort  in
                    let bv' =
                      let uu___107_5414 = bv  in
                      {
                        FStar_Syntax_Syntax.ppname =
                          (uu___107_5414.FStar_Syntax_Syntax.ppname);
                        FStar_Syntax_Syntax.index =
                          (uu___107_5414.FStar_Syntax_Syntax.index);
                        FStar_Syntax_Syntax.sort = sort'
                      }  in
                    let env' = push_bvs e0 (bv' :: bvs)  in
                    replace_cur
                      (let uu___108_5418 = goal  in
                       {
                         FStar_Tactics_Types.context = env';
                         FStar_Tactics_Types.witness =
                           (uu___108_5418.FStar_Tactics_Types.witness);
                         FStar_Tactics_Types.goal_ty =
                           (uu___108_5418.FStar_Tactics_Types.goal_ty);
                         FStar_Tactics_Types.opts =
                           (uu___108_5418.FStar_Tactics_Types.opts);
                         FStar_Tactics_Types.is_guard =
                           (uu___108_5418.FStar_Tactics_Types.is_guard)
                       })))
  
let (revert : Prims.unit -> Prims.unit tac) =
  fun uu____5423  ->
    let uu____5426 = cur_goal ()  in
    bind uu____5426
      (fun goal  ->
         let uu____5432 =
           FStar_TypeChecker_Env.pop_bv goal.FStar_Tactics_Types.context  in
         match uu____5432 with
         | FStar_Pervasives_Native.None  ->
             fail "Cannot revert; empty context"
         | FStar_Pervasives_Native.Some (x,env') ->
             let typ' =
               let uu____5454 =
                 FStar_Syntax_Syntax.mk_Total
                   goal.FStar_Tactics_Types.goal_ty
                  in
               FStar_Syntax_Util.arrow [(x, FStar_Pervasives_Native.None)]
                 uu____5454
                in
             let w' =
               FStar_Syntax_Util.abs [(x, FStar_Pervasives_Native.None)]
                 goal.FStar_Tactics_Types.witness
                 FStar_Pervasives_Native.None
                in
             replace_cur
               (let uu___109_5488 = goal  in
                {
                  FStar_Tactics_Types.context = env';
                  FStar_Tactics_Types.witness = w';
                  FStar_Tactics_Types.goal_ty = typ';
                  FStar_Tactics_Types.opts =
                    (uu___109_5488.FStar_Tactics_Types.opts);
                  FStar_Tactics_Types.is_guard =
                    (uu___109_5488.FStar_Tactics_Types.is_guard)
                }))
  
let (free_in :
  FStar_Syntax_Syntax.bv -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun bv  ->
    fun t  ->
      let uu____5495 = FStar_Syntax_Free.names t  in
      FStar_Util.set_mem bv uu____5495
  
let rec (clear : FStar_Syntax_Syntax.binder -> Prims.unit tac) =
  fun b  ->
    let bv = FStar_Pervasives_Native.fst b  in
    let uu____5506 = cur_goal ()  in
    bind uu____5506
      (fun goal  ->
         mlog
           (fun uu____5514  ->
              let uu____5515 = FStar_Syntax_Print.binder_to_string b  in
              let uu____5516 =
                let uu____5517 =
                  let uu____5518 =
                    FStar_TypeChecker_Env.all_binders
                      goal.FStar_Tactics_Types.context
                     in
                  FStar_All.pipe_right uu____5518 FStar_List.length  in
                FStar_All.pipe_right uu____5517 FStar_Util.string_of_int  in
              FStar_Util.print2 "Clear of (%s), env has %s binders\n"
                uu____5515 uu____5516)
           (fun uu____5529  ->
              let uu____5530 = split_env bv goal.FStar_Tactics_Types.context
                 in
              match uu____5530 with
              | FStar_Pervasives_Native.None  ->
                  fail "Cannot clear; binder not in environment"
              | FStar_Pervasives_Native.Some (e',bvs) ->
                  let rec check1 bvs1 =
                    match bvs1 with
                    | [] -> ret ()
                    | bv'::bvs2 ->
                        let uu____5575 =
                          free_in bv bv'.FStar_Syntax_Syntax.sort  in
                        if uu____5575
                        then
                          let uu____5578 =
                            let uu____5579 =
                              FStar_Syntax_Print.bv_to_string bv'  in
                            FStar_Util.format1
                              "Cannot clear; binder present in the type of %s"
                              uu____5579
                             in
                          fail uu____5578
                        else check1 bvs2
                     in
                  let uu____5581 =
                    free_in bv goal.FStar_Tactics_Types.goal_ty  in
                  if uu____5581
                  then fail "Cannot clear; binder present in goal"
                  else
                    (let uu____5585 = check1 bvs  in
                     bind uu____5585
                       (fun uu____5591  ->
                          let env' = push_bvs e' bvs  in
                          let uu____5593 =
                            new_uvar "clear.witness" env'
                              goal.FStar_Tactics_Types.goal_ty
                             in
                          bind uu____5593
                            (fun ut  ->
                               let uu____5599 =
                                 do_unify goal.FStar_Tactics_Types.context
                                   goal.FStar_Tactics_Types.witness ut
                                  in
                               bind uu____5599
                                 (fun b1  ->
                                    if b1
                                    then
                                      replace_cur
                                        (let uu___110_5608 = goal  in
                                         {
                                           FStar_Tactics_Types.context = env';
                                           FStar_Tactics_Types.witness = ut;
                                           FStar_Tactics_Types.goal_ty =
                                             (uu___110_5608.FStar_Tactics_Types.goal_ty);
                                           FStar_Tactics_Types.opts =
                                             (uu___110_5608.FStar_Tactics_Types.opts);
                                           FStar_Tactics_Types.is_guard =
                                             (uu___110_5608.FStar_Tactics_Types.is_guard)
                                         })
                                    else
                                      fail
                                        "Cannot clear; binder appears in witness"))))))
  
let (clear_top : Prims.unit -> Prims.unit tac) =
  fun uu____5614  ->
    let uu____5617 = cur_goal ()  in
    bind uu____5617
      (fun goal  ->
         let uu____5623 =
           FStar_TypeChecker_Env.pop_bv goal.FStar_Tactics_Types.context  in
         match uu____5623 with
         | FStar_Pervasives_Native.None  ->
             fail "Cannot clear; empty context"
         | FStar_Pervasives_Native.Some (x,uu____5637) ->
             let uu____5642 = FStar_Syntax_Syntax.mk_binder x  in
             clear uu____5642)
  
let (prune : Prims.string -> Prims.unit tac) =
  fun s  ->
    let uu____5650 = cur_goal ()  in
    bind uu____5650
      (fun g  ->
         let ctx = g.FStar_Tactics_Types.context  in
         let ctx' =
           FStar_TypeChecker_Env.rem_proof_ns ctx
             (FStar_Ident.path_of_text s)
            in
         let g' =
           let uu___111_5661 = g  in
           {
             FStar_Tactics_Types.context = ctx';
             FStar_Tactics_Types.witness =
               (uu___111_5661.FStar_Tactics_Types.witness);
             FStar_Tactics_Types.goal_ty =
               (uu___111_5661.FStar_Tactics_Types.goal_ty);
             FStar_Tactics_Types.opts =
               (uu___111_5661.FStar_Tactics_Types.opts);
             FStar_Tactics_Types.is_guard =
               (uu___111_5661.FStar_Tactics_Types.is_guard)
           }  in
         bind __dismiss (fun uu____5663  -> add_goals [g']))
  
let (addns : Prims.string -> Prims.unit tac) =
  fun s  ->
    let uu____5671 = cur_goal ()  in
    bind uu____5671
      (fun g  ->
         let ctx = g.FStar_Tactics_Types.context  in
         let ctx' =
           FStar_TypeChecker_Env.add_proof_ns ctx
             (FStar_Ident.path_of_text s)
            in
         let g' =
           let uu___112_5682 = g  in
           {
             FStar_Tactics_Types.context = ctx';
             FStar_Tactics_Types.witness =
               (uu___112_5682.FStar_Tactics_Types.witness);
             FStar_Tactics_Types.goal_ty =
               (uu___112_5682.FStar_Tactics_Types.goal_ty);
             FStar_Tactics_Types.opts =
               (uu___112_5682.FStar_Tactics_Types.opts);
             FStar_Tactics_Types.is_guard =
               (uu___112_5682.FStar_Tactics_Types.is_guard)
           }  in
         bind __dismiss (fun uu____5684  -> add_goals [g']))
  
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
            let uu____5716 = FStar_Syntax_Subst.compress t  in
            uu____5716.FStar_Syntax_Syntax.n  in
          let uu____5719 =
            if d = FStar_Tactics_Types.TopDown
            then
              f env
                (let uu___116_5725 = t  in
                 {
                   FStar_Syntax_Syntax.n = tn;
                   FStar_Syntax_Syntax.pos =
                     (uu___116_5725.FStar_Syntax_Syntax.pos);
                   FStar_Syntax_Syntax.vars =
                     (uu___116_5725.FStar_Syntax_Syntax.vars)
                 })
            else ret t  in
          bind uu____5719
            (fun t1  ->
               let ff = tac_fold_env d f env  in
               let tn1 =
                 let uu____5739 =
                   let uu____5740 = FStar_Syntax_Subst.compress t1  in
                   uu____5740.FStar_Syntax_Syntax.n  in
                 match uu____5739 with
                 | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
                     let uu____5767 = ff hd1  in
                     bind uu____5767
                       (fun hd2  ->
                          let fa uu____5787 =
                            match uu____5787 with
                            | (a,q) ->
                                let uu____5800 = ff a  in
                                bind uu____5800 (fun a1  -> ret (a1, q))
                             in
                          let uu____5813 = mapM fa args  in
                          bind uu____5813
                            (fun args1  ->
                               ret (FStar_Syntax_Syntax.Tm_app (hd2, args1))))
                 | FStar_Syntax_Syntax.Tm_abs (bs,t2,k) ->
                     let uu____5873 = FStar_Syntax_Subst.open_term bs t2  in
                     (match uu____5873 with
                      | (bs1,t') ->
                          let uu____5882 =
                            let uu____5885 =
                              FStar_TypeChecker_Env.push_binders env bs1  in
                            tac_fold_env d f uu____5885 t'  in
                          bind uu____5882
                            (fun t''  ->
                               let uu____5889 =
                                 let uu____5890 =
                                   let uu____5907 =
                                     FStar_Syntax_Subst.close_binders bs1  in
                                   let uu____5908 =
                                     FStar_Syntax_Subst.close bs1 t''  in
                                   (uu____5907, uu____5908, k)  in
                                 FStar_Syntax_Syntax.Tm_abs uu____5890  in
                               ret uu____5889))
                 | FStar_Syntax_Syntax.Tm_arrow (bs,k) -> ret tn
                 | FStar_Syntax_Syntax.Tm_match (hd1,brs) ->
                     let uu____5967 = ff hd1  in
                     bind uu____5967
                       (fun hd2  ->
                          let ffb br =
                            let uu____5980 =
                              FStar_Syntax_Subst.open_branch br  in
                            match uu____5980 with
                            | (pat,w,e) ->
                                let uu____6002 = ff e  in
                                bind uu____6002
                                  (fun e1  ->
                                     let br1 =
                                       FStar_Syntax_Subst.close_branch
                                         (pat, w, e1)
                                        in
                                     ret br1)
                             in
                          let uu____6015 = mapM ffb brs  in
                          bind uu____6015
                            (fun brs1  ->
                               ret (FStar_Syntax_Syntax.Tm_match (hd2, brs1))))
                 | FStar_Syntax_Syntax.Tm_let
                     ((false
                       ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inl bv;
                          FStar_Syntax_Syntax.lbunivs = uu____6029;
                          FStar_Syntax_Syntax.lbtyp = uu____6030;
                          FStar_Syntax_Syntax.lbeff = uu____6031;
                          FStar_Syntax_Syntax.lbdef = def;
                          FStar_Syntax_Syntax.lbattrs = uu____6033;
                          FStar_Syntax_Syntax.lbpos = uu____6034;_}::[]),e)
                     ->
                     let lb =
                       let uu____6059 =
                         let uu____6060 = FStar_Syntax_Subst.compress t1  in
                         uu____6060.FStar_Syntax_Syntax.n  in
                       match uu____6059 with
                       | FStar_Syntax_Syntax.Tm_let
                           ((false ,lb::[]),uu____6064) -> lb
                       | uu____6077 -> failwith "impossible"  in
                     let fflb lb1 =
                       let uu____6084 = ff lb1.FStar_Syntax_Syntax.lbdef  in
                       bind uu____6084
                         (fun def1  ->
                            ret
                              (let uu___113_6090 = lb1  in
                               {
                                 FStar_Syntax_Syntax.lbname =
                                   (uu___113_6090.FStar_Syntax_Syntax.lbname);
                                 FStar_Syntax_Syntax.lbunivs =
                                   (uu___113_6090.FStar_Syntax_Syntax.lbunivs);
                                 FStar_Syntax_Syntax.lbtyp =
                                   (uu___113_6090.FStar_Syntax_Syntax.lbtyp);
                                 FStar_Syntax_Syntax.lbeff =
                                   (uu___113_6090.FStar_Syntax_Syntax.lbeff);
                                 FStar_Syntax_Syntax.lbdef = def1;
                                 FStar_Syntax_Syntax.lbattrs =
                                   (uu___113_6090.FStar_Syntax_Syntax.lbattrs);
                                 FStar_Syntax_Syntax.lbpos =
                                   (uu___113_6090.FStar_Syntax_Syntax.lbpos)
                               }))
                        in
                     let uu____6091 = fflb lb  in
                     bind uu____6091
                       (fun lb1  ->
                          let uu____6100 =
                            let uu____6105 =
                              let uu____6106 =
                                FStar_Syntax_Syntax.mk_binder bv  in
                              [uu____6106]  in
                            FStar_Syntax_Subst.open_term uu____6105 e  in
                          match uu____6100 with
                          | (bs,e1) ->
                              let uu____6111 = ff e1  in
                              bind uu____6111
                                (fun e2  ->
                                   let e3 = FStar_Syntax_Subst.close bs e2
                                      in
                                   ret
                                     (FStar_Syntax_Syntax.Tm_let
                                        ((false, [lb1]), e3))))
                 | FStar_Syntax_Syntax.Tm_let ((true ,lbs),e) ->
                     let fflb lb =
                       let uu____6148 = ff lb.FStar_Syntax_Syntax.lbdef  in
                       bind uu____6148
                         (fun def  ->
                            ret
                              (let uu___114_6154 = lb  in
                               {
                                 FStar_Syntax_Syntax.lbname =
                                   (uu___114_6154.FStar_Syntax_Syntax.lbname);
                                 FStar_Syntax_Syntax.lbunivs =
                                   (uu___114_6154.FStar_Syntax_Syntax.lbunivs);
                                 FStar_Syntax_Syntax.lbtyp =
                                   (uu___114_6154.FStar_Syntax_Syntax.lbtyp);
                                 FStar_Syntax_Syntax.lbeff =
                                   (uu___114_6154.FStar_Syntax_Syntax.lbeff);
                                 FStar_Syntax_Syntax.lbdef = def;
                                 FStar_Syntax_Syntax.lbattrs =
                                   (uu___114_6154.FStar_Syntax_Syntax.lbattrs);
                                 FStar_Syntax_Syntax.lbpos =
                                   (uu___114_6154.FStar_Syntax_Syntax.lbpos)
                               }))
                        in
                     let uu____6155 = FStar_Syntax_Subst.open_let_rec lbs e
                        in
                     (match uu____6155 with
                      | (lbs1,e1) ->
                          let uu____6170 = mapM fflb lbs1  in
                          bind uu____6170
                            (fun lbs2  ->
                               let uu____6182 = ff e1  in
                               bind uu____6182
                                 (fun e2  ->
                                    let uu____6190 =
                                      FStar_Syntax_Subst.close_let_rec lbs2
                                        e2
                                       in
                                    match uu____6190 with
                                    | (lbs3,e3) ->
                                        ret
                                          (FStar_Syntax_Syntax.Tm_let
                                             ((true, lbs3), e3)))))
                 | FStar_Syntax_Syntax.Tm_ascribed (t2,asc,eff) ->
                     let uu____6256 = ff t2  in
                     bind uu____6256
                       (fun t3  ->
                          ret
                            (FStar_Syntax_Syntax.Tm_ascribed (t3, asc, eff)))
                 | FStar_Syntax_Syntax.Tm_meta (t2,m) ->
                     let uu____6285 = ff t2  in
                     bind uu____6285
                       (fun t3  -> ret (FStar_Syntax_Syntax.Tm_meta (t3, m)))
                 | uu____6290 -> ret tn  in
               bind tn1
                 (fun tn2  ->
                    let t' =
                      let uu___115_6297 = t1  in
                      {
                        FStar_Syntax_Syntax.n = tn2;
                        FStar_Syntax_Syntax.pos =
                          (uu___115_6297.FStar_Syntax_Syntax.pos);
                        FStar_Syntax_Syntax.vars =
                          (uu___115_6297.FStar_Syntax_Syntax.vars)
                      }  in
                    if d = FStar_Tactics_Types.BottomUp
                    then f env t'
                    else ret t'))
  
let (pointwise_rec :
  FStar_Tactics_Types.proofstate ->
    Prims.unit tac ->
      FStar_Options.optionstate ->
        FStar_TypeChecker_Env.env ->
          FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term tac)
  =
  fun ps  ->
    fun tau  ->
      fun opts  ->
        fun env  ->
          fun t  ->
            let uu____6326 = FStar_TypeChecker_TcTerm.tc_term env t  in
            match uu____6326 with
            | (t1,lcomp,g) ->
                let uu____6338 =
                  (let uu____6341 =
                     FStar_Syntax_Util.is_pure_or_ghost_lcomp lcomp  in
                   Prims.op_Negation uu____6341) ||
                    (let uu____6343 = FStar_TypeChecker_Rel.is_trivial g  in
                     Prims.op_Negation uu____6343)
                   in
                if uu____6338
                then ret t1
                else
                  (let rewrite_eq =
                     let typ = lcomp.FStar_Syntax_Syntax.res_typ  in
                     let uu____6353 = new_uvar "pointwise_rec" env typ  in
                     bind uu____6353
                       (fun ut  ->
                          log ps
                            (fun uu____6364  ->
                               let uu____6365 =
                                 FStar_Syntax_Print.term_to_string t1  in
                               let uu____6366 =
                                 FStar_Syntax_Print.term_to_string ut  in
                               FStar_Util.print2
                                 "Pointwise_rec: making equality\n\t%s ==\n\t%s\n"
                                 uu____6365 uu____6366);
                          (let uu____6367 =
                             let uu____6370 =
                               let uu____6371 =
                                 FStar_TypeChecker_TcTerm.universe_of env typ
                                  in
                               FStar_Syntax_Util.mk_eq2 uu____6371 typ t1 ut
                                in
                             add_irrelevant_goal "pointwise_rec equation" env
                               uu____6370 opts
                              in
                           bind uu____6367
                             (fun uu____6374  ->
                                let uu____6375 =
                                  bind tau
                                    (fun uu____6381  ->
                                       let ut1 =
                                         FStar_TypeChecker_Normalize.reduce_uvar_solutions
                                           env ut
                                          in
                                       log ps
                                         (fun uu____6387  ->
                                            let uu____6388 =
                                              FStar_Syntax_Print.term_to_string
                                                t1
                                               in
                                            let uu____6389 =
                                              FStar_Syntax_Print.term_to_string
                                                ut1
                                               in
                                            FStar_Util.print2
                                              "Pointwise_rec: succeeded rewriting\n\t%s to\n\t%s\n"
                                              uu____6388 uu____6389);
                                       ret ut1)
                                   in
                                focus uu____6375)))
                      in
                   let uu____6390 = trytac' rewrite_eq  in
                   bind uu____6390
                     (fun x  ->
                        match x with
                        | FStar_Util.Inl "SKIP" -> ret t1
                        | FStar_Util.Inl e -> fail e
                        | FStar_Util.Inr x1 -> ret x1))
  
type ctrl = FStar_BigInt.t[@@deriving show]
let (keepGoing : ctrl) = FStar_BigInt.zero 
let (proceedToNextSubtree : FStar_BigInt.bigint) = FStar_BigInt.one 
let (globalStop : FStar_BigInt.bigint) =
  FStar_BigInt.succ_big_int FStar_BigInt.one 
type rewrite_result = Prims.bool[@@deriving show]
let (skipThisTerm : Prims.bool) = false 
let (rewroteThisTerm : Prims.bool) = true 
type 'a ctrl_tac = ('a,ctrl) FStar_Pervasives_Native.tuple2 tac[@@deriving
                                                                 show]
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
          let uu____6538 = FStar_Syntax_Subst.compress t  in
          maybe_continue ctrl uu____6538
            (fun t1  ->
               let uu____6542 =
                 f env
                   (let uu___119_6551 = t1  in
                    {
                      FStar_Syntax_Syntax.n = (t1.FStar_Syntax_Syntax.n);
                      FStar_Syntax_Syntax.pos =
                        (uu___119_6551.FStar_Syntax_Syntax.pos);
                      FStar_Syntax_Syntax.vars =
                        (uu___119_6551.FStar_Syntax_Syntax.vars)
                    })
                  in
               bind uu____6542
                 (fun uu____6563  ->
                    match uu____6563 with
                    | (t2,ctrl1) ->
                        maybe_continue ctrl1 t2
                          (fun t3  ->
                             let uu____6582 =
                               let uu____6583 =
                                 FStar_Syntax_Subst.compress t3  in
                               uu____6583.FStar_Syntax_Syntax.n  in
                             match uu____6582 with
                             | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
                                 let uu____6616 =
                                   ctrl_tac_fold f env ctrl1 hd1  in
                                 bind uu____6616
                                   (fun uu____6641  ->
                                      match uu____6641 with
                                      | (hd2,ctrl2) ->
                                          let ctrl3 = keep_going ctrl2  in
                                          let uu____6657 =
                                            ctrl_tac_fold_args f env ctrl3
                                              args
                                             in
                                          bind uu____6657
                                            (fun uu____6684  ->
                                               match uu____6684 with
                                               | (args1,ctrl4) ->
                                                   ret
                                                     ((let uu___117_6714 = t3
                                                          in
                                                       {
                                                         FStar_Syntax_Syntax.n
                                                           =
                                                           (FStar_Syntax_Syntax.Tm_app
                                                              (hd2, args1));
                                                         FStar_Syntax_Syntax.pos
                                                           =
                                                           (uu___117_6714.FStar_Syntax_Syntax.pos);
                                                         FStar_Syntax_Syntax.vars
                                                           =
                                                           (uu___117_6714.FStar_Syntax_Syntax.vars)
                                                       }), ctrl4)))
                             | FStar_Syntax_Syntax.Tm_abs (bs,t4,k) ->
                                 let uu____6740 =
                                   FStar_Syntax_Subst.open_term bs t4  in
                                 (match uu____6740 with
                                  | (bs1,t') ->
                                      let uu____6755 =
                                        let uu____6762 =
                                          FStar_TypeChecker_Env.push_binders
                                            env bs1
                                           in
                                        ctrl_tac_fold f uu____6762 ctrl1 t'
                                         in
                                      bind uu____6755
                                        (fun uu____6780  ->
                                           match uu____6780 with
                                           | (t'',ctrl2) ->
                                               let uu____6795 =
                                                 let uu____6802 =
                                                   let uu___118_6805 = t4  in
                                                   let uu____6808 =
                                                     let uu____6809 =
                                                       let uu____6826 =
                                                         FStar_Syntax_Subst.close_binders
                                                           bs1
                                                          in
                                                       let uu____6827 =
                                                         FStar_Syntax_Subst.close
                                                           bs1 t''
                                                          in
                                                       (uu____6826,
                                                         uu____6827, k)
                                                        in
                                                     FStar_Syntax_Syntax.Tm_abs
                                                       uu____6809
                                                      in
                                                   {
                                                     FStar_Syntax_Syntax.n =
                                                       uu____6808;
                                                     FStar_Syntax_Syntax.pos
                                                       =
                                                       (uu___118_6805.FStar_Syntax_Syntax.pos);
                                                     FStar_Syntax_Syntax.vars
                                                       =
                                                       (uu___118_6805.FStar_Syntax_Syntax.vars)
                                                   }  in
                                                 (uu____6802, ctrl2)  in
                                               ret uu____6795))
                             | FStar_Syntax_Syntax.Tm_arrow (bs,k) ->
                                 ret (t3, ctrl1)
                             | uu____6860 -> ret (t3, ctrl1))))

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
              let uu____6911 = ctrl_tac_fold f env ctrl t  in
              bind uu____6911
                (fun uu____6939  ->
                   match uu____6939 with
                   | (t1,ctrl1) ->
                       let uu____6958 = ctrl_tac_fold_args f env ctrl1 ts1
                          in
                       bind uu____6958
                         (fun uu____6989  ->
                            match uu____6989 with
                            | (ts2,ctrl2) -> ret (((t1, q) :: ts2), ctrl2)))

let (rewrite_rec :
  FStar_Tactics_Types.proofstate ->
    (FStar_Syntax_Syntax.term -> rewrite_result ctrl_tac) ->
      Prims.unit tac ->
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
              let uu____7073 =
                let uu____7080 =
                  add_irrelevant_goal "dummy" env FStar_Syntax_Util.t_true
                    opts
                   in
                bind uu____7080
                  (fun uu____7089  ->
                     let uu____7090 = ctrl t1  in
                     bind uu____7090
                       (fun res  ->
                          let uu____7113 = trivial ()  in
                          bind uu____7113 (fun uu____7121  -> ret res)))
                 in
              bind uu____7073
                (fun uu____7137  ->
                   match uu____7137 with
                   | (should_rewrite,ctrl1) ->
                       if Prims.op_Negation should_rewrite
                       then ret (t1, ctrl1)
                       else
                         (let uu____7161 =
                            FStar_TypeChecker_TcTerm.tc_term env t1  in
                          match uu____7161 with
                          | (t2,lcomp,g) ->
                              let uu____7177 =
                                (let uu____7180 =
                                   FStar_Syntax_Util.is_pure_or_ghost_lcomp
                                     lcomp
                                    in
                                 Prims.op_Negation uu____7180) ||
                                  (let uu____7182 =
                                     FStar_TypeChecker_Rel.is_trivial g  in
                                   Prims.op_Negation uu____7182)
                                 in
                              if uu____7177
                              then ret (t2, globalStop)
                              else
                                (let typ = lcomp.FStar_Syntax_Syntax.res_typ
                                    in
                                 let uu____7197 =
                                   new_uvar "pointwise_rec" env typ  in
                                 bind uu____7197
                                   (fun ut  ->
                                      log ps
                                        (fun uu____7212  ->
                                           let uu____7213 =
                                             FStar_Syntax_Print.term_to_string
                                               t2
                                              in
                                           let uu____7214 =
                                             FStar_Syntax_Print.term_to_string
                                               ut
                                              in
                                           FStar_Util.print2
                                             "Pointwise_rec: making equality\n\t%s ==\n\t%s\n"
                                             uu____7213 uu____7214);
                                      (let uu____7215 =
                                         let uu____7218 =
                                           let uu____7219 =
                                             FStar_TypeChecker_TcTerm.universe_of
                                               env typ
                                              in
                                           FStar_Syntax_Util.mk_eq2
                                             uu____7219 typ t2 ut
                                            in
                                         add_irrelevant_goal
                                           "rewrite_rec equation" env
                                           uu____7218 opts
                                          in
                                       bind uu____7215
                                         (fun uu____7226  ->
                                            let uu____7227 =
                                              bind rewriter
                                                (fun uu____7241  ->
                                                   let ut1 =
                                                     FStar_TypeChecker_Normalize.reduce_uvar_solutions
                                                       env ut
                                                      in
                                                   log ps
                                                     (fun uu____7247  ->
                                                        let uu____7248 =
                                                          FStar_Syntax_Print.term_to_string
                                                            t2
                                                           in
                                                        let uu____7249 =
                                                          FStar_Syntax_Print.term_to_string
                                                            ut1
                                                           in
                                                        FStar_Util.print2
                                                          "rewrite_rec: succeeded rewriting\n\t%s to\n\t%s\n"
                                                          uu____7248
                                                          uu____7249);
                                                   ret (ut1, ctrl1))
                                               in
                                            focus uu____7227))))))
  
let (topdown_rewrite :
  (FStar_Syntax_Syntax.term ->
     (Prims.bool,FStar_BigInt.t) FStar_Pervasives_Native.tuple2 tac)
    -> Prims.unit tac -> Prims.unit tac)
  =
  fun ctrl  ->
    fun rewriter  ->
      bind get
        (fun ps  ->
           let uu____7293 =
             match ps.FStar_Tactics_Types.goals with
             | g::gs -> (g, gs)
             | [] -> failwith "Pointwise: no goals"  in
           match uu____7293 with
           | (g,gs) ->
               let gt1 = g.FStar_Tactics_Types.goal_ty  in
               (log ps
                  (fun uu____7330  ->
                     let uu____7331 = FStar_Syntax_Print.term_to_string gt1
                        in
                     FStar_Util.print1 "Pointwise starting with %s\n"
                       uu____7331);
                bind dismiss_all
                  (fun uu____7334  ->
                     let uu____7335 =
                       ctrl_tac_fold
                         (rewrite_rec ps ctrl rewriter
                            g.FStar_Tactics_Types.opts)
                         g.FStar_Tactics_Types.context keepGoing gt1
                        in
                     bind uu____7335
                       (fun uu____7353  ->
                          match uu____7353 with
                          | (gt',uu____7361) ->
                              (log ps
                                 (fun uu____7365  ->
                                    let uu____7366 =
                                      FStar_Syntax_Print.term_to_string gt'
                                       in
                                    FStar_Util.print1
                                      "Pointwise seems to have succeded with %s\n"
                                      uu____7366);
                               (let uu____7367 = push_goals gs  in
                                bind uu____7367
                                  (fun uu____7371  ->
                                     add_goals
                                       [(let uu___120_7373 = g  in
                                         {
                                           FStar_Tactics_Types.context =
                                             (uu___120_7373.FStar_Tactics_Types.context);
                                           FStar_Tactics_Types.witness =
                                             (uu___120_7373.FStar_Tactics_Types.witness);
                                           FStar_Tactics_Types.goal_ty = gt';
                                           FStar_Tactics_Types.opts =
                                             (uu___120_7373.FStar_Tactics_Types.opts);
                                           FStar_Tactics_Types.is_guard =
                                             (uu___120_7373.FStar_Tactics_Types.is_guard)
                                         })])))))))
  
let (pointwise :
  FStar_Tactics_Types.direction -> Prims.unit tac -> Prims.unit tac) =
  fun d  ->
    fun tau  ->
      bind get
        (fun ps  ->
           let uu____7395 =
             match ps.FStar_Tactics_Types.goals with
             | g::gs -> (g, gs)
             | [] -> failwith "Pointwise: no goals"  in
           match uu____7395 with
           | (g,gs) ->
               let gt1 = g.FStar_Tactics_Types.goal_ty  in
               (log ps
                  (fun uu____7432  ->
                     let uu____7433 = FStar_Syntax_Print.term_to_string gt1
                        in
                     FStar_Util.print1 "Pointwise starting with %s\n"
                       uu____7433);
                bind dismiss_all
                  (fun uu____7436  ->
                     let uu____7437 =
                       tac_fold_env d
                         (pointwise_rec ps tau g.FStar_Tactics_Types.opts)
                         g.FStar_Tactics_Types.context gt1
                        in
                     bind uu____7437
                       (fun gt'  ->
                          log ps
                            (fun uu____7447  ->
                               let uu____7448 =
                                 FStar_Syntax_Print.term_to_string gt'  in
                               FStar_Util.print1
                                 "Pointwise seems to have succeded with %s\n"
                                 uu____7448);
                          (let uu____7449 = push_goals gs  in
                           bind uu____7449
                             (fun uu____7453  ->
                                add_goals
                                  [(let uu___121_7455 = g  in
                                    {
                                      FStar_Tactics_Types.context =
                                        (uu___121_7455.FStar_Tactics_Types.context);
                                      FStar_Tactics_Types.witness =
                                        (uu___121_7455.FStar_Tactics_Types.witness);
                                      FStar_Tactics_Types.goal_ty = gt';
                                      FStar_Tactics_Types.opts =
                                        (uu___121_7455.FStar_Tactics_Types.opts);
                                      FStar_Tactics_Types.is_guard =
                                        (uu___121_7455.FStar_Tactics_Types.is_guard)
                                    })]))))))
  
let (trefl : Prims.unit -> Prims.unit tac) =
  fun uu____7460  ->
    let uu____7463 = cur_goal ()  in
    bind uu____7463
      (fun g  ->
         let uu____7481 =
           FStar_Syntax_Util.un_squash g.FStar_Tactics_Types.goal_ty  in
         match uu____7481 with
         | FStar_Pervasives_Native.Some t ->
             let uu____7493 = FStar_Syntax_Util.head_and_args' t  in
             (match uu____7493 with
              | (hd1,args) ->
                  let uu____7526 =
                    let uu____7539 =
                      let uu____7540 = FStar_Syntax_Util.un_uinst hd1  in
                      uu____7540.FStar_Syntax_Syntax.n  in
                    (uu____7539, args)  in
                  (match uu____7526 with
                   | (FStar_Syntax_Syntax.Tm_fvar
                      fv,uu____7554::(l,uu____7556)::(r,uu____7558)::[]) when
                       FStar_Syntax_Syntax.fv_eq_lid fv
                         FStar_Parser_Const.eq2_lid
                       ->
                       let uu____7605 =
                         do_unify g.FStar_Tactics_Types.context l r  in
                       bind uu____7605
                         (fun b  ->
                            if Prims.op_Negation b
                            then
                              let uu____7614 =
                                tts g.FStar_Tactics_Types.context l  in
                              let uu____7615 =
                                tts g.FStar_Tactics_Types.context r  in
                              fail2
                                "trefl: not a trivial equality (%s vs %s)"
                                uu____7614 uu____7615
                            else solve g FStar_Syntax_Util.exp_unit)
                   | (hd2,uu____7618) ->
                       let uu____7635 = tts g.FStar_Tactics_Types.context t
                          in
                       fail1 "trefl: not an equality (%s)" uu____7635))
         | FStar_Pervasives_Native.None  -> fail "not an irrelevant goal")
  
let (dup : Prims.unit -> Prims.unit tac) =
  fun uu____7642  ->
    let uu____7645 = cur_goal ()  in
    bind uu____7645
      (fun g  ->
         let uu____7651 =
           new_uvar "dup" g.FStar_Tactics_Types.context
             g.FStar_Tactics_Types.goal_ty
            in
         bind uu____7651
           (fun u  ->
              let g' =
                let uu___122_7658 = g  in
                {
                  FStar_Tactics_Types.context =
                    (uu___122_7658.FStar_Tactics_Types.context);
                  FStar_Tactics_Types.witness = u;
                  FStar_Tactics_Types.goal_ty =
                    (uu___122_7658.FStar_Tactics_Types.goal_ty);
                  FStar_Tactics_Types.opts =
                    (uu___122_7658.FStar_Tactics_Types.opts);
                  FStar_Tactics_Types.is_guard =
                    (uu___122_7658.FStar_Tactics_Types.is_guard)
                }  in
              bind __dismiss
                (fun uu____7661  ->
                   let uu____7662 =
                     let uu____7665 =
                       let uu____7666 =
                         FStar_TypeChecker_TcTerm.universe_of
                           g.FStar_Tactics_Types.context
                           g.FStar_Tactics_Types.goal_ty
                          in
                       FStar_Syntax_Util.mk_eq2 uu____7666
                         g.FStar_Tactics_Types.goal_ty u
                         g.FStar_Tactics_Types.witness
                        in
                     add_irrelevant_goal "dup equation"
                       g.FStar_Tactics_Types.context uu____7665
                       g.FStar_Tactics_Types.opts
                      in
                   bind uu____7662
                     (fun uu____7669  ->
                        let uu____7670 = add_goals [g']  in
                        bind uu____7670 (fun uu____7674  -> ret ())))))
  
let (flip : Prims.unit -> Prims.unit tac) =
  fun uu____7679  ->
    bind get
      (fun ps  ->
         match ps.FStar_Tactics_Types.goals with
         | g1::g2::gs ->
             set
               (let uu___123_7696 = ps  in
                {
                  FStar_Tactics_Types.main_context =
                    (uu___123_7696.FStar_Tactics_Types.main_context);
                  FStar_Tactics_Types.main_goal =
                    (uu___123_7696.FStar_Tactics_Types.main_goal);
                  FStar_Tactics_Types.all_implicits =
                    (uu___123_7696.FStar_Tactics_Types.all_implicits);
                  FStar_Tactics_Types.goals = (g2 :: g1 :: gs);
                  FStar_Tactics_Types.smt_goals =
                    (uu___123_7696.FStar_Tactics_Types.smt_goals);
                  FStar_Tactics_Types.depth =
                    (uu___123_7696.FStar_Tactics_Types.depth);
                  FStar_Tactics_Types.__dump =
                    (uu___123_7696.FStar_Tactics_Types.__dump);
                  FStar_Tactics_Types.psc =
                    (uu___123_7696.FStar_Tactics_Types.psc);
                  FStar_Tactics_Types.entry_range =
                    (uu___123_7696.FStar_Tactics_Types.entry_range);
                  FStar_Tactics_Types.guard_policy =
                    (uu___123_7696.FStar_Tactics_Types.guard_policy);
                  FStar_Tactics_Types.freshness =
                    (uu___123_7696.FStar_Tactics_Types.freshness)
                })
         | uu____7697 -> fail "flip: less than 2 goals")
  
let (later : Prims.unit -> Prims.unit tac) =
  fun uu____7704  ->
    bind get
      (fun ps  ->
         match ps.FStar_Tactics_Types.goals with
         | [] -> ret ()
         | g::gs ->
             set
               (let uu___124_7717 = ps  in
                {
                  FStar_Tactics_Types.main_context =
                    (uu___124_7717.FStar_Tactics_Types.main_context);
                  FStar_Tactics_Types.main_goal =
                    (uu___124_7717.FStar_Tactics_Types.main_goal);
                  FStar_Tactics_Types.all_implicits =
                    (uu___124_7717.FStar_Tactics_Types.all_implicits);
                  FStar_Tactics_Types.goals = (FStar_List.append gs [g]);
                  FStar_Tactics_Types.smt_goals =
                    (uu___124_7717.FStar_Tactics_Types.smt_goals);
                  FStar_Tactics_Types.depth =
                    (uu___124_7717.FStar_Tactics_Types.depth);
                  FStar_Tactics_Types.__dump =
                    (uu___124_7717.FStar_Tactics_Types.__dump);
                  FStar_Tactics_Types.psc =
                    (uu___124_7717.FStar_Tactics_Types.psc);
                  FStar_Tactics_Types.entry_range =
                    (uu___124_7717.FStar_Tactics_Types.entry_range);
                  FStar_Tactics_Types.guard_policy =
                    (uu___124_7717.FStar_Tactics_Types.guard_policy);
                  FStar_Tactics_Types.freshness =
                    (uu___124_7717.FStar_Tactics_Types.freshness)
                }))
  
let (qed : Prims.unit -> Prims.unit tac) =
  fun uu____7722  ->
    bind get
      (fun ps  ->
         match ps.FStar_Tactics_Types.goals with
         | [] -> ret ()
         | uu____7729 -> fail "Not done!")
  
let (cases :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 tac)
  =
  fun t  ->
    let uu____7747 =
      let uu____7754 = cur_goal ()  in
      bind uu____7754
        (fun g  ->
           let uu____7764 = __tc g.FStar_Tactics_Types.context t  in
           bind uu____7764
             (fun uu____7800  ->
                match uu____7800 with
                | (t1,typ,guard) ->
                    let uu____7816 = FStar_Syntax_Util.head_and_args typ  in
                    (match uu____7816 with
                     | (hd1,args) ->
                         let uu____7859 =
                           let uu____7872 =
                             let uu____7873 = FStar_Syntax_Util.un_uinst hd1
                                in
                             uu____7873.FStar_Syntax_Syntax.n  in
                           (uu____7872, args)  in
                         (match uu____7859 with
                          | (FStar_Syntax_Syntax.Tm_fvar
                             fv,(p,uu____7892)::(q,uu____7894)::[]) when
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
                                let uu___125_7932 = g  in
                                let uu____7933 =
                                  FStar_TypeChecker_Env.push_bv
                                    g.FStar_Tactics_Types.context v_p
                                   in
                                {
                                  FStar_Tactics_Types.context = uu____7933;
                                  FStar_Tactics_Types.witness =
                                    (uu___125_7932.FStar_Tactics_Types.witness);
                                  FStar_Tactics_Types.goal_ty =
                                    (uu___125_7932.FStar_Tactics_Types.goal_ty);
                                  FStar_Tactics_Types.opts =
                                    (uu___125_7932.FStar_Tactics_Types.opts);
                                  FStar_Tactics_Types.is_guard =
                                    (uu___125_7932.FStar_Tactics_Types.is_guard)
                                }  in
                              let g2 =
                                let uu___126_7935 = g  in
                                let uu____7936 =
                                  FStar_TypeChecker_Env.push_bv
                                    g.FStar_Tactics_Types.context v_q
                                   in
                                {
                                  FStar_Tactics_Types.context = uu____7936;
                                  FStar_Tactics_Types.witness =
                                    (uu___126_7935.FStar_Tactics_Types.witness);
                                  FStar_Tactics_Types.goal_ty =
                                    (uu___126_7935.FStar_Tactics_Types.goal_ty);
                                  FStar_Tactics_Types.opts =
                                    (uu___126_7935.FStar_Tactics_Types.opts);
                                  FStar_Tactics_Types.is_guard =
                                    (uu___126_7935.FStar_Tactics_Types.is_guard)
                                }  in
                              bind __dismiss
                                (fun uu____7943  ->
                                   let uu____7944 = add_goals [g1; g2]  in
                                   bind uu____7944
                                     (fun uu____7953  ->
                                        let uu____7954 =
                                          let uu____7959 =
                                            FStar_Syntax_Syntax.bv_to_name
                                              v_p
                                             in
                                          let uu____7960 =
                                            FStar_Syntax_Syntax.bv_to_name
                                              v_q
                                             in
                                          (uu____7959, uu____7960)  in
                                        ret uu____7954))
                          | uu____7965 ->
                              let uu____7978 =
                                tts g.FStar_Tactics_Types.context typ  in
                              fail1 "Not a disjunction: %s" uu____7978))))
       in
    FStar_All.pipe_left (wrap_err "cases") uu____7747
  
let (set_options : Prims.string -> Prims.unit tac) =
  fun s  ->
    let uu____8006 = cur_goal ()  in
    bind uu____8006
      (fun g  ->
         FStar_Options.push ();
         (let uu____8019 = FStar_Util.smap_copy g.FStar_Tactics_Types.opts
             in
          FStar_Options.set uu____8019);
         (let res = FStar_Options.set_options FStar_Options.Set s  in
          let opts' = FStar_Options.peek ()  in
          FStar_Options.pop ();
          (match res with
           | FStar_Getopt.Success  ->
               let g' =
                 let uu___127_8026 = g  in
                 {
                   FStar_Tactics_Types.context =
                     (uu___127_8026.FStar_Tactics_Types.context);
                   FStar_Tactics_Types.witness =
                     (uu___127_8026.FStar_Tactics_Types.witness);
                   FStar_Tactics_Types.goal_ty =
                     (uu___127_8026.FStar_Tactics_Types.goal_ty);
                   FStar_Tactics_Types.opts = opts';
                   FStar_Tactics_Types.is_guard =
                     (uu___127_8026.FStar_Tactics_Types.is_guard)
                 }  in
               replace_cur g'
           | FStar_Getopt.Error err ->
               fail2 "Setting options `%s` failed: %s" s err
           | FStar_Getopt.Help  ->
               fail1 "Setting options `%s` failed (got `Help`?)" s)))
  
let (top_env : Prims.unit -> env tac) =
  fun uu____8032  ->
    bind get
      (fun ps  -> FStar_All.pipe_left ret ps.FStar_Tactics_Types.main_context)
  
let (cur_env : Prims.unit -> env tac) =
  fun uu____8043  ->
    let uu____8046 = cur_goal ()  in
    bind uu____8046
      (fun g  -> FStar_All.pipe_left ret g.FStar_Tactics_Types.context)
  
let (cur_goal' : Prims.unit -> FStar_Syntax_Syntax.term tac) =
  fun uu____8057  ->
    let uu____8060 = cur_goal ()  in
    bind uu____8060
      (fun g  -> FStar_All.pipe_left ret g.FStar_Tactics_Types.goal_ty)
  
let (cur_witness : Prims.unit -> FStar_Syntax_Syntax.term tac) =
  fun uu____8071  ->
    let uu____8074 = cur_goal ()  in
    bind uu____8074
      (fun g  -> FStar_All.pipe_left ret g.FStar_Tactics_Types.witness)
  
let (unquote :
  FStar_Reflection_Data.typ ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term tac)
  =
  fun ty  ->
    fun tm  ->
      let uu____8091 =
        let uu____8094 = cur_goal ()  in
        bind uu____8094
          (fun goal  ->
             let env =
               FStar_TypeChecker_Env.set_expected_typ
                 goal.FStar_Tactics_Types.context ty
                in
             let uu____8102 = __tc env tm  in
             bind uu____8102
               (fun uu____8122  ->
                  match uu____8122 with
                  | (tm1,typ,guard) ->
                      let uu____8134 =
                        proc_guard "unquote" env guard
                          goal.FStar_Tactics_Types.opts
                         in
                      bind uu____8134 (fun uu____8138  -> ret tm1)))
         in
      FStar_All.pipe_left (wrap_err "unquote") uu____8091
  
let (uvar_env :
  env ->
    FStar_Reflection_Data.typ FStar_Pervasives_Native.option ->
      FStar_Syntax_Syntax.term tac)
  =
  fun env  ->
    fun ty  ->
      let uu____8157 =
        match ty with
        | FStar_Pervasives_Native.Some ty1 -> ret ty1
        | FStar_Pervasives_Native.None  ->
            let uu____8163 =
              let uu____8164 = FStar_Syntax_Util.type_u ()  in
              FStar_All.pipe_left FStar_Pervasives_Native.fst uu____8164  in
            new_uvar "uvar_env.2" env uu____8163
         in
      bind uu____8157
        (fun typ  ->
           let uu____8176 = new_uvar "uvar_env" env typ  in
           bind uu____8176 (fun t  -> ret t))
  
let (unshelve : FStar_Syntax_Syntax.term -> Prims.unit tac) =
  fun t  ->
    let uu____8188 =
      bind get
        (fun ps  ->
           let env = ps.FStar_Tactics_Types.main_context  in
           let opts =
             match ps.FStar_Tactics_Types.goals with
             | g::uu____8205 -> g.FStar_Tactics_Types.opts
             | uu____8208 -> FStar_Options.peek ()  in
           let uu____8211 = FStar_Syntax_Util.head_and_args t  in
           match uu____8211 with
           | ({
                FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                  (uu____8228,typ);
                FStar_Syntax_Syntax.pos = uu____8230;
                FStar_Syntax_Syntax.vars = uu____8231;_},uu____8232)
               ->
               let uu____8277 =
                 let uu____8280 =
                   let uu____8281 = bnorm env t  in
                   let uu____8282 = bnorm env typ  in
                   {
                     FStar_Tactics_Types.context = env;
                     FStar_Tactics_Types.witness = uu____8281;
                     FStar_Tactics_Types.goal_ty = uu____8282;
                     FStar_Tactics_Types.opts = opts;
                     FStar_Tactics_Types.is_guard = false
                   }  in
                 [uu____8280]  in
               add_goals uu____8277
           | uu____8283 -> fail "not a uvar")
       in
    FStar_All.pipe_left (wrap_err "unshelve") uu____8188
  
let (unify :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.bool tac) =
  fun t1  ->
    fun t2  ->
      bind get
        (fun ps  -> do_unify ps.FStar_Tactics_Types.main_context t1 t2)
  
let (launch_process :
  Prims.string -> Prims.string -> Prims.string -> Prims.string tac) =
  fun prog  ->
    fun args  ->
      fun input  ->
        bind idtac
          (fun uu____8330  ->
             let uu____8331 = FStar_Options.unsafe_tactic_exec ()  in
             if uu____8331
             then
               let s =
                 FStar_Util.launch_process true "tactic_launch" prog args
                   input (fun uu____8337  -> fun uu____8338  -> false)
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
        (fun uu____8352  ->
           let uu____8353 =
             FStar_Syntax_Syntax.gen_bv nm FStar_Pervasives_Native.None t  in
           ret uu____8353)
  
let (change : FStar_Reflection_Data.typ -> Prims.unit tac) =
  fun ty  ->
    let uu____8361 =
      mlog
        (fun uu____8366  ->
           let uu____8367 = FStar_Syntax_Print.term_to_string ty  in
           FStar_Util.print1 "change: ty = %s\n" uu____8367)
        (fun uu____8370  ->
           let uu____8371 = cur_goal ()  in
           bind uu____8371
             (fun g  ->
                let uu____8377 = __tc g.FStar_Tactics_Types.context ty  in
                bind uu____8377
                  (fun uu____8397  ->
                     match uu____8397 with
                     | (ty1,uu____8407,guard) ->
                         let uu____8409 =
                           proc_guard "change" g.FStar_Tactics_Types.context
                             guard g.FStar_Tactics_Types.opts
                            in
                         bind uu____8409
                           (fun uu____8414  ->
                              let uu____8415 =
                                do_unify g.FStar_Tactics_Types.context
                                  g.FStar_Tactics_Types.goal_ty ty1
                                 in
                              bind uu____8415
                                (fun bb  ->
                                   if bb
                                   then
                                     replace_cur
                                       (let uu___128_8424 = g  in
                                        {
                                          FStar_Tactics_Types.context =
                                            (uu___128_8424.FStar_Tactics_Types.context);
                                          FStar_Tactics_Types.witness =
                                            (uu___128_8424.FStar_Tactics_Types.witness);
                                          FStar_Tactics_Types.goal_ty = ty1;
                                          FStar_Tactics_Types.opts =
                                            (uu___128_8424.FStar_Tactics_Types.opts);
                                          FStar_Tactics_Types.is_guard =
                                            (uu___128_8424.FStar_Tactics_Types.is_guard)
                                        })
                                   else
                                     (let steps =
                                        [FStar_TypeChecker_Normalize.Reify;
                                        FStar_TypeChecker_Normalize.UnfoldUntil
                                          FStar_Syntax_Syntax.Delta_constant;
                                        FStar_TypeChecker_Normalize.AllowUnboundUniverses;
                                        FStar_TypeChecker_Normalize.Primops;
                                        FStar_TypeChecker_Normalize.Simplify;
                                        FStar_TypeChecker_Normalize.UnfoldTac;
                                        FStar_TypeChecker_Normalize.Unmeta]
                                         in
                                      let ng =
                                        normalize steps
                                          g.FStar_Tactics_Types.context
                                          g.FStar_Tactics_Types.goal_ty
                                         in
                                      let nty =
                                        normalize steps
                                          g.FStar_Tactics_Types.context ty1
                                         in
                                      let uu____8431 =
                                        do_unify
                                          g.FStar_Tactics_Types.context ng
                                          nty
                                         in
                                      bind uu____8431
                                        (fun b  ->
                                           if b
                                           then
                                             replace_cur
                                               (let uu___129_8440 = g  in
                                                {
                                                  FStar_Tactics_Types.context
                                                    =
                                                    (uu___129_8440.FStar_Tactics_Types.context);
                                                  FStar_Tactics_Types.witness
                                                    =
                                                    (uu___129_8440.FStar_Tactics_Types.witness);
                                                  FStar_Tactics_Types.goal_ty
                                                    = ty1;
                                                  FStar_Tactics_Types.opts =
                                                    (uu___129_8440.FStar_Tactics_Types.opts);
                                                  FStar_Tactics_Types.is_guard
                                                    =
                                                    (uu___129_8440.FStar_Tactics_Types.is_guard)
                                                })
                                           else fail "not convertible")))))))
       in
    FStar_All.pipe_left (wrap_err "change") uu____8361
  
let rec last : 'a . 'a Prims.list -> 'a =
  fun l  ->
    match l with
    | [] -> failwith "last: empty list"
    | x::[] -> x
    | uu____8459::xs -> last xs
  
let rec init : 'a . 'a Prims.list -> 'a Prims.list =
  fun l  ->
    match l with
    | [] -> failwith "init: empty list"
    | x::[] -> []
    | x::xs -> let uu____8484 = init xs  in x :: uu____8484
  
let rec (inspect :
  FStar_Syntax_Syntax.term -> FStar_Reflection_Data.term_view tac) =
  fun t  ->
    let t1 = FStar_Syntax_Util.unascribe t  in
    let t2 = FStar_Syntax_Util.un_uinst t1  in
    match t2.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_meta (t3,uu____8499) -> inspect t3
    | FStar_Syntax_Syntax.Tm_name bv ->
        FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_Var bv)
    | FStar_Syntax_Syntax.Tm_bvar bv ->
        FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_BVar bv)
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_FVar fv)
    | FStar_Syntax_Syntax.Tm_app (hd1,[]) ->
        failwith "inspect: empty arguments on Tm_app"
    | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
        let uu____8556 = last args  in
        (match uu____8556 with
         | (a,q) ->
             let q' = FStar_Reflection_Basic.inspect_aqual q  in
             let uu____8578 =
               let uu____8579 =
                 let uu____8584 =
                   let uu____8587 =
                     let uu____8588 = init args  in
                     FStar_Syntax_Syntax.mk_Tm_app hd1 uu____8588  in
                   uu____8587 FStar_Pervasives_Native.None
                     t2.FStar_Syntax_Syntax.pos
                    in
                 (uu____8584, (a, q'))  in
               FStar_Reflection_Data.Tv_App uu____8579  in
             FStar_All.pipe_left ret uu____8578)
    | FStar_Syntax_Syntax.Tm_abs ([],uu____8609,uu____8610) ->
        failwith "inspect: empty arguments on Tm_abs"
    | FStar_Syntax_Syntax.Tm_abs (bs,t3,k) ->
        let uu____8654 = FStar_Syntax_Subst.open_term bs t3  in
        (match uu____8654 with
         | (bs1,t4) ->
             (match bs1 with
              | [] -> failwith "impossible"
              | b::bs2 ->
                  let uu____8687 =
                    let uu____8688 =
                      let uu____8693 = FStar_Syntax_Util.abs bs2 t4 k  in
                      (b, uu____8693)  in
                    FStar_Reflection_Data.Tv_Abs uu____8688  in
                  FStar_All.pipe_left ret uu____8687))
    | FStar_Syntax_Syntax.Tm_type uu____8700 ->
        FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_Type ())
    | FStar_Syntax_Syntax.Tm_arrow ([],k) ->
        failwith "inspect: empty binders on arrow"
    | FStar_Syntax_Syntax.Tm_arrow uu____8720 ->
        let uu____8733 = FStar_Syntax_Util.arrow_one t2  in
        (match uu____8733 with
         | FStar_Pervasives_Native.Some (b,c) ->
             FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_Arrow (b, c))
         | FStar_Pervasives_Native.None  -> failwith "impossible")
    | FStar_Syntax_Syntax.Tm_refine (bv,t3) ->
        let b = FStar_Syntax_Syntax.mk_binder bv  in
        let uu____8763 = FStar_Syntax_Subst.open_term [b] t3  in
        (match uu____8763 with
         | (b',t4) ->
             let b1 =
               match b' with
               | b'1::[] -> b'1
               | uu____8794 -> failwith "impossible"  in
             FStar_All.pipe_left ret
               (FStar_Reflection_Data.Tv_Refine
                  ((FStar_Pervasives_Native.fst b1), t4)))
    | FStar_Syntax_Syntax.Tm_constant c ->
        let uu____8802 =
          let uu____8803 = FStar_Reflection_Basic.inspect_const c  in
          FStar_Reflection_Data.Tv_Const uu____8803  in
        FStar_All.pipe_left ret uu____8802
    | FStar_Syntax_Syntax.Tm_uvar (u,t3) ->
        let uu____8832 =
          let uu____8833 =
            let uu____8838 =
              let uu____8839 = FStar_Syntax_Unionfind.uvar_id u  in
              FStar_BigInt.of_int_fs uu____8839  in
            (uu____8838, t3)  in
          FStar_Reflection_Data.Tv_Uvar uu____8833  in
        FStar_All.pipe_left ret uu____8832
    | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),t21) ->
        if lb.FStar_Syntax_Syntax.lbunivs <> []
        then FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown
        else
          (match lb.FStar_Syntax_Syntax.lbname with
           | FStar_Util.Inr uu____8867 ->
               FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown
           | FStar_Util.Inl bv ->
               let b = FStar_Syntax_Syntax.mk_binder bv  in
               let uu____8872 = FStar_Syntax_Subst.open_term [b] t21  in
               (match uu____8872 with
                | (bs,t22) ->
                    let b1 =
                      match bs with
                      | b1::[] -> b1
                      | uu____8903 ->
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
           | FStar_Util.Inr uu____8935 ->
               FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown
           | FStar_Util.Inl bv ->
               let uu____8939 = FStar_Syntax_Subst.open_let_rec [lb] t21  in
               (match uu____8939 with
                | (lbs,t22) ->
                    (match lbs with
                     | lb1::[] ->
                         (match lb1.FStar_Syntax_Syntax.lbname with
                          | FStar_Util.Inr uu____8959 ->
                              ret FStar_Reflection_Data.Tv_Unknown
                          | FStar_Util.Inl bv1 ->
                              FStar_All.pipe_left ret
                                (FStar_Reflection_Data.Tv_Let
                                   (true, bv1,
                                     (lb1.FStar_Syntax_Syntax.lbdef), t22)))
                     | uu____8965 ->
                         failwith
                           "impossible: open_term returned different amount of binders")))
    | FStar_Syntax_Syntax.Tm_match (t3,brs) ->
        let rec inspect_pat p =
          match p.FStar_Syntax_Syntax.v with
          | FStar_Syntax_Syntax.Pat_constant c ->
              let uu____9017 = FStar_Reflection_Basic.inspect_const c  in
              FStar_Reflection_Data.Pat_Constant uu____9017
          | FStar_Syntax_Syntax.Pat_cons (fv,ps) ->
              let uu____9036 =
                let uu____9043 =
                  FStar_List.map
                    (fun uu____9055  ->
                       match uu____9055 with
                       | (p1,uu____9063) -> inspect_pat p1) ps
                   in
                (fv, uu____9043)  in
              FStar_Reflection_Data.Pat_Cons uu____9036
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
            (fun uu___63_9117  ->
               match uu___63_9117 with
               | (pat,uu____9139,t4) ->
                   let uu____9157 = inspect_pat pat  in (uu____9157, t4))
            brs1
           in
        FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_Match (t3, brs2))
    | FStar_Syntax_Syntax.Tm_unknown  ->
        FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown
    | uu____9174 ->
        ((let uu____9176 =
            let uu____9181 =
              let uu____9182 = FStar_Syntax_Print.tag_of_term t2  in
              let uu____9183 = FStar_Syntax_Print.term_to_string t2  in
              FStar_Util.format2
                "inspect: outside of expected syntax (%s, %s)\n" uu____9182
                uu____9183
               in
            (FStar_Errors.Warning_CantInspect, uu____9181)  in
          FStar_Errors.log_issue t2.FStar_Syntax_Syntax.pos uu____9176);
         FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown)
  
let (pack : FStar_Reflection_Data.term_view -> FStar_Syntax_Syntax.term tac)
  =
  fun tv  ->
    match tv with
    | FStar_Reflection_Data.Tv_Var bv ->
        let uu____9194 = FStar_Syntax_Syntax.bv_to_name bv  in
        FStar_All.pipe_left ret uu____9194
    | FStar_Reflection_Data.Tv_BVar bv ->
        let uu____9198 = FStar_Syntax_Syntax.bv_to_tm bv  in
        FStar_All.pipe_left ret uu____9198
    | FStar_Reflection_Data.Tv_FVar fv ->
        let uu____9202 = FStar_Syntax_Syntax.fv_to_tm fv  in
        FStar_All.pipe_left ret uu____9202
    | FStar_Reflection_Data.Tv_App (l,(r,q)) ->
        let q' = FStar_Reflection_Basic.pack_aqual q  in
        let uu____9213 = FStar_Syntax_Util.mk_app l [(r, q')]  in
        FStar_All.pipe_left ret uu____9213
    | FStar_Reflection_Data.Tv_Abs (b,t) ->
        let uu____9234 =
          FStar_Syntax_Util.abs [b] t FStar_Pervasives_Native.None  in
        FStar_All.pipe_left ret uu____9234
    | FStar_Reflection_Data.Tv_Arrow (b,c) ->
        let uu____9239 = FStar_Syntax_Util.arrow [b] c  in
        FStar_All.pipe_left ret uu____9239
    | FStar_Reflection_Data.Tv_Type () ->
        FStar_All.pipe_left ret FStar_Syntax_Util.ktype
    | FStar_Reflection_Data.Tv_Refine (bv,t) ->
        let uu____9260 = FStar_Syntax_Util.refine bv t  in
        FStar_All.pipe_left ret uu____9260
    | FStar_Reflection_Data.Tv_Const c ->
        let uu____9272 =
          let uu____9275 =
            let uu____9278 =
              let uu____9279 = FStar_Reflection_Basic.pack_const c  in
              FStar_Syntax_Syntax.Tm_constant uu____9279  in
            FStar_Syntax_Syntax.mk uu____9278  in
          uu____9275 FStar_Pervasives_Native.None FStar_Range.dummyRange  in
        FStar_All.pipe_left ret uu____9272
    | FStar_Reflection_Data.Tv_Uvar (u,t) ->
        let uu____9293 =
          let uu____9296 = FStar_BigInt.to_int_fs u  in
          FStar_Syntax_Util.uvar_from_id uu____9296 t  in
        FStar_All.pipe_left ret uu____9293
    | FStar_Reflection_Data.Tv_Let (false ,bv,t1,t2) ->
        let lb =
          FStar_Syntax_Util.mk_letbinding (FStar_Util.Inl bv) []
            bv.FStar_Syntax_Syntax.sort FStar_Parser_Const.effect_Tot_lid t1
            [] FStar_Range.dummyRange
           in
        let uu____9311 =
          let uu____9314 =
            let uu____9317 =
              let uu____9318 =
                let uu____9331 =
                  let uu____9332 =
                    let uu____9333 = FStar_Syntax_Syntax.mk_binder bv  in
                    [uu____9333]  in
                  FStar_Syntax_Subst.close uu____9332 t2  in
                ((false, [lb]), uu____9331)  in
              FStar_Syntax_Syntax.Tm_let uu____9318  in
            FStar_Syntax_Syntax.mk uu____9317  in
          uu____9314 FStar_Pervasives_Native.None FStar_Range.dummyRange  in
        FStar_All.pipe_left ret uu____9311
    | FStar_Reflection_Data.Tv_Let (true ,bv,t1,t2) ->
        let lb =
          FStar_Syntax_Util.mk_letbinding (FStar_Util.Inl bv) []
            bv.FStar_Syntax_Syntax.sort FStar_Parser_Const.effect_Tot_lid t1
            [] FStar_Range.dummyRange
           in
        let uu____9359 = FStar_Syntax_Subst.close_let_rec [lb] t2  in
        (match uu____9359 with
         | (lbs,body) ->
             let uu____9374 =
               FStar_Syntax_Syntax.mk
                 (FStar_Syntax_Syntax.Tm_let ((true, lbs), body))
                 FStar_Pervasives_Native.None FStar_Range.dummyRange
                in
             FStar_All.pipe_left ret uu____9374)
    | FStar_Reflection_Data.Tv_Match (t,brs) ->
        let wrap v1 =
          {
            FStar_Syntax_Syntax.v = v1;
            FStar_Syntax_Syntax.p = FStar_Range.dummyRange
          }  in
        let rec pack_pat p =
          match p with
          | FStar_Reflection_Data.Pat_Constant c ->
              let uu____9410 =
                let uu____9411 = FStar_Reflection_Basic.pack_const c  in
                FStar_Syntax_Syntax.Pat_constant uu____9411  in
              FStar_All.pipe_left wrap uu____9410
          | FStar_Reflection_Data.Pat_Cons (fv,ps) ->
              let uu____9420 =
                let uu____9421 =
                  let uu____9434 =
                    FStar_List.map
                      (fun p1  ->
                         let uu____9448 = pack_pat p1  in (uu____9448, false))
                      ps
                     in
                  (fv, uu____9434)  in
                FStar_Syntax_Syntax.Pat_cons uu____9421  in
              FStar_All.pipe_left wrap uu____9420
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
            (fun uu___64_9498  ->
               match uu___64_9498 with
               | (pat,t1) ->
                   let uu____9515 = pack_pat pat  in
                   (uu____9515, FStar_Pervasives_Native.None, t1)) brs
           in
        let brs2 = FStar_List.map FStar_Syntax_Subst.close_branch brs1  in
        let uu____9525 =
          FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_match (t, brs2))
            FStar_Pervasives_Native.None FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____9525
    | FStar_Reflection_Data.Tv_AscribedT (e,t,tacopt) ->
        let uu____9545 =
          FStar_Syntax_Syntax.mk
            (FStar_Syntax_Syntax.Tm_ascribed
               (e, ((FStar_Util.Inl t), tacopt),
                 FStar_Pervasives_Native.None)) FStar_Pervasives_Native.None
            FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____9545
    | FStar_Reflection_Data.Tv_AscribedC (e,c,tacopt) ->
        let uu____9587 =
          FStar_Syntax_Syntax.mk
            (FStar_Syntax_Syntax.Tm_ascribed
               (e, ((FStar_Util.Inr c), tacopt),
                 FStar_Pervasives_Native.None)) FStar_Pervasives_Native.None
            FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____9587
    | FStar_Reflection_Data.Tv_Unknown  ->
        let uu____9622 =
          FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown
            FStar_Pervasives_Native.None FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____9622
  
let (goal_of_goal_ty :
  env ->
    FStar_Reflection_Data.typ ->
      (FStar_Tactics_Types.goal,FStar_TypeChecker_Env.guard_t)
        FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun typ  ->
      let uu____9647 =
        FStar_TypeChecker_Util.new_implicit_var "proofstate_of_goal_ty"
          typ.FStar_Syntax_Syntax.pos env typ
         in
      match uu____9647 with
      | (u,uu____9665,g_u) ->
          let g =
            let uu____9680 = FStar_Options.peek ()  in
            {
              FStar_Tactics_Types.context = env;
              FStar_Tactics_Types.witness = u;
              FStar_Tactics_Types.goal_ty = typ;
              FStar_Tactics_Types.opts = uu____9680;
              FStar_Tactics_Types.is_guard = false
            }  in
          (g, g_u)
  
let (proofstate_of_goal_ty :
  env ->
    FStar_Reflection_Data.typ ->
      (FStar_Tactics_Types.proofstate,FStar_Syntax_Syntax.term)
        FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun typ  ->
      let uu____9691 = goal_of_goal_ty env typ  in
      match uu____9691 with
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
              FStar_Tactics_Types.psc = FStar_TypeChecker_Normalize.null_psc;
              FStar_Tactics_Types.entry_range = FStar_Range.dummyRange;
              FStar_Tactics_Types.guard_policy = FStar_Tactics_Types.SMT;
              FStar_Tactics_Types.freshness = (Prims.parse_int "0")
            }  in
          (ps, (g.FStar_Tactics_Types.witness))
  