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
        (let uu____1029 =
           FStar_TypeChecker_Env.debug env (FStar_Options.Other "1346")  in
         if uu____1029
         then
           let uu____1030 = FStar_Syntax_Print.term_to_string t1  in
           let uu____1031 = FStar_Syntax_Print.term_to_string t2  in
           FStar_Util.print2 "%%%%%%%%do_unify %s =? %s\n" uu____1030
             uu____1031
         else ());
        (try
           let res = FStar_TypeChecker_Rel.teq_nosmt env t1 t2  in
           (let uu____1043 =
              FStar_TypeChecker_Env.debug env (FStar_Options.Other "1346")
               in
            if uu____1043
            then
              let uu____1044 = FStar_Util.string_of_bool res  in
              let uu____1045 = FStar_Syntax_Print.term_to_string t1  in
              let uu____1046 = FStar_Syntax_Print.term_to_string t2  in
              FStar_Util.print3 "%%%%%%%%do_unify (RESULT %s) %s =? %s\n"
                uu____1044 uu____1045 uu____1046
            else ());
           ret res
         with
         | FStar_Errors.Err (uu____1054,msg) ->
             mlog
               (fun uu____1057  ->
                  FStar_Util.print1 ">> do_unify error, (%s)\n" msg)
               (fun uu____1059  -> ret false)
         | FStar_Errors.Error (uu____1060,msg,r) ->
             mlog
               (fun uu____1065  ->
                  let uu____1066 = FStar_Range.string_of_range r  in
                  FStar_Util.print2 ">> do_unify error, (%s) at (%s)\n" msg
                    uu____1066) (fun uu____1068  -> ret false))
  
let (do_unify :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.bool tac)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        bind idtac
          (fun uu____1085  ->
             (let uu____1087 =
                FStar_TypeChecker_Env.debug env (FStar_Options.Other "1346")
                 in
              if uu____1087
              then
                (FStar_Options.push ();
                 (let uu____1089 =
                    FStar_Options.set_options FStar_Options.Set
                      "--debug_level Rel --debug_level RelCheck"
                     in
                  ()))
              else ());
             (let uu____1091 =
                let uu____1094 = __do_unify env t1 t2  in
                bind uu____1094
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
              bind uu____1091
                (fun r  ->
                   (let uu____1110 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "1346")
                       in
                    if uu____1110 then FStar_Options.pop () else ());
                   ret r)))
  
let (trysolve :
  FStar_Tactics_Types.goal -> FStar_Syntax_Syntax.term -> Prims.bool tac) =
  fun goal  ->
    fun solution  ->
      do_unify goal.FStar_Tactics_Types.context solution
        goal.FStar_Tactics_Types.witness
  
let (__dismiss : Prims.unit tac) =
  bind get
    (fun p  ->
       let uu____1127 =
         let uu___70_1128 = p  in
         let uu____1129 = FStar_List.tl p.FStar_Tactics_Types.goals  in
         {
           FStar_Tactics_Types.main_context =
             (uu___70_1128.FStar_Tactics_Types.main_context);
           FStar_Tactics_Types.main_goal =
             (uu___70_1128.FStar_Tactics_Types.main_goal);
           FStar_Tactics_Types.all_implicits =
             (uu___70_1128.FStar_Tactics_Types.all_implicits);
           FStar_Tactics_Types.goals = uu____1129;
           FStar_Tactics_Types.smt_goals =
             (uu___70_1128.FStar_Tactics_Types.smt_goals);
           FStar_Tactics_Types.depth =
             (uu___70_1128.FStar_Tactics_Types.depth);
           FStar_Tactics_Types.__dump =
             (uu___70_1128.FStar_Tactics_Types.__dump);
           FStar_Tactics_Types.psc = (uu___70_1128.FStar_Tactics_Types.psc);
           FStar_Tactics_Types.entry_range =
             (uu___70_1128.FStar_Tactics_Types.entry_range);
           FStar_Tactics_Types.guard_policy =
             (uu___70_1128.FStar_Tactics_Types.guard_policy);
           FStar_Tactics_Types.freshness =
             (uu___70_1128.FStar_Tactics_Types.freshness)
         }  in
       set uu____1127)
  
let (dismiss : Prims.unit -> Prims.unit tac) =
  fun uu____1136  ->
    bind get
      (fun p  ->
         match p.FStar_Tactics_Types.goals with
         | [] -> fail "dismiss: no more goals"
         | uu____1143 -> __dismiss)
  
let (solve :
  FStar_Tactics_Types.goal -> FStar_Syntax_Syntax.term -> Prims.unit tac) =
  fun goal  ->
    fun solution  ->
      let uu____1156 = trysolve goal solution  in
      bind uu____1156
        (fun b  ->
           if b
           then __dismiss
           else
             (let uu____1164 =
                let uu____1165 =
                  tts goal.FStar_Tactics_Types.context solution  in
                let uu____1166 =
                  tts goal.FStar_Tactics_Types.context
                    goal.FStar_Tactics_Types.witness
                   in
                let uu____1167 =
                  tts goal.FStar_Tactics_Types.context
                    goal.FStar_Tactics_Types.goal_ty
                   in
                FStar_Util.format3 "%s does not solve %s : %s" uu____1165
                  uu____1166 uu____1167
                 in
              fail uu____1164))
  
let (dismiss_all : Prims.unit tac) =
  bind get
    (fun p  ->
       set
         (let uu___71_1174 = p  in
          {
            FStar_Tactics_Types.main_context =
              (uu___71_1174.FStar_Tactics_Types.main_context);
            FStar_Tactics_Types.main_goal =
              (uu___71_1174.FStar_Tactics_Types.main_goal);
            FStar_Tactics_Types.all_implicits =
              (uu___71_1174.FStar_Tactics_Types.all_implicits);
            FStar_Tactics_Types.goals = [];
            FStar_Tactics_Types.smt_goals =
              (uu___71_1174.FStar_Tactics_Types.smt_goals);
            FStar_Tactics_Types.depth =
              (uu___71_1174.FStar_Tactics_Types.depth);
            FStar_Tactics_Types.__dump =
              (uu___71_1174.FStar_Tactics_Types.__dump);
            FStar_Tactics_Types.psc = (uu___71_1174.FStar_Tactics_Types.psc);
            FStar_Tactics_Types.entry_range =
              (uu___71_1174.FStar_Tactics_Types.entry_range);
            FStar_Tactics_Types.guard_policy =
              (uu___71_1174.FStar_Tactics_Types.guard_policy);
            FStar_Tactics_Types.freshness =
              (uu___71_1174.FStar_Tactics_Types.freshness)
          }))
  
let (nwarn : Prims.int FStar_ST.ref) =
  FStar_Util.mk_ref (Prims.parse_int "0") 
let (check_valid_goal : FStar_Tactics_Types.goal -> Prims.unit) =
  fun g  ->
    let uu____1191 = FStar_Options.defensive ()  in
    if uu____1191
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
        let uu____1203 = FStar_TypeChecker_Env.pop_bv e  in
        match uu____1203 with
        | FStar_Pervasives_Native.None  -> b3
        | FStar_Pervasives_Native.Some (bv,e1) ->
            let b4 =
              b3 &&
                (FStar_TypeChecker_Env.closed e1 bv.FStar_Syntax_Syntax.sort)
               in
            aux b4 e1
         in
      let uu____1221 =
        (let uu____1224 = aux b2 env  in Prims.op_Negation uu____1224) &&
          (let uu____1226 = FStar_ST.op_Bang nwarn  in
           uu____1226 < (Prims.parse_int "5"))
         in
      (if uu____1221
       then
         ((let uu____1247 =
             let uu____1252 =
               let uu____1253 = goal_to_string g  in
               FStar_Util.format1
                 "The following goal is ill-formed. Keeping calm and carrying on...\n<%s>\n\n"
                 uu____1253
                in
             (FStar_Errors.Warning_IllFormedGoal, uu____1252)  in
           FStar_Errors.log_issue
             (g.FStar_Tactics_Types.goal_ty).FStar_Syntax_Syntax.pos
             uu____1247);
          (let uu____1254 =
             let uu____1255 = FStar_ST.op_Bang nwarn  in
             uu____1255 + (Prims.parse_int "1")  in
           FStar_ST.op_Colon_Equals nwarn uu____1254))
       else ())
    else ()
  
let (add_goals : FStar_Tactics_Types.goal Prims.list -> Prims.unit tac) =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___72_1313 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___72_1313.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___72_1313.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___72_1313.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (FStar_List.append gs p.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (uu___72_1313.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___72_1313.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___72_1313.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___72_1313.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___72_1313.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___72_1313.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___72_1313.FStar_Tactics_Types.freshness)
            }))
  
let (add_smt_goals : FStar_Tactics_Types.goal Prims.list -> Prims.unit tac) =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___73_1331 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___73_1331.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___73_1331.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___73_1331.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___73_1331.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (FStar_List.append gs p.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___73_1331.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___73_1331.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___73_1331.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___73_1331.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___73_1331.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___73_1331.FStar_Tactics_Types.freshness)
            }))
  
let (push_goals : FStar_Tactics_Types.goal Prims.list -> Prims.unit tac) =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___74_1349 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___74_1349.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___74_1349.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___74_1349.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (FStar_List.append p.FStar_Tactics_Types.goals gs);
              FStar_Tactics_Types.smt_goals =
                (uu___74_1349.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___74_1349.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___74_1349.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___74_1349.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___74_1349.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___74_1349.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___74_1349.FStar_Tactics_Types.freshness)
            }))
  
let (push_smt_goals : FStar_Tactics_Types.goal Prims.list -> Prims.unit tac)
  =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___75_1367 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___75_1367.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___75_1367.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___75_1367.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___75_1367.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (FStar_List.append p.FStar_Tactics_Types.smt_goals gs);
              FStar_Tactics_Types.depth =
                (uu___75_1367.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___75_1367.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___75_1367.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___75_1367.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___75_1367.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___75_1367.FStar_Tactics_Types.freshness)
            }))
  
let (replace_cur : FStar_Tactics_Types.goal -> Prims.unit tac) =
  fun g  -> bind __dismiss (fun uu____1376  -> add_goals [g]) 
let (add_implicits : implicits -> Prims.unit tac) =
  fun i  ->
    bind get
      (fun p  ->
         set
           (let uu___76_1388 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___76_1388.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___76_1388.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (FStar_List.append i p.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___76_1388.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (uu___76_1388.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___76_1388.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___76_1388.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___76_1388.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___76_1388.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___76_1388.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___76_1388.FStar_Tactics_Types.freshness)
            }))
  
let (new_uvar :
  Prims.string ->
    env -> FStar_Reflection_Data.typ -> FStar_Syntax_Syntax.term tac)
  =
  fun reason  ->
    fun env  ->
      fun typ  ->
        let uu____1414 =
          FStar_TypeChecker_Util.new_implicit_var reason
            typ.FStar_Syntax_Syntax.pos env typ
           in
        match uu____1414 with
        | (u,uu____1430,g_u) ->
            let uu____1444 =
              add_implicits g_u.FStar_TypeChecker_Env.implicits  in
            bind uu____1444 (fun uu____1448  -> ret u)
  
let (is_true : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____1452 = FStar_Syntax_Util.un_squash t  in
    match uu____1452 with
    | FStar_Pervasives_Native.Some t' ->
        let uu____1462 =
          let uu____1463 = FStar_Syntax_Subst.compress t'  in
          uu____1463.FStar_Syntax_Syntax.n  in
        (match uu____1462 with
         | FStar_Syntax_Syntax.Tm_fvar fv ->
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.true_lid
         | uu____1467 -> false)
    | uu____1468 -> false
  
let (is_false : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____1476 = FStar_Syntax_Util.un_squash t  in
    match uu____1476 with
    | FStar_Pervasives_Native.Some t' ->
        let uu____1486 =
          let uu____1487 = FStar_Syntax_Subst.compress t'  in
          uu____1487.FStar_Syntax_Syntax.n  in
        (match uu____1486 with
         | FStar_Syntax_Syntax.Tm_fvar fv ->
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.false_lid
         | uu____1491 -> false)
    | uu____1492 -> false
  
let (cur_goal : Prims.unit -> FStar_Tactics_Types.goal tac) =
  fun uu____1501  ->
    bind get
      (fun p  ->
         match p.FStar_Tactics_Types.goals with
         | [] -> fail "No more goals (1)"
         | hd1::tl1 -> ret hd1)
  
let (tadmit : Prims.unit -> Prims.unit tac) =
  fun uu____1516  ->
    let uu____1519 =
      let uu____1522 = cur_goal ()  in
      bind uu____1522
        (fun g  ->
           (let uu____1529 =
              let uu____1534 =
                let uu____1535 = goal_to_string g  in
                FStar_Util.format1 "Tactics admitted goal <%s>\n\n"
                  uu____1535
                 in
              (FStar_Errors.Warning_TacAdmit, uu____1534)  in
            FStar_Errors.log_issue
              (g.FStar_Tactics_Types.goal_ty).FStar_Syntax_Syntax.pos
              uu____1529);
           solve g FStar_Syntax_Util.exp_unit)
       in
    FStar_All.pipe_left (wrap_err "tadmit") uu____1519
  
let (fresh : Prims.unit -> FStar_BigInt.t tac) =
  fun uu____1544  ->
    bind get
      (fun ps  ->
         let n1 = ps.FStar_Tactics_Types.freshness  in
         let ps1 =
           let uu___77_1554 = ps  in
           {
             FStar_Tactics_Types.main_context =
               (uu___77_1554.FStar_Tactics_Types.main_context);
             FStar_Tactics_Types.main_goal =
               (uu___77_1554.FStar_Tactics_Types.main_goal);
             FStar_Tactics_Types.all_implicits =
               (uu___77_1554.FStar_Tactics_Types.all_implicits);
             FStar_Tactics_Types.goals =
               (uu___77_1554.FStar_Tactics_Types.goals);
             FStar_Tactics_Types.smt_goals =
               (uu___77_1554.FStar_Tactics_Types.smt_goals);
             FStar_Tactics_Types.depth =
               (uu___77_1554.FStar_Tactics_Types.depth);
             FStar_Tactics_Types.__dump =
               (uu___77_1554.FStar_Tactics_Types.__dump);
             FStar_Tactics_Types.psc = (uu___77_1554.FStar_Tactics_Types.psc);
             FStar_Tactics_Types.entry_range =
               (uu___77_1554.FStar_Tactics_Types.entry_range);
             FStar_Tactics_Types.guard_policy =
               (uu___77_1554.FStar_Tactics_Types.guard_policy);
             FStar_Tactics_Types.freshness = (n1 + (Prims.parse_int "1"))
           }  in
         let uu____1555 = set ps1  in
         bind uu____1555
           (fun uu____1560  ->
              let uu____1561 = FStar_BigInt.of_int_fs n1  in ret uu____1561))
  
let (ngoals : Prims.unit -> FStar_BigInt.t tac) =
  fun uu____1566  ->
    bind get
      (fun ps  ->
         let n1 = FStar_List.length ps.FStar_Tactics_Types.goals  in
         let uu____1574 = FStar_BigInt.of_int_fs n1  in ret uu____1574)
  
let (ngoals_smt : Prims.unit -> FStar_BigInt.t tac) =
  fun uu____1585  ->
    bind get
      (fun ps  ->
         let n1 = FStar_List.length ps.FStar_Tactics_Types.smt_goals  in
         let uu____1593 = FStar_BigInt.of_int_fs n1  in ret uu____1593)
  
let (is_guard : Prims.unit -> Prims.bool tac) =
  fun uu____1604  ->
    let uu____1607 = cur_goal ()  in
    bind uu____1607 (fun g  -> ret g.FStar_Tactics_Types.is_guard)
  
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
            let uu____1631 = env.FStar_TypeChecker_Env.universe_of env phi
               in
            FStar_Syntax_Util.mk_squash uu____1631 phi  in
          let uu____1632 = new_uvar reason env typ  in
          bind uu____1632
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
             (fun uu____1677  ->
                let uu____1678 = tts e t  in
                FStar_Util.print1 "Tac> __tc(%s)\n" uu____1678)
             (fun uu____1680  ->
                try
                  let uu____1700 =
                    (ps.FStar_Tactics_Types.main_context).FStar_TypeChecker_Env.type_of
                      e t
                     in
                  ret uu____1700
                with
                | FStar_Errors.Err (uu____1727,msg) ->
                    let uu____1729 = tts e t  in
                    let uu____1730 =
                      let uu____1731 = FStar_TypeChecker_Env.all_binders e
                         in
                      FStar_All.pipe_right uu____1731
                        (FStar_Syntax_Print.binders_to_string ", ")
                       in
                    fail3 "Cannot type %s in context (%s). Error = (%s)"
                      uu____1729 uu____1730 msg
                | FStar_Errors.Error (uu____1738,msg,uu____1740) ->
                    let uu____1741 = tts e t  in
                    let uu____1742 =
                      let uu____1743 = FStar_TypeChecker_Env.all_binders e
                         in
                      FStar_All.pipe_right uu____1743
                        (FStar_Syntax_Print.binders_to_string ", ")
                       in
                    fail3 "Cannot type %s in context (%s). Error = (%s)"
                      uu____1741 uu____1742 msg))
  
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
  fun uu____1764  ->
    bind get (fun ps  -> ret ps.FStar_Tactics_Types.guard_policy)
  
let (set_guard_policy : FStar_Tactics_Types.guard_policy -> Prims.unit tac) =
  fun pol  ->
    bind get
      (fun ps  ->
         set
           (let uu___80_1780 = ps  in
            {
              FStar_Tactics_Types.main_context =
                (uu___80_1780.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___80_1780.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___80_1780.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___80_1780.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (uu___80_1780.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___80_1780.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___80_1780.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___80_1780.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___80_1780.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy = pol;
              FStar_Tactics_Types.freshness =
                (uu___80_1780.FStar_Tactics_Types.freshness)
            }))
  
let with_policy : 'a . FStar_Tactics_Types.guard_policy -> 'a tac -> 'a tac =
  fun pol  ->
    fun t  ->
      let uu____1799 = get_guard_policy ()  in
      bind uu____1799
        (fun old_pol  ->
           let uu____1805 = set_guard_policy pol  in
           bind uu____1805
             (fun uu____1809  ->
                bind t
                  (fun r  ->
                     let uu____1813 = set_guard_policy old_pol  in
                     bind uu____1813 (fun uu____1817  -> ret r))))
  
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
          let uu____1834 =
            let uu____1835 = FStar_TypeChecker_Rel.simplify_guard e g  in
            uu____1835.FStar_TypeChecker_Env.guard_f  in
          match uu____1834 with
          | FStar_TypeChecker_Common.Trivial  -> ret ()
          | FStar_TypeChecker_Common.NonTrivial f ->
              let uu____1839 = istrivial e f  in
              if uu____1839
              then ret ()
              else
                bind get
                  (fun ps  ->
                     match ps.FStar_Tactics_Types.guard_policy with
                     | FStar_Tactics_Types.Drop  -> ret ()
                     | FStar_Tactics_Types.Goal  ->
                         let uu____1847 = mk_irrelevant_goal reason e f opts
                            in
                         bind uu____1847
                           (fun goal  ->
                              let goal1 =
                                let uu___81_1854 = goal  in
                                {
                                  FStar_Tactics_Types.context =
                                    (uu___81_1854.FStar_Tactics_Types.context);
                                  FStar_Tactics_Types.witness =
                                    (uu___81_1854.FStar_Tactics_Types.witness);
                                  FStar_Tactics_Types.goal_ty =
                                    (uu___81_1854.FStar_Tactics_Types.goal_ty);
                                  FStar_Tactics_Types.opts =
                                    (uu___81_1854.FStar_Tactics_Types.opts);
                                  FStar_Tactics_Types.is_guard = true
                                }  in
                              push_goals [goal1])
                     | FStar_Tactics_Types.SMT  ->
                         let uu____1855 = mk_irrelevant_goal reason e f opts
                            in
                         bind uu____1855
                           (fun goal  ->
                              let goal1 =
                                let uu___82_1862 = goal  in
                                {
                                  FStar_Tactics_Types.context =
                                    (uu___82_1862.FStar_Tactics_Types.context);
                                  FStar_Tactics_Types.witness =
                                    (uu___82_1862.FStar_Tactics_Types.witness);
                                  FStar_Tactics_Types.goal_ty =
                                    (uu___82_1862.FStar_Tactics_Types.goal_ty);
                                  FStar_Tactics_Types.opts =
                                    (uu___82_1862.FStar_Tactics_Types.opts);
                                  FStar_Tactics_Types.is_guard = true
                                }  in
                              push_smt_goals [goal1])
                     | FStar_Tactics_Types.Force  ->
                         (try
                            let uu____1870 =
                              let uu____1871 =
                                let uu____1872 =
                                  FStar_TypeChecker_Rel.discharge_guard_no_smt
                                    e g
                                   in
                                FStar_All.pipe_left
                                  FStar_TypeChecker_Rel.is_trivial uu____1872
                                 in
                              Prims.op_Negation uu____1871  in
                            if uu____1870
                            then
                              mlog
                                (fun uu____1877  ->
                                   let uu____1878 =
                                     FStar_TypeChecker_Rel.guard_to_string e
                                       g
                                      in
                                   FStar_Util.print1 "guard = %s\n"
                                     uu____1878)
                                (fun uu____1880  ->
                                   fail1 "Forcing the guard failed %s)"
                                     reason)
                            else ret ()
                          with
                          | uu____1887 ->
                              mlog
                                (fun uu____1890  ->
                                   let uu____1891 =
                                     FStar_TypeChecker_Rel.guard_to_string e
                                       g
                                      in
                                   FStar_Util.print1 "guard = %s\n"
                                     uu____1891)
                                (fun uu____1893  ->
                                   fail1 "Forcing the guard failed (%s)"
                                     reason)))
  
let (tc : FStar_Syntax_Syntax.term -> FStar_Reflection_Data.typ tac) =
  fun t  ->
    let uu____1901 =
      let uu____1904 = cur_goal ()  in
      bind uu____1904
        (fun goal  ->
           let uu____1910 = __tc goal.FStar_Tactics_Types.context t  in
           bind uu____1910
             (fun uu____1930  ->
                match uu____1930 with
                | (t1,typ,guard) ->
                    let uu____1942 =
                      proc_guard "tc" goal.FStar_Tactics_Types.context guard
                        goal.FStar_Tactics_Types.opts
                       in
                    bind uu____1942 (fun uu____1946  -> ret typ)))
       in
    FStar_All.pipe_left (wrap_err "tc") uu____1901
  
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
          let uu____1967 = mk_irrelevant_goal reason env phi opts  in
          bind uu____1967 (fun goal  -> add_goals [goal])
  
let (trivial : Prims.unit -> Prims.unit tac) =
  fun uu____1976  ->
    let uu____1979 = cur_goal ()  in
    bind uu____1979
      (fun goal  ->
         let uu____1985 =
           istrivial goal.FStar_Tactics_Types.context
             goal.FStar_Tactics_Types.goal_ty
            in
         if uu____1985
         then solve goal FStar_Syntax_Util.exp_unit
         else
           (let uu____1989 =
              tts goal.FStar_Tactics_Types.context
                goal.FStar_Tactics_Types.goal_ty
               in
            fail1 "Not a trivial goal: %s" uu____1989))
  
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
          let uu____2010 =
            let uu____2011 = FStar_TypeChecker_Rel.simplify_guard e g  in
            uu____2011.FStar_TypeChecker_Env.guard_f  in
          match uu____2010 with
          | FStar_TypeChecker_Common.Trivial  ->
              ret FStar_Pervasives_Native.None
          | FStar_TypeChecker_Common.NonTrivial f ->
              let uu____2019 = istrivial e f  in
              if uu____2019
              then ret FStar_Pervasives_Native.None
              else
                (let uu____2027 = mk_irrelevant_goal reason e f opts  in
                 bind uu____2027
                   (fun goal  ->
                      ret
                        (FStar_Pervasives_Native.Some
                           (let uu___85_2037 = goal  in
                            {
                              FStar_Tactics_Types.context =
                                (uu___85_2037.FStar_Tactics_Types.context);
                              FStar_Tactics_Types.witness =
                                (uu___85_2037.FStar_Tactics_Types.witness);
                              FStar_Tactics_Types.goal_ty =
                                (uu___85_2037.FStar_Tactics_Types.goal_ty);
                              FStar_Tactics_Types.opts =
                                (uu___85_2037.FStar_Tactics_Types.opts);
                              FStar_Tactics_Types.is_guard = true
                            }))))
  
let (smt : Prims.unit -> Prims.unit tac) =
  fun uu____2042  ->
    let uu____2045 = cur_goal ()  in
    bind uu____2045
      (fun g  ->
         let uu____2051 = is_irrelevant g  in
         if uu____2051
         then bind __dismiss (fun uu____2055  -> add_smt_goals [g])
         else
           (let uu____2057 =
              tts g.FStar_Tactics_Types.context g.FStar_Tactics_Types.goal_ty
               in
            fail1 "goal is not irrelevant: cannot dispatch to smt (%s)"
              uu____2057))
  
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
             let uu____2098 =
               try
                 let uu____2132 =
                   let uu____2141 = FStar_BigInt.to_int_fs n1  in
                   FStar_List.splitAt uu____2141 p.FStar_Tactics_Types.goals
                    in
                 ret uu____2132
               with | uu____2163 -> fail "divide: not enough goals"  in
             bind uu____2098
               (fun uu____2190  ->
                  match uu____2190 with
                  | (lgs,rgs) ->
                      let lp =
                        let uu___86_2216 = p  in
                        {
                          FStar_Tactics_Types.main_context =
                            (uu___86_2216.FStar_Tactics_Types.main_context);
                          FStar_Tactics_Types.main_goal =
                            (uu___86_2216.FStar_Tactics_Types.main_goal);
                          FStar_Tactics_Types.all_implicits =
                            (uu___86_2216.FStar_Tactics_Types.all_implicits);
                          FStar_Tactics_Types.goals = lgs;
                          FStar_Tactics_Types.smt_goals = [];
                          FStar_Tactics_Types.depth =
                            (uu___86_2216.FStar_Tactics_Types.depth);
                          FStar_Tactics_Types.__dump =
                            (uu___86_2216.FStar_Tactics_Types.__dump);
                          FStar_Tactics_Types.psc =
                            (uu___86_2216.FStar_Tactics_Types.psc);
                          FStar_Tactics_Types.entry_range =
                            (uu___86_2216.FStar_Tactics_Types.entry_range);
                          FStar_Tactics_Types.guard_policy =
                            (uu___86_2216.FStar_Tactics_Types.guard_policy);
                          FStar_Tactics_Types.freshness =
                            (uu___86_2216.FStar_Tactics_Types.freshness)
                        }  in
                      let rp =
                        let uu___87_2218 = p  in
                        {
                          FStar_Tactics_Types.main_context =
                            (uu___87_2218.FStar_Tactics_Types.main_context);
                          FStar_Tactics_Types.main_goal =
                            (uu___87_2218.FStar_Tactics_Types.main_goal);
                          FStar_Tactics_Types.all_implicits =
                            (uu___87_2218.FStar_Tactics_Types.all_implicits);
                          FStar_Tactics_Types.goals = rgs;
                          FStar_Tactics_Types.smt_goals = [];
                          FStar_Tactics_Types.depth =
                            (uu___87_2218.FStar_Tactics_Types.depth);
                          FStar_Tactics_Types.__dump =
                            (uu___87_2218.FStar_Tactics_Types.__dump);
                          FStar_Tactics_Types.psc =
                            (uu___87_2218.FStar_Tactics_Types.psc);
                          FStar_Tactics_Types.entry_range =
                            (uu___87_2218.FStar_Tactics_Types.entry_range);
                          FStar_Tactics_Types.guard_policy =
                            (uu___87_2218.FStar_Tactics_Types.guard_policy);
                          FStar_Tactics_Types.freshness =
                            (uu___87_2218.FStar_Tactics_Types.freshness)
                        }  in
                      let uu____2219 = set lp  in
                      bind uu____2219
                        (fun uu____2227  ->
                           bind l
                             (fun a  ->
                                bind get
                                  (fun lp'  ->
                                     let uu____2241 = set rp  in
                                     bind uu____2241
                                       (fun uu____2249  ->
                                          bind r
                                            (fun b  ->
                                               bind get
                                                 (fun rp'  ->
                                                    let p' =
                                                      let uu___88_2265 = p
                                                         in
                                                      {
                                                        FStar_Tactics_Types.main_context
                                                          =
                                                          (uu___88_2265.FStar_Tactics_Types.main_context);
                                                        FStar_Tactics_Types.main_goal
                                                          =
                                                          (uu___88_2265.FStar_Tactics_Types.main_goal);
                                                        FStar_Tactics_Types.all_implicits
                                                          =
                                                          (uu___88_2265.FStar_Tactics_Types.all_implicits);
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
                                                          (uu___88_2265.FStar_Tactics_Types.depth);
                                                        FStar_Tactics_Types.__dump
                                                          =
                                                          (uu___88_2265.FStar_Tactics_Types.__dump);
                                                        FStar_Tactics_Types.psc
                                                          =
                                                          (uu___88_2265.FStar_Tactics_Types.psc);
                                                        FStar_Tactics_Types.entry_range
                                                          =
                                                          (uu___88_2265.FStar_Tactics_Types.entry_range);
                                                        FStar_Tactics_Types.guard_policy
                                                          =
                                                          (uu___88_2265.FStar_Tactics_Types.guard_policy);
                                                        FStar_Tactics_Types.freshness
                                                          =
                                                          (uu___88_2265.FStar_Tactics_Types.freshness)
                                                      }  in
                                                    let uu____2266 = set p'
                                                       in
                                                    bind uu____2266
                                                      (fun uu____2274  ->
                                                         ret (a, b))))))))))
  
let focus : 'a . 'a tac -> 'a tac =
  fun f  ->
    let uu____2292 = divide FStar_BigInt.one f idtac  in
    bind uu____2292
      (fun uu____2305  -> match uu____2305 with | (a,()) -> ret a)
  
let rec map : 'a . 'a tac -> 'a Prims.list tac =
  fun tau  ->
    bind get
      (fun p  ->
         match p.FStar_Tactics_Types.goals with
         | [] -> ret []
         | uu____2339::uu____2340 ->
             let uu____2343 =
               let uu____2352 = map tau  in
               divide FStar_BigInt.one tau uu____2352  in
             bind uu____2343
               (fun uu____2370  ->
                  match uu____2370 with | (h,t) -> ret (h :: t)))
  
let (seq : Prims.unit tac -> Prims.unit tac -> Prims.unit tac) =
  fun t1  ->
    fun t2  ->
      let uu____2407 =
        bind t1
          (fun uu____2412  ->
             let uu____2413 = map t2  in
             bind uu____2413 (fun uu____2421  -> ret ()))
         in
      focus uu____2407
  
let (intro : Prims.unit -> FStar_Syntax_Syntax.binder tac) =
  fun uu____2428  ->
    let uu____2431 =
      let uu____2434 = cur_goal ()  in
      bind uu____2434
        (fun goal  ->
           let uu____2443 =
             FStar_Syntax_Util.arrow_one goal.FStar_Tactics_Types.goal_ty  in
           match uu____2443 with
           | FStar_Pervasives_Native.Some (b,c) ->
               let uu____2458 =
                 let uu____2459 = FStar_Syntax_Util.is_total_comp c  in
                 Prims.op_Negation uu____2459  in
               if uu____2458
               then fail "Codomain is effectful"
               else
                 (let env' =
                    FStar_TypeChecker_Env.push_binders
                      goal.FStar_Tactics_Types.context [b]
                     in
                  let typ' = comp_to_typ c  in
                  let uu____2465 = new_uvar "intro" env' typ'  in
                  bind uu____2465
                    (fun u  ->
                       let uu____2471 =
                         let uu____2474 =
                           FStar_Syntax_Util.abs [b] u
                             FStar_Pervasives_Native.None
                            in
                         trysolve goal uu____2474  in
                       bind uu____2471
                         (fun bb  ->
                            if bb
                            then
                              let uu____2480 =
                                let uu____2483 =
                                  let uu___91_2484 = goal  in
                                  let uu____2485 = bnorm env' u  in
                                  let uu____2486 = bnorm env' typ'  in
                                  {
                                    FStar_Tactics_Types.context = env';
                                    FStar_Tactics_Types.witness = uu____2485;
                                    FStar_Tactics_Types.goal_ty = uu____2486;
                                    FStar_Tactics_Types.opts =
                                      (uu___91_2484.FStar_Tactics_Types.opts);
                                    FStar_Tactics_Types.is_guard =
                                      (uu___91_2484.FStar_Tactics_Types.is_guard)
                                  }  in
                                replace_cur uu____2483  in
                              bind uu____2480 (fun uu____2488  -> ret b)
                            else fail "unification failed")))
           | FStar_Pervasives_Native.None  ->
               let uu____2494 =
                 tts goal.FStar_Tactics_Types.context
                   goal.FStar_Tactics_Types.goal_ty
                  in
               fail1 "goal is not an arrow (%s)" uu____2494)
       in
    FStar_All.pipe_left (wrap_err "intro") uu____2431
  
let (intro_rec :
  Prims.unit ->
    (FStar_Syntax_Syntax.binder,FStar_Syntax_Syntax.binder)
      FStar_Pervasives_Native.tuple2 tac)
  =
  fun uu____2507  ->
    let uu____2514 = cur_goal ()  in
    bind uu____2514
      (fun goal  ->
         FStar_Util.print_string
           "WARNING (intro_rec): calling this is known to cause normalizer loops\n";
         FStar_Util.print_string
           "WARNING (intro_rec): proceed at your own risk...\n";
         (let uu____2531 =
            FStar_Syntax_Util.arrow_one goal.FStar_Tactics_Types.goal_ty  in
          match uu____2531 with
          | FStar_Pervasives_Native.Some (b,c) ->
              let uu____2550 =
                let uu____2551 = FStar_Syntax_Util.is_total_comp c  in
                Prims.op_Negation uu____2551  in
              if uu____2550
              then fail "Codomain is effectful"
              else
                (let bv =
                   FStar_Syntax_Syntax.gen_bv "__recf"
                     FStar_Pervasives_Native.None
                     goal.FStar_Tactics_Types.goal_ty
                    in
                 let bs =
                   let uu____2567 = FStar_Syntax_Syntax.mk_binder bv  in
                   [uu____2567; b]  in
                 let env' =
                   FStar_TypeChecker_Env.push_binders
                     goal.FStar_Tactics_Types.context bs
                    in
                 let uu____2569 =
                   let uu____2572 = comp_to_typ c  in
                   new_uvar "intro_rec" env' uu____2572  in
                 bind uu____2569
                   (fun u  ->
                      let lb =
                        let uu____2587 =
                          FStar_Syntax_Util.abs [b] u
                            FStar_Pervasives_Native.None
                           in
                        FStar_Syntax_Util.mk_letbinding (FStar_Util.Inl bv)
                          [] goal.FStar_Tactics_Types.goal_ty
                          FStar_Parser_Const.effect_Tot_lid uu____2587 []
                          FStar_Range.dummyRange
                         in
                      let body = FStar_Syntax_Syntax.bv_to_name bv  in
                      let uu____2593 =
                        FStar_Syntax_Subst.close_let_rec [lb] body  in
                      match uu____2593 with
                      | (lbs,body1) ->
                          let tm =
                            FStar_Syntax_Syntax.mk
                              (FStar_Syntax_Syntax.Tm_let
                                 ((true, lbs), body1))
                              FStar_Pervasives_Native.None
                              (goal.FStar_Tactics_Types.witness).FStar_Syntax_Syntax.pos
                             in
                          let uu____2623 = trysolve goal tm  in
                          bind uu____2623
                            (fun bb  ->
                               if bb
                               then
                                 let uu____2639 =
                                   let uu____2642 =
                                     let uu___92_2643 = goal  in
                                     let uu____2644 = bnorm env' u  in
                                     let uu____2645 =
                                       let uu____2646 = comp_to_typ c  in
                                       bnorm env' uu____2646  in
                                     {
                                       FStar_Tactics_Types.context = env';
                                       FStar_Tactics_Types.witness =
                                         uu____2644;
                                       FStar_Tactics_Types.goal_ty =
                                         uu____2645;
                                       FStar_Tactics_Types.opts =
                                         (uu___92_2643.FStar_Tactics_Types.opts);
                                       FStar_Tactics_Types.is_guard =
                                         (uu___92_2643.FStar_Tactics_Types.is_guard)
                                     }  in
                                   replace_cur uu____2642  in
                                 bind uu____2639
                                   (fun uu____2653  ->
                                      let uu____2654 =
                                        let uu____2659 =
                                          FStar_Syntax_Syntax.mk_binder bv
                                           in
                                        (uu____2659, b)  in
                                      ret uu____2654)
                               else fail "intro_rec: unification failed")))
          | FStar_Pervasives_Native.None  ->
              let uu____2673 =
                tts goal.FStar_Tactics_Types.context
                  goal.FStar_Tactics_Types.goal_ty
                 in
              fail1 "intro_rec: goal is not an arrow (%s)" uu____2673))
  
let (norm : FStar_Syntax_Embeddings.norm_step Prims.list -> Prims.unit tac) =
  fun s  ->
    let uu____2689 = cur_goal ()  in
    bind uu____2689
      (fun goal  ->
         mlog
           (fun uu____2696  ->
              let uu____2697 =
                FStar_Syntax_Print.term_to_string
                  goal.FStar_Tactics_Types.witness
                 in
              FStar_Util.print1 "norm: witness = %s\n" uu____2697)
           (fun uu____2702  ->
              let steps =
                let uu____2706 = FStar_TypeChecker_Normalize.tr_norm_steps s
                   in
                FStar_List.append
                  [FStar_TypeChecker_Normalize.Reify;
                  FStar_TypeChecker_Normalize.UnfoldTac] uu____2706
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
                (let uu___93_2713 = goal  in
                 {
                   FStar_Tactics_Types.context =
                     (uu___93_2713.FStar_Tactics_Types.context);
                   FStar_Tactics_Types.witness = w;
                   FStar_Tactics_Types.goal_ty = t;
                   FStar_Tactics_Types.opts =
                     (uu___93_2713.FStar_Tactics_Types.opts);
                   FStar_Tactics_Types.is_guard =
                     (uu___93_2713.FStar_Tactics_Types.is_guard)
                 })))
  
let (norm_term_env :
  env ->
    FStar_Syntax_Embeddings.norm_step Prims.list ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term tac)
  =
  fun e  ->
    fun s  ->
      fun t  ->
        let uu____2731 =
          mlog
            (fun uu____2736  ->
               let uu____2737 = FStar_Syntax_Print.term_to_string t  in
               FStar_Util.print1 "norm_term: tm = %s\n" uu____2737)
            (fun uu____2739  ->
               bind get
                 (fun ps  ->
                    let opts =
                      match ps.FStar_Tactics_Types.goals with
                      | g::uu____2745 -> g.FStar_Tactics_Types.opts
                      | uu____2748 -> FStar_Options.peek ()  in
                    mlog
                      (fun uu____2753  ->
                         let uu____2754 =
                           tts ps.FStar_Tactics_Types.main_context t  in
                         FStar_Util.print1 "norm_term_env: t = %s\n"
                           uu____2754)
                      (fun uu____2757  ->
                         let uu____2758 = __tc e t  in
                         bind uu____2758
                           (fun uu____2779  ->
                              match uu____2779 with
                              | (t1,uu____2789,uu____2790) ->
                                  let steps =
                                    let uu____2794 =
                                      FStar_TypeChecker_Normalize.tr_norm_steps
                                        s
                                       in
                                    FStar_List.append
                                      [FStar_TypeChecker_Normalize.Reify;
                                      FStar_TypeChecker_Normalize.UnfoldTac]
                                      uu____2794
                                     in
                                  let t2 =
                                    normalize steps
                                      ps.FStar_Tactics_Types.main_context t1
                                     in
                                  ret t2))))
           in
        FStar_All.pipe_left (wrap_err "norm_term") uu____2731
  
let (refine_intro : Prims.unit -> Prims.unit tac) =
  fun uu____2806  ->
    let uu____2809 =
      let uu____2812 = cur_goal ()  in
      bind uu____2812
        (fun g  ->
           let uu____2819 =
             FStar_TypeChecker_Rel.base_and_refinement
               g.FStar_Tactics_Types.context g.FStar_Tactics_Types.goal_ty
              in
           match uu____2819 with
           | (uu____2832,FStar_Pervasives_Native.None ) ->
               fail "not a refinement"
           | (t,FStar_Pervasives_Native.Some (bv,phi)) ->
               let g1 =
                 let uu___94_2857 = g  in
                 {
                   FStar_Tactics_Types.context =
                     (uu___94_2857.FStar_Tactics_Types.context);
                   FStar_Tactics_Types.witness =
                     (uu___94_2857.FStar_Tactics_Types.witness);
                   FStar_Tactics_Types.goal_ty = t;
                   FStar_Tactics_Types.opts =
                     (uu___94_2857.FStar_Tactics_Types.opts);
                   FStar_Tactics_Types.is_guard =
                     (uu___94_2857.FStar_Tactics_Types.is_guard)
                 }  in
               let uu____2858 =
                 let uu____2863 =
                   let uu____2868 =
                     let uu____2869 = FStar_Syntax_Syntax.mk_binder bv  in
                     [uu____2869]  in
                   FStar_Syntax_Subst.open_term uu____2868 phi  in
                 match uu____2863 with
                 | (bvs,phi1) ->
                     let uu____2876 =
                       let uu____2877 = FStar_List.hd bvs  in
                       FStar_Pervasives_Native.fst uu____2877  in
                     (uu____2876, phi1)
                  in
               (match uu____2858 with
                | (bv1,phi1) ->
                    let uu____2890 =
                      let uu____2893 =
                        FStar_Syntax_Subst.subst
                          [FStar_Syntax_Syntax.NT
                             (bv1, (g.FStar_Tactics_Types.witness))] phi1
                         in
                      mk_irrelevant_goal "refine_intro refinement"
                        g.FStar_Tactics_Types.context uu____2893
                        g.FStar_Tactics_Types.opts
                       in
                    bind uu____2890
                      (fun g2  ->
                         bind __dismiss
                           (fun uu____2897  -> add_goals [g1; g2]))))
       in
    FStar_All.pipe_left (wrap_err "refine_intro") uu____2809
  
let (__exact_now : Prims.bool -> FStar_Syntax_Syntax.term -> Prims.unit tac)
  =
  fun set_expected_typ1  ->
    fun t  ->
      let uu____2912 = cur_goal ()  in
      bind uu____2912
        (fun goal  ->
           let env =
             if set_expected_typ1
             then
               FStar_TypeChecker_Env.set_expected_typ
                 goal.FStar_Tactics_Types.context
                 goal.FStar_Tactics_Types.goal_ty
             else goal.FStar_Tactics_Types.context  in
           let uu____2921 = __tc env t  in
           bind uu____2921
             (fun uu____2940  ->
                match uu____2940 with
                | (t1,typ,guard) ->
                    mlog
                      (fun uu____2955  ->
                         let uu____2956 =
                           tts goal.FStar_Tactics_Types.context typ  in
                         let uu____2957 =
                           FStar_TypeChecker_Rel.guard_to_string
                             goal.FStar_Tactics_Types.context guard
                            in
                         FStar_Util.print2
                           "__exact_now: got type %s\n__exact_now and guard %s\n"
                           uu____2956 uu____2957)
                      (fun uu____2960  ->
                         let uu____2961 =
                           proc_guard "__exact typing"
                             goal.FStar_Tactics_Types.context guard
                             goal.FStar_Tactics_Types.opts
                            in
                         bind uu____2961
                           (fun uu____2965  ->
                              mlog
                                (fun uu____2969  ->
                                   let uu____2970 =
                                     tts goal.FStar_Tactics_Types.context typ
                                      in
                                   let uu____2971 =
                                     tts goal.FStar_Tactics_Types.context
                                       goal.FStar_Tactics_Types.goal_ty
                                      in
                                   FStar_Util.print2
                                     "__exact_now: unifying %s and %s\n"
                                     uu____2970 uu____2971)
                                (fun uu____2974  ->
                                   let uu____2975 =
                                     do_unify
                                       goal.FStar_Tactics_Types.context typ
                                       goal.FStar_Tactics_Types.goal_ty
                                      in
                                   bind uu____2975
                                     (fun b  ->
                                        if b
                                        then solve goal t1
                                        else
                                          (let uu____2983 =
                                             tts
                                               goal.FStar_Tactics_Types.context
                                               t1
                                              in
                                           let uu____2984 =
                                             tts
                                               goal.FStar_Tactics_Types.context
                                               typ
                                              in
                                           let uu____2985 =
                                             tts
                                               goal.FStar_Tactics_Types.context
                                               goal.FStar_Tactics_Types.goal_ty
                                              in
                                           let uu____2986 =
                                             tts
                                               goal.FStar_Tactics_Types.context
                                               goal.FStar_Tactics_Types.witness
                                              in
                                           fail4
                                             "%s : %s does not exactly solve the goal %s (witness = %s)"
                                             uu____2983 uu____2984 uu____2985
                                             uu____2986)))))))
  
let (t_exact : Prims.bool -> FStar_Syntax_Syntax.term -> Prims.unit tac) =
  fun set_expected_typ1  ->
    fun tm  ->
      let uu____2997 =
        mlog
          (fun uu____3002  ->
             let uu____3003 = FStar_Syntax_Print.term_to_string tm  in
             FStar_Util.print1 "t_exact: tm = %s\n" uu____3003)
          (fun uu____3006  ->
             let uu____3007 =
               let uu____3014 = __exact_now set_expected_typ1 tm  in
               trytac' uu____3014  in
             bind uu____3007
               (fun uu___60_3023  ->
                  match uu___60_3023 with
                  | FStar_Util.Inr r -> ret ()
                  | FStar_Util.Inl e ->
                      let uu____3032 =
                        let uu____3039 =
                          let uu____3042 =
                            norm [FStar_Syntax_Embeddings.Delta]  in
                          bind uu____3042
                            (fun uu____3047  ->
                               let uu____3048 = refine_intro ()  in
                               bind uu____3048
                                 (fun uu____3052  ->
                                    __exact_now set_expected_typ1 tm))
                           in
                        trytac' uu____3039  in
                      bind uu____3032
                        (fun uu___59_3059  ->
                           match uu___59_3059 with
                           | FStar_Util.Inr r -> ret ()
                           | FStar_Util.Inl uu____3067 -> fail e)))
         in
      FStar_All.pipe_left (wrap_err "exact") uu____2997
  
let (uvar_free_in_goal :
  FStar_Syntax_Syntax.uvar -> FStar_Tactics_Types.goal -> Prims.bool) =
  fun u  ->
    fun g  ->
      if g.FStar_Tactics_Types.is_guard
      then false
      else
        (let free_uvars =
           let uu____3082 =
             let uu____3089 =
               FStar_Syntax_Free.uvars g.FStar_Tactics_Types.goal_ty  in
             FStar_Util.set_elements uu____3089  in
           FStar_List.map FStar_Pervasives_Native.fst uu____3082  in
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
          let uu____3149 = f x  in
          bind uu____3149
            (fun y  ->
               let uu____3157 = mapM f xs  in
               bind uu____3157 (fun ys  -> ret (y :: ys)))
  
exception NoUnif 
let (uu___is_NoUnif : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with | NoUnif  -> true | uu____3175 -> false
  
let rec (__apply :
  Prims.bool ->
    FStar_Syntax_Syntax.term -> FStar_Reflection_Data.typ -> Prims.unit tac)
  =
  fun uopt  ->
    fun tm  ->
      fun typ  ->
        let uu____3189 = cur_goal ()  in
        bind uu____3189
          (fun goal  ->
             mlog
               (fun uu____3196  ->
                  let uu____3197 = FStar_Syntax_Print.term_to_string tm  in
                  FStar_Util.print1 ">>> Calling __exact(%s)\n" uu____3197)
               (fun uu____3200  ->
                  let uu____3201 =
                    let uu____3206 =
                      let uu____3209 = t_exact false tm  in
                      with_policy FStar_Tactics_Types.Force uu____3209  in
                    trytac_exn uu____3206  in
                  bind uu____3201
                    (fun uu___61_3216  ->
                       match uu___61_3216 with
                       | FStar_Pervasives_Native.Some r -> ret ()
                       | FStar_Pervasives_Native.None  ->
                           mlog
                             (fun uu____3224  ->
                                let uu____3225 =
                                  FStar_Syntax_Print.term_to_string typ  in
                                FStar_Util.print1 ">>> typ = %s\n" uu____3225)
                             (fun uu____3228  ->
                                let uu____3229 =
                                  FStar_Syntax_Util.arrow_one typ  in
                                match uu____3229 with
                                | FStar_Pervasives_Native.None  ->
                                    FStar_Exn.raise NoUnif
                                | FStar_Pervasives_Native.Some ((bv,aq),c) ->
                                    mlog
                                      (fun uu____3261  ->
                                         let uu____3262 =
                                           FStar_Syntax_Print.binder_to_string
                                             (bv, aq)
                                            in
                                         FStar_Util.print1
                                           "__apply: pushing binder %s\n"
                                           uu____3262)
                                      (fun uu____3265  ->
                                         let uu____3266 =
                                           let uu____3267 =
                                             FStar_Syntax_Util.is_total_comp
                                               c
                                              in
                                           Prims.op_Negation uu____3267  in
                                         if uu____3266
                                         then
                                           fail "apply: not total codomain"
                                         else
                                           (let uu____3271 =
                                              new_uvar "apply"
                                                goal.FStar_Tactics_Types.context
                                                bv.FStar_Syntax_Syntax.sort
                                               in
                                            bind uu____3271
                                              (fun u  ->
                                                 let tm' =
                                                   FStar_Syntax_Syntax.mk_Tm_app
                                                     tm [(u, aq)]
                                                     FStar_Pervasives_Native.None
                                                     tm.FStar_Syntax_Syntax.pos
                                                    in
                                                 let typ' =
                                                   let uu____3291 =
                                                     comp_to_typ c  in
                                                   FStar_All.pipe_left
                                                     (FStar_Syntax_Subst.subst
                                                        [FStar_Syntax_Syntax.NT
                                                           (bv, u)])
                                                     uu____3291
                                                    in
                                                 let uu____3292 =
                                                   __apply uopt tm' typ'  in
                                                 bind uu____3292
                                                   (fun uu____3300  ->
                                                      let u1 =
                                                        bnorm
                                                          goal.FStar_Tactics_Types.context
                                                          u
                                                         in
                                                      let uu____3302 =
                                                        let uu____3303 =
                                                          let uu____3306 =
                                                            let uu____3307 =
                                                              FStar_Syntax_Util.head_and_args
                                                                u1
                                                               in
                                                            FStar_Pervasives_Native.fst
                                                              uu____3307
                                                             in
                                                          FStar_Syntax_Subst.compress
                                                            uu____3306
                                                           in
                                                        uu____3303.FStar_Syntax_Syntax.n
                                                         in
                                                      match uu____3302 with
                                                      | FStar_Syntax_Syntax.Tm_uvar
                                                          (uvar,uu____3335)
                                                          ->
                                                          bind get
                                                            (fun ps  ->
                                                               let uu____3363
                                                                 =
                                                                 uopt &&
                                                                   (uvar_free
                                                                    uvar ps)
                                                                  in
                                                               if uu____3363
                                                               then ret ()
                                                               else
                                                                 (let uu____3367
                                                                    =
                                                                    let uu____3370
                                                                    =
                                                                    let uu___95_3371
                                                                    = goal
                                                                     in
                                                                    let uu____3372
                                                                    =
                                                                    bnorm
                                                                    goal.FStar_Tactics_Types.context
                                                                    u1  in
                                                                    let uu____3373
                                                                    =
                                                                    bnorm
                                                                    goal.FStar_Tactics_Types.context
                                                                    bv.FStar_Syntax_Syntax.sort
                                                                     in
                                                                    {
                                                                    FStar_Tactics_Types.context
                                                                    =
                                                                    (uu___95_3371.FStar_Tactics_Types.context);
                                                                    FStar_Tactics_Types.witness
                                                                    =
                                                                    uu____3372;
                                                                    FStar_Tactics_Types.goal_ty
                                                                    =
                                                                    uu____3373;
                                                                    FStar_Tactics_Types.opts
                                                                    =
                                                                    (uu___95_3371.FStar_Tactics_Types.opts);
                                                                    FStar_Tactics_Types.is_guard
                                                                    = false
                                                                    }  in
                                                                    [uu____3370]
                                                                     in
                                                                  add_goals
                                                                    uu____3367))
                                                      | t -> ret ()))))))))
  
let try_unif : 'a . 'a tac -> 'a tac -> 'a tac =
  fun t  ->
    fun t'  -> mk_tac (fun ps  -> try run t ps with | NoUnif  -> run t' ps)
  
let (apply : Prims.bool -> FStar_Syntax_Syntax.term -> Prims.unit tac) =
  fun uopt  ->
    fun tm  ->
      let uu____3419 =
        mlog
          (fun uu____3424  ->
             let uu____3425 = FStar_Syntax_Print.term_to_string tm  in
             FStar_Util.print1 "apply: tm = %s\n" uu____3425)
          (fun uu____3428  ->
             let uu____3429 = cur_goal ()  in
             bind uu____3429
               (fun goal  ->
                  let uu____3435 = __tc goal.FStar_Tactics_Types.context tm
                     in
                  bind uu____3435
                    (fun uu____3457  ->
                       match uu____3457 with
                       | (tm1,typ,guard) ->
                           let typ1 =
                             bnorm goal.FStar_Tactics_Types.context typ  in
                           let uu____3470 =
                             let uu____3473 =
                               let uu____3476 = __apply uopt tm1 typ1  in
                               bind uu____3476
                                 (fun uu____3480  ->
                                    proc_guard "apply guard"
                                      goal.FStar_Tactics_Types.context guard
                                      goal.FStar_Tactics_Types.opts)
                                in
                             focus uu____3473  in
                           let uu____3481 =
                             let uu____3484 =
                               tts goal.FStar_Tactics_Types.context tm1  in
                             let uu____3485 =
                               tts goal.FStar_Tactics_Types.context typ1  in
                             let uu____3486 =
                               tts goal.FStar_Tactics_Types.context
                                 goal.FStar_Tactics_Types.goal_ty
                                in
                             fail3
                               "Cannot instantiate %s (of type %s) to match goal (%s)"
                               uu____3484 uu____3485 uu____3486
                              in
                           try_unif uu____3470 uu____3481)))
         in
      FStar_All.pipe_left (wrap_err "apply") uu____3419
  
let (lemma_or_sq :
  FStar_Syntax_Syntax.comp ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun c  ->
    let ct = FStar_Syntax_Util.comp_to_comp_typ_nouniv c  in
    let uu____3507 =
      FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
        FStar_Parser_Const.effect_Lemma_lid
       in
    if uu____3507
    then
      let uu____3514 =
        match ct.FStar_Syntax_Syntax.effect_args with
        | pre::post::uu____3533 ->
            ((FStar_Pervasives_Native.fst pre),
              (FStar_Pervasives_Native.fst post))
        | uu____3574 -> failwith "apply_lemma: impossible: not a lemma"  in
      match uu____3514 with
      | (pre,post) ->
          let post1 =
            let uu____3610 =
              let uu____3619 =
                FStar_Syntax_Syntax.as_arg FStar_Syntax_Util.exp_unit  in
              [uu____3619]  in
            FStar_Syntax_Util.mk_app post uu____3610  in
          FStar_Pervasives_Native.Some (pre, post1)
    else
      (let uu____3633 =
         FStar_Syntax_Util.is_pure_effect ct.FStar_Syntax_Syntax.effect_name
          in
       if uu____3633
       then
         let uu____3640 =
           FStar_Syntax_Util.un_squash ct.FStar_Syntax_Syntax.result_typ  in
         FStar_Util.map_opt uu____3640
           (fun post  -> (FStar_Syntax_Util.t_true, post))
       else FStar_Pervasives_Native.None)
  
let (apply_lemma : FStar_Syntax_Syntax.term -> Prims.unit tac) =
  fun tm  ->
    let uu____3671 =
      let uu____3674 =
        mlog
          (fun uu____3679  ->
             let uu____3680 = FStar_Syntax_Print.term_to_string tm  in
             FStar_Util.print1 "apply_lemma: tm = %s\n" uu____3680)
          (fun uu____3684  ->
             let is_unit_t t =
               let uu____3689 =
                 let uu____3690 = FStar_Syntax_Subst.compress t  in
                 uu____3690.FStar_Syntax_Syntax.n  in
               match uu____3689 with
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.unit_lid
                   -> true
               | uu____3694 -> false  in
             let uu____3695 = cur_goal ()  in
             bind uu____3695
               (fun goal  ->
                  let uu____3701 = __tc goal.FStar_Tactics_Types.context tm
                     in
                  bind uu____3701
                    (fun uu____3724  ->
                       match uu____3724 with
                       | (tm1,t,guard) ->
                           let uu____3736 =
                             FStar_Syntax_Util.arrow_formals_comp t  in
                           (match uu____3736 with
                            | (bs,comp) ->
                                let uu____3763 = lemma_or_sq comp  in
                                (match uu____3763 with
                                 | FStar_Pervasives_Native.None  ->
                                     fail "not a lemma or squashed function"
                                 | FStar_Pervasives_Native.Some (pre,post) ->
                                     let uu____3782 =
                                       FStar_List.fold_left
                                         (fun uu____3828  ->
                                            fun uu____3829  ->
                                              match (uu____3828, uu____3829)
                                              with
                                              | ((uvs,guard1,subst1),(b,aq))
                                                  ->
                                                  let b_t =
                                                    FStar_Syntax_Subst.subst
                                                      subst1
                                                      b.FStar_Syntax_Syntax.sort
                                                     in
                                                  let uu____3932 =
                                                    is_unit_t b_t  in
                                                  if uu____3932
                                                  then
                                                    (((FStar_Syntax_Util.exp_unit,
                                                        aq) :: uvs), guard1,
                                                      ((FStar_Syntax_Syntax.NT
                                                          (b,
                                                            FStar_Syntax_Util.exp_unit))
                                                      :: subst1))
                                                  else
                                                    (let uu____3970 =
                                                       FStar_TypeChecker_Util.new_implicit_var
                                                         "apply_lemma"
                                                         (goal.FStar_Tactics_Types.goal_ty).FStar_Syntax_Syntax.pos
                                                         goal.FStar_Tactics_Types.context
                                                         b_t
                                                        in
                                                     match uu____3970 with
                                                     | (u,uu____4000,g_u) ->
                                                         let uu____4014 =
                                                           FStar_TypeChecker_Rel.conj_guard
                                                             guard1 g_u
                                                            in
                                                         (((u, aq) :: uvs),
                                                           uu____4014,
                                                           ((FStar_Syntax_Syntax.NT
                                                               (b, u)) ::
                                                           subst1))))
                                         ([], guard, []) bs
                                        in
                                     (match uu____3782 with
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
                                          let uu____4085 =
                                            let uu____4088 =
                                              FStar_Syntax_Util.mk_squash
                                                FStar_Syntax_Syntax.U_zero
                                                post1
                                               in
                                            do_unify
                                              goal.FStar_Tactics_Types.context
                                              uu____4088
                                              goal.FStar_Tactics_Types.goal_ty
                                             in
                                          bind uu____4085
                                            (fun b  ->
                                               if Prims.op_Negation b
                                               then
                                                 let uu____4096 =
                                                   tts
                                                     goal.FStar_Tactics_Types.context
                                                     tm1
                                                    in
                                                 let uu____4097 =
                                                   let uu____4098 =
                                                     FStar_Syntax_Util.mk_squash
                                                       FStar_Syntax_Syntax.U_zero
                                                       post1
                                                      in
                                                   tts
                                                     goal.FStar_Tactics_Types.context
                                                     uu____4098
                                                    in
                                                 let uu____4099 =
                                                   tts
                                                     goal.FStar_Tactics_Types.context
                                                     goal.FStar_Tactics_Types.goal_ty
                                                    in
                                                 fail3
                                                   "Cannot instantiate lemma %s (with postcondition: %s) to match goal (%s)"
                                                   uu____4096 uu____4097
                                                   uu____4099
                                               else
                                                 (let uu____4101 =
                                                    add_implicits
                                                      implicits.FStar_TypeChecker_Env.implicits
                                                     in
                                                  bind uu____4101
                                                    (fun uu____4106  ->
                                                       let uu____4107 =
                                                         solve goal
                                                           FStar_Syntax_Util.exp_unit
                                                          in
                                                       bind uu____4107
                                                         (fun uu____4115  ->
                                                            let is_free_uvar
                                                              uv t1 =
                                                              let free_uvars
                                                                =
                                                                let uu____4126
                                                                  =
                                                                  let uu____4133
                                                                    =
                                                                    FStar_Syntax_Free.uvars
                                                                    t1  in
                                                                  FStar_Util.set_elements
                                                                    uu____4133
                                                                   in
                                                                FStar_List.map
                                                                  FStar_Pervasives_Native.fst
                                                                  uu____4126
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
                                                              let uu____4174
                                                                =
                                                                FStar_Syntax_Util.head_and_args
                                                                  t1
                                                                 in
                                                              match uu____4174
                                                              with
                                                              | (hd1,uu____4190)
                                                                  ->
                                                                  (match 
                                                                    hd1.FStar_Syntax_Syntax.n
                                                                   with
                                                                   | 
                                                                   FStar_Syntax_Syntax.Tm_uvar
                                                                    (uv,uu____4212)
                                                                    ->
                                                                    appears
                                                                    uv goals
                                                                   | 
                                                                   uu____4237
                                                                    -> false)
                                                               in
                                                            let uu____4238 =
                                                              FStar_All.pipe_right
                                                                implicits.FStar_TypeChecker_Env.implicits
                                                                (mapM
                                                                   (fun
                                                                    uu____4310
                                                                     ->
                                                                    match uu____4310
                                                                    with
                                                                    | 
                                                                    (_msg,env,_uvar,term,typ,uu____4338)
                                                                    ->
                                                                    let uu____4339
                                                                    =
                                                                    FStar_Syntax_Util.head_and_args
                                                                    term  in
                                                                    (match uu____4339
                                                                    with
                                                                    | 
                                                                    (hd1,uu____4365)
                                                                    ->
                                                                    let uu____4386
                                                                    =
                                                                    let uu____4387
                                                                    =
                                                                    FStar_Syntax_Subst.compress
                                                                    hd1  in
                                                                    uu____4387.FStar_Syntax_Syntax.n
                                                                     in
                                                                    (match uu____4386
                                                                    with
                                                                    | 
                                                                    FStar_Syntax_Syntax.Tm_uvar
                                                                    uu____4400
                                                                    ->
                                                                    let uu____4417
                                                                    =
                                                                    let uu____4426
                                                                    =
                                                                    let uu____4429
                                                                    =
                                                                    let uu___98_4430
                                                                    = goal
                                                                     in
                                                                    let uu____4431
                                                                    =
                                                                    bnorm
                                                                    goal.FStar_Tactics_Types.context
                                                                    term  in
                                                                    let uu____4432
                                                                    =
                                                                    bnorm
                                                                    goal.FStar_Tactics_Types.context
                                                                    typ  in
                                                                    {
                                                                    FStar_Tactics_Types.context
                                                                    =
                                                                    (uu___98_4430.FStar_Tactics_Types.context);
                                                                    FStar_Tactics_Types.witness
                                                                    =
                                                                    uu____4431;
                                                                    FStar_Tactics_Types.goal_ty
                                                                    =
                                                                    uu____4432;
                                                                    FStar_Tactics_Types.opts
                                                                    =
                                                                    (uu___98_4430.FStar_Tactics_Types.opts);
                                                                    FStar_Tactics_Types.is_guard
                                                                    =
                                                                    (uu___98_4430.FStar_Tactics_Types.is_guard)
                                                                    }  in
                                                                    [uu____4429]
                                                                     in
                                                                    (uu____4426,
                                                                    [])  in
                                                                    ret
                                                                    uu____4417
                                                                    | 
                                                                    uu____4445
                                                                    ->
                                                                    let g_typ
                                                                    =
                                                                    let uu____4447
                                                                    =
                                                                    FStar_Options.__temp_fast_implicits
                                                                    ()  in
                                                                    if
                                                                    uu____4447
                                                                    then
                                                                    FStar_TypeChecker_TcTerm.check_type_of_well_typed_term
                                                                    false env
                                                                    term typ
                                                                    else
                                                                    (let term1
                                                                    =
                                                                    bnorm env
                                                                    term  in
                                                                    let uu____4450
                                                                    =
                                                                    let uu____4457
                                                                    =
                                                                    FStar_TypeChecker_Env.set_expected_typ
                                                                    env typ
                                                                     in
                                                                    env.FStar_TypeChecker_Env.type_of
                                                                    uu____4457
                                                                    term1  in
                                                                    match uu____4450
                                                                    with
                                                                    | 
                                                                    (uu____4458,uu____4459,g_typ)
                                                                    -> g_typ)
                                                                     in
                                                                    let uu____4461
                                                                    =
                                                                    goal_from_guard
                                                                    "apply_lemma solved arg"
                                                                    goal.FStar_Tactics_Types.context
                                                                    g_typ
                                                                    goal.FStar_Tactics_Types.opts
                                                                     in
                                                                    bind
                                                                    uu____4461
                                                                    (fun
                                                                    uu___62_4477
                                                                     ->
                                                                    match uu___62_4477
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
                                                            bind uu____4238
                                                              (fun goals_  ->
                                                                 let sub_goals
                                                                   =
                                                                   let uu____4545
                                                                    =
                                                                    FStar_List.map
                                                                    FStar_Pervasives_Native.fst
                                                                    goals_
                                                                     in
                                                                   FStar_List.flatten
                                                                    uu____4545
                                                                    in
                                                                 let smt_goals
                                                                   =
                                                                   let uu____4567
                                                                    =
                                                                    FStar_List.map
                                                                    FStar_Pervasives_Native.snd
                                                                    goals_
                                                                     in
                                                                   FStar_List.flatten
                                                                    uu____4567
                                                                    in
                                                                 let rec filter'
                                                                   a f xs =
                                                                   match xs
                                                                   with
                                                                   | 
                                                                   [] -> []
                                                                   | 
                                                                   x::xs1 ->
                                                                    let uu____4622
                                                                    = f x xs1
                                                                     in
                                                                    if
                                                                    uu____4622
                                                                    then
                                                                    let uu____4625
                                                                    =
                                                                    filter'
                                                                    () f xs1
                                                                     in x ::
                                                                    uu____4625
                                                                    else
                                                                    filter'
                                                                    () f xs1
                                                                    in
                                                                 let sub_goals1
                                                                   =
                                                                   Obj.magic
                                                                    (filter'
                                                                    ()
                                                                    (fun a417
                                                                     ->
                                                                    fun a418 
                                                                    ->
                                                                    (Obj.magic
                                                                    (fun g 
                                                                    ->
                                                                    fun goals
                                                                     ->
                                                                    let uu____4639
                                                                    =
                                                                    checkone
                                                                    g.FStar_Tactics_Types.witness
                                                                    goals  in
                                                                    Prims.op_Negation
                                                                    uu____4639))
                                                                    a417 a418)
                                                                    (Obj.magic
                                                                    sub_goals))
                                                                    in
                                                                 let uu____4640
                                                                   =
                                                                   proc_guard
                                                                    "apply_lemma guard"
                                                                    goal.FStar_Tactics_Types.context
                                                                    guard
                                                                    goal.FStar_Tactics_Types.opts
                                                                    in
                                                                 bind
                                                                   uu____4640
                                                                   (fun
                                                                    uu____4645
                                                                     ->
                                                                    let uu____4646
                                                                    =
                                                                    let uu____4649
                                                                    =
                                                                    let uu____4650
                                                                    =
                                                                    let uu____4651
                                                                    =
                                                                    FStar_Syntax_Util.mk_squash
                                                                    FStar_Syntax_Syntax.U_zero
                                                                    pre1  in
                                                                    istrivial
                                                                    goal.FStar_Tactics_Types.context
                                                                    uu____4651
                                                                     in
                                                                    Prims.op_Negation
                                                                    uu____4650
                                                                     in
                                                                    if
                                                                    uu____4649
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
                                                                    uu____4646
                                                                    (fun
                                                                    uu____4657
                                                                     ->
                                                                    let uu____4658
                                                                    =
                                                                    add_smt_goals
                                                                    smt_goals
                                                                     in
                                                                    bind
                                                                    uu____4658
                                                                    (fun
                                                                    uu____4662
                                                                     ->
                                                                    add_goals
                                                                    sub_goals1))))))))))))))
         in
      focus uu____3674  in
    FStar_All.pipe_left (wrap_err "apply_lemma") uu____3671
  
let (destruct_eq' :
  FStar_Reflection_Data.typ ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun typ  ->
    let uu____4682 = FStar_Syntax_Util.destruct_typ_as_formula typ  in
    match uu____4682 with
    | FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn
        (l,uu____4692::(e1,uu____4694)::(e2,uu____4696)::[])) when
        FStar_Ident.lid_equals l FStar_Parser_Const.eq2_lid ->
        FStar_Pervasives_Native.Some (e1, e2)
    | uu____4755 -> FStar_Pervasives_Native.None
  
let (destruct_eq :
  FStar_Reflection_Data.typ ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun typ  ->
    let uu____4777 = destruct_eq' typ  in
    match uu____4777 with
    | FStar_Pervasives_Native.Some t -> FStar_Pervasives_Native.Some t
    | FStar_Pervasives_Native.None  ->
        let uu____4807 = FStar_Syntax_Util.un_squash typ  in
        (match uu____4807 with
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
        let uu____4863 = FStar_TypeChecker_Env.pop_bv e1  in
        match uu____4863 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (bv',e') ->
            if FStar_Syntax_Syntax.bv_eq bvar bv'
            then FStar_Pervasives_Native.Some (e', [])
            else
              (let uu____4911 = aux e'  in
               FStar_Util.map_opt uu____4911
                 (fun uu____4935  ->
                    match uu____4935 with | (e'',bvs) -> (e'', (bv' :: bvs))))
         in
      let uu____4956 = aux e  in
      FStar_Util.map_opt uu____4956
        (fun uu____4980  ->
           match uu____4980 with | (e',bvs) -> (e', (FStar_List.rev bvs)))
  
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
          let uu____5035 = split_env b1 g.FStar_Tactics_Types.context  in
          FStar_Util.map_opt uu____5035
            (fun uu____5059  ->
               match uu____5059 with
               | (e0,bvs) ->
                   let s1 bv =
                     let uu___99_5076 = bv  in
                     let uu____5077 =
                       FStar_Syntax_Subst.subst s bv.FStar_Syntax_Syntax.sort
                        in
                     {
                       FStar_Syntax_Syntax.ppname =
                         (uu___99_5076.FStar_Syntax_Syntax.ppname);
                       FStar_Syntax_Syntax.index =
                         (uu___99_5076.FStar_Syntax_Syntax.index);
                       FStar_Syntax_Syntax.sort = uu____5077
                     }  in
                   let bvs1 = FStar_List.map s1 bvs  in
                   let c = push_bvs e0 (b2 :: bvs1)  in
                   let w =
                     FStar_Syntax_Subst.subst s g.FStar_Tactics_Types.witness
                      in
                   let t =
                     FStar_Syntax_Subst.subst s g.FStar_Tactics_Types.goal_ty
                      in
                   let uu___100_5086 = g  in
                   {
                     FStar_Tactics_Types.context = c;
                     FStar_Tactics_Types.witness = w;
                     FStar_Tactics_Types.goal_ty = t;
                     FStar_Tactics_Types.opts =
                       (uu___100_5086.FStar_Tactics_Types.opts);
                     FStar_Tactics_Types.is_guard =
                       (uu___100_5086.FStar_Tactics_Types.is_guard)
                   })
  
let (rewrite : FStar_Syntax_Syntax.binder -> Prims.unit tac) =
  fun h  ->
    let uu____5094 = cur_goal ()  in
    bind uu____5094
      (fun goal  ->
         let uu____5102 = h  in
         match uu____5102 with
         | (bv,uu____5106) ->
             mlog
               (fun uu____5110  ->
                  let uu____5111 = FStar_Syntax_Print.bv_to_string bv  in
                  let uu____5112 =
                    tts goal.FStar_Tactics_Types.context
                      bv.FStar_Syntax_Syntax.sort
                     in
                  FStar_Util.print2 "+++Rewrite %s : %s\n" uu____5111
                    uu____5112)
               (fun uu____5115  ->
                  let uu____5116 =
                    split_env bv goal.FStar_Tactics_Types.context  in
                  match uu____5116 with
                  | FStar_Pervasives_Native.None  ->
                      fail "rewrite: binder not found in environment"
                  | FStar_Pervasives_Native.Some (e0,bvs) ->
                      let uu____5145 =
                        destruct_eq bv.FStar_Syntax_Syntax.sort  in
                      (match uu____5145 with
                       | FStar_Pervasives_Native.Some (x,e) ->
                           let uu____5160 =
                             let uu____5161 = FStar_Syntax_Subst.compress x
                                in
                             uu____5161.FStar_Syntax_Syntax.n  in
                           (match uu____5160 with
                            | FStar_Syntax_Syntax.Tm_name x1 ->
                                let s = [FStar_Syntax_Syntax.NT (x1, e)]  in
                                let s1 bv1 =
                                  let uu___101_5174 = bv1  in
                                  let uu____5175 =
                                    FStar_Syntax_Subst.subst s
                                      bv1.FStar_Syntax_Syntax.sort
                                     in
                                  {
                                    FStar_Syntax_Syntax.ppname =
                                      (uu___101_5174.FStar_Syntax_Syntax.ppname);
                                    FStar_Syntax_Syntax.index =
                                      (uu___101_5174.FStar_Syntax_Syntax.index);
                                    FStar_Syntax_Syntax.sort = uu____5175
                                  }  in
                                let bvs1 = FStar_List.map s1 bvs  in
                                let uu____5181 =
                                  let uu___102_5182 = goal  in
                                  let uu____5183 = push_bvs e0 (bv :: bvs1)
                                     in
                                  let uu____5184 =
                                    FStar_Syntax_Subst.subst s
                                      goal.FStar_Tactics_Types.witness
                                     in
                                  let uu____5185 =
                                    FStar_Syntax_Subst.subst s
                                      goal.FStar_Tactics_Types.goal_ty
                                     in
                                  {
                                    FStar_Tactics_Types.context = uu____5183;
                                    FStar_Tactics_Types.witness = uu____5184;
                                    FStar_Tactics_Types.goal_ty = uu____5185;
                                    FStar_Tactics_Types.opts =
                                      (uu___102_5182.FStar_Tactics_Types.opts);
                                    FStar_Tactics_Types.is_guard =
                                      (uu___102_5182.FStar_Tactics_Types.is_guard)
                                  }  in
                                replace_cur uu____5181
                            | uu____5186 ->
                                fail
                                  "rewrite: Not an equality hypothesis with a variable on the LHS")
                       | uu____5187 ->
                           fail "rewrite: Not an equality hypothesis")))
  
let (rename_to :
  FStar_Syntax_Syntax.binder -> Prims.string -> Prims.unit tac) =
  fun b  ->
    fun s  ->
      let uu____5204 = cur_goal ()  in
      bind uu____5204
        (fun goal  ->
           let uu____5215 = b  in
           match uu____5215 with
           | (bv,uu____5219) ->
               let bv' =
                 let uu____5221 =
                   let uu___103_5222 = bv  in
                   let uu____5223 =
                     FStar_Ident.mk_ident
                       (s,
                         ((bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange))
                      in
                   {
                     FStar_Syntax_Syntax.ppname = uu____5223;
                     FStar_Syntax_Syntax.index =
                       (uu___103_5222.FStar_Syntax_Syntax.index);
                     FStar_Syntax_Syntax.sort =
                       (uu___103_5222.FStar_Syntax_Syntax.sort)
                   }  in
                 FStar_Syntax_Syntax.freshen_bv uu____5221  in
               let s1 =
                 let uu____5227 =
                   let uu____5228 =
                     let uu____5235 = FStar_Syntax_Syntax.bv_to_name bv'  in
                     (bv, uu____5235)  in
                   FStar_Syntax_Syntax.NT uu____5228  in
                 [uu____5227]  in
               let uu____5236 = subst_goal bv bv' s1 goal  in
               (match uu____5236 with
                | FStar_Pervasives_Native.None  ->
                    fail "rename_to: binder not found in environment"
                | FStar_Pervasives_Native.Some goal1 -> replace_cur goal1))
  
let (binder_retype : FStar_Syntax_Syntax.binder -> Prims.unit tac) =
  fun b  ->
    let uu____5249 = cur_goal ()  in
    bind uu____5249
      (fun goal  ->
         let uu____5258 = b  in
         match uu____5258 with
         | (bv,uu____5262) ->
             let uu____5263 = split_env bv goal.FStar_Tactics_Types.context
                in
             (match uu____5263 with
              | FStar_Pervasives_Native.None  ->
                  fail "binder_retype: binder is not present in environment"
              | FStar_Pervasives_Native.Some (e0,bvs) ->
                  let uu____5292 = FStar_Syntax_Util.type_u ()  in
                  (match uu____5292 with
                   | (ty,u) ->
                       let uu____5301 = new_uvar "binder_retype" e0 ty  in
                       bind uu____5301
                         (fun t'  ->
                            let bv'' =
                              let uu___104_5311 = bv  in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___104_5311.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___104_5311.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = t'
                              }  in
                            let s =
                              let uu____5315 =
                                let uu____5316 =
                                  let uu____5323 =
                                    FStar_Syntax_Syntax.bv_to_name bv''  in
                                  (bv, uu____5323)  in
                                FStar_Syntax_Syntax.NT uu____5316  in
                              [uu____5315]  in
                            let bvs1 =
                              FStar_List.map
                                (fun b1  ->
                                   let uu___105_5331 = b1  in
                                   let uu____5332 =
                                     FStar_Syntax_Subst.subst s
                                       b1.FStar_Syntax_Syntax.sort
                                      in
                                   {
                                     FStar_Syntax_Syntax.ppname =
                                       (uu___105_5331.FStar_Syntax_Syntax.ppname);
                                     FStar_Syntax_Syntax.index =
                                       (uu___105_5331.FStar_Syntax_Syntax.index);
                                     FStar_Syntax_Syntax.sort = uu____5332
                                   }) bvs
                               in
                            let env' = push_bvs e0 (bv'' :: bvs1)  in
                            bind __dismiss
                              (fun uu____5338  ->
                                 let uu____5339 =
                                   let uu____5342 =
                                     let uu____5345 =
                                       let uu___106_5346 = goal  in
                                       let uu____5347 =
                                         FStar_Syntax_Subst.subst s
                                           goal.FStar_Tactics_Types.witness
                                          in
                                       let uu____5348 =
                                         FStar_Syntax_Subst.subst s
                                           goal.FStar_Tactics_Types.goal_ty
                                          in
                                       {
                                         FStar_Tactics_Types.context = env';
                                         FStar_Tactics_Types.witness =
                                           uu____5347;
                                         FStar_Tactics_Types.goal_ty =
                                           uu____5348;
                                         FStar_Tactics_Types.opts =
                                           (uu___106_5346.FStar_Tactics_Types.opts);
                                         FStar_Tactics_Types.is_guard =
                                           (uu___106_5346.FStar_Tactics_Types.is_guard)
                                       }  in
                                     [uu____5345]  in
                                   add_goals uu____5342  in
                                 bind uu____5339
                                   (fun uu____5351  ->
                                      let uu____5352 =
                                        FStar_Syntax_Util.mk_eq2
                                          (FStar_Syntax_Syntax.U_succ u) ty
                                          bv.FStar_Syntax_Syntax.sort t'
                                         in
                                      add_irrelevant_goal
                                        "binder_retype equation" e0
                                        uu____5352
                                        goal.FStar_Tactics_Types.opts))))))
  
let (norm_binder_type :
  FStar_Syntax_Embeddings.norm_step Prims.list ->
    FStar_Syntax_Syntax.binder -> Prims.unit tac)
  =
  fun s  ->
    fun b  ->
      let uu____5367 = cur_goal ()  in
      bind uu____5367
        (fun goal  ->
           let uu____5376 = b  in
           match uu____5376 with
           | (bv,uu____5380) ->
               let uu____5381 = split_env bv goal.FStar_Tactics_Types.context
                  in
               (match uu____5381 with
                | FStar_Pervasives_Native.None  ->
                    fail
                      "binder_retype: binder is not present in environment"
                | FStar_Pervasives_Native.Some (e0,bvs) ->
                    let steps =
                      let uu____5413 =
                        FStar_TypeChecker_Normalize.tr_norm_steps s  in
                      FStar_List.append
                        [FStar_TypeChecker_Normalize.Reify;
                        FStar_TypeChecker_Normalize.UnfoldTac] uu____5413
                       in
                    let sort' =
                      normalize steps e0 bv.FStar_Syntax_Syntax.sort  in
                    let bv' =
                      let uu___107_5418 = bv  in
                      {
                        FStar_Syntax_Syntax.ppname =
                          (uu___107_5418.FStar_Syntax_Syntax.ppname);
                        FStar_Syntax_Syntax.index =
                          (uu___107_5418.FStar_Syntax_Syntax.index);
                        FStar_Syntax_Syntax.sort = sort'
                      }  in
                    let env' = push_bvs e0 (bv' :: bvs)  in
                    replace_cur
                      (let uu___108_5422 = goal  in
                       {
                         FStar_Tactics_Types.context = env';
                         FStar_Tactics_Types.witness =
                           (uu___108_5422.FStar_Tactics_Types.witness);
                         FStar_Tactics_Types.goal_ty =
                           (uu___108_5422.FStar_Tactics_Types.goal_ty);
                         FStar_Tactics_Types.opts =
                           (uu___108_5422.FStar_Tactics_Types.opts);
                         FStar_Tactics_Types.is_guard =
                           (uu___108_5422.FStar_Tactics_Types.is_guard)
                       })))
  
let (revert : Prims.unit -> Prims.unit tac) =
  fun uu____5427  ->
    let uu____5430 = cur_goal ()  in
    bind uu____5430
      (fun goal  ->
         let uu____5436 =
           FStar_TypeChecker_Env.pop_bv goal.FStar_Tactics_Types.context  in
         match uu____5436 with
         | FStar_Pervasives_Native.None  ->
             fail "Cannot revert; empty context"
         | FStar_Pervasives_Native.Some (x,env') ->
             let typ' =
               let uu____5458 =
                 FStar_Syntax_Syntax.mk_Total
                   goal.FStar_Tactics_Types.goal_ty
                  in
               FStar_Syntax_Util.arrow [(x, FStar_Pervasives_Native.None)]
                 uu____5458
                in
             let w' =
               FStar_Syntax_Util.abs [(x, FStar_Pervasives_Native.None)]
                 goal.FStar_Tactics_Types.witness
                 FStar_Pervasives_Native.None
                in
             replace_cur
               (let uu___109_5492 = goal  in
                {
                  FStar_Tactics_Types.context = env';
                  FStar_Tactics_Types.witness = w';
                  FStar_Tactics_Types.goal_ty = typ';
                  FStar_Tactics_Types.opts =
                    (uu___109_5492.FStar_Tactics_Types.opts);
                  FStar_Tactics_Types.is_guard =
                    (uu___109_5492.FStar_Tactics_Types.is_guard)
                }))
  
let (free_in :
  FStar_Syntax_Syntax.bv -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun bv  ->
    fun t  ->
      let uu____5499 = FStar_Syntax_Free.names t  in
      FStar_Util.set_mem bv uu____5499
  
let rec (clear : FStar_Syntax_Syntax.binder -> Prims.unit tac) =
  fun b  ->
    let bv = FStar_Pervasives_Native.fst b  in
    let uu____5510 = cur_goal ()  in
    bind uu____5510
      (fun goal  ->
         mlog
           (fun uu____5518  ->
              let uu____5519 = FStar_Syntax_Print.binder_to_string b  in
              let uu____5520 =
                let uu____5521 =
                  let uu____5522 =
                    FStar_TypeChecker_Env.all_binders
                      goal.FStar_Tactics_Types.context
                     in
                  FStar_All.pipe_right uu____5522 FStar_List.length  in
                FStar_All.pipe_right uu____5521 FStar_Util.string_of_int  in
              FStar_Util.print2 "Clear of (%s), env has %s binders\n"
                uu____5519 uu____5520)
           (fun uu____5533  ->
              let uu____5534 = split_env bv goal.FStar_Tactics_Types.context
                 in
              match uu____5534 with
              | FStar_Pervasives_Native.None  ->
                  fail "Cannot clear; binder not in environment"
              | FStar_Pervasives_Native.Some (e',bvs) ->
                  let rec check1 bvs1 =
                    match bvs1 with
                    | [] -> ret ()
                    | bv'::bvs2 ->
                        let uu____5579 =
                          free_in bv bv'.FStar_Syntax_Syntax.sort  in
                        if uu____5579
                        then
                          let uu____5582 =
                            let uu____5583 =
                              FStar_Syntax_Print.bv_to_string bv'  in
                            FStar_Util.format1
                              "Cannot clear; binder present in the type of %s"
                              uu____5583
                             in
                          fail uu____5582
                        else check1 bvs2
                     in
                  let uu____5585 =
                    free_in bv goal.FStar_Tactics_Types.goal_ty  in
                  if uu____5585
                  then fail "Cannot clear; binder present in goal"
                  else
                    (let uu____5589 = check1 bvs  in
                     bind uu____5589
                       (fun uu____5595  ->
                          let env' = push_bvs e' bvs  in
                          let uu____5597 =
                            new_uvar "clear.witness" env'
                              goal.FStar_Tactics_Types.goal_ty
                             in
                          bind uu____5597
                            (fun ut  ->
                               let uu____5603 =
                                 do_unify goal.FStar_Tactics_Types.context
                                   goal.FStar_Tactics_Types.witness ut
                                  in
                               bind uu____5603
                                 (fun b1  ->
                                    if b1
                                    then
                                      replace_cur
                                        (let uu___110_5612 = goal  in
                                         {
                                           FStar_Tactics_Types.context = env';
                                           FStar_Tactics_Types.witness = ut;
                                           FStar_Tactics_Types.goal_ty =
                                             (uu___110_5612.FStar_Tactics_Types.goal_ty);
                                           FStar_Tactics_Types.opts =
                                             (uu___110_5612.FStar_Tactics_Types.opts);
                                           FStar_Tactics_Types.is_guard =
                                             (uu___110_5612.FStar_Tactics_Types.is_guard)
                                         })
                                    else
                                      fail
                                        "Cannot clear; binder appears in witness"))))))
  
let (clear_top : Prims.unit -> Prims.unit tac) =
  fun uu____5618  ->
    let uu____5621 = cur_goal ()  in
    bind uu____5621
      (fun goal  ->
         let uu____5627 =
           FStar_TypeChecker_Env.pop_bv goal.FStar_Tactics_Types.context  in
         match uu____5627 with
         | FStar_Pervasives_Native.None  ->
             fail "Cannot clear; empty context"
         | FStar_Pervasives_Native.Some (x,uu____5641) ->
             let uu____5646 = FStar_Syntax_Syntax.mk_binder x  in
             clear uu____5646)
  
let (prune : Prims.string -> Prims.unit tac) =
  fun s  ->
    let uu____5654 = cur_goal ()  in
    bind uu____5654
      (fun g  ->
         let ctx = g.FStar_Tactics_Types.context  in
         let ctx' =
           let uu____5664 = FStar_Ident.path_of_text s  in
           FStar_TypeChecker_Env.rem_proof_ns ctx uu____5664  in
         let g' =
           let uu___111_5666 = g  in
           {
             FStar_Tactics_Types.context = ctx';
             FStar_Tactics_Types.witness =
               (uu___111_5666.FStar_Tactics_Types.witness);
             FStar_Tactics_Types.goal_ty =
               (uu___111_5666.FStar_Tactics_Types.goal_ty);
             FStar_Tactics_Types.opts =
               (uu___111_5666.FStar_Tactics_Types.opts);
             FStar_Tactics_Types.is_guard =
               (uu___111_5666.FStar_Tactics_Types.is_guard)
           }  in
         bind __dismiss (fun uu____5668  -> add_goals [g']))
  
let (addns : Prims.string -> Prims.unit tac) =
  fun s  ->
    let uu____5676 = cur_goal ()  in
    bind uu____5676
      (fun g  ->
         let ctx = g.FStar_Tactics_Types.context  in
         let ctx' =
           let uu____5686 = FStar_Ident.path_of_text s  in
           FStar_TypeChecker_Env.add_proof_ns ctx uu____5686  in
         let g' =
           let uu___112_5688 = g  in
           {
             FStar_Tactics_Types.context = ctx';
             FStar_Tactics_Types.witness =
               (uu___112_5688.FStar_Tactics_Types.witness);
             FStar_Tactics_Types.goal_ty =
               (uu___112_5688.FStar_Tactics_Types.goal_ty);
             FStar_Tactics_Types.opts =
               (uu___112_5688.FStar_Tactics_Types.opts);
             FStar_Tactics_Types.is_guard =
               (uu___112_5688.FStar_Tactics_Types.is_guard)
           }  in
         bind __dismiss (fun uu____5690  -> add_goals [g']))
  
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
            let uu____5722 = FStar_Syntax_Subst.compress t  in
            uu____5722.FStar_Syntax_Syntax.n  in
          let uu____5725 =
            if d = FStar_Tactics_Types.TopDown
            then
              f env
                (let uu___116_5731 = t  in
                 {
                   FStar_Syntax_Syntax.n = tn;
                   FStar_Syntax_Syntax.pos =
                     (uu___116_5731.FStar_Syntax_Syntax.pos);
                   FStar_Syntax_Syntax.vars =
                     (uu___116_5731.FStar_Syntax_Syntax.vars)
                 })
            else ret t  in
          bind uu____5725
            (fun t1  ->
               let ff = tac_fold_env d f env  in
               let tn1 =
                 let uu____5745 =
                   let uu____5746 = FStar_Syntax_Subst.compress t1  in
                   uu____5746.FStar_Syntax_Syntax.n  in
                 match uu____5745 with
                 | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
                     let uu____5773 = ff hd1  in
                     bind uu____5773
                       (fun hd2  ->
                          let fa uu____5793 =
                            match uu____5793 with
                            | (a,q) ->
                                let uu____5806 = ff a  in
                                bind uu____5806 (fun a1  -> ret (a1, q))
                             in
                          let uu____5819 = mapM fa args  in
                          bind uu____5819
                            (fun args1  ->
                               ret (FStar_Syntax_Syntax.Tm_app (hd2, args1))))
                 | FStar_Syntax_Syntax.Tm_abs (bs,t2,k) ->
                     let uu____5879 = FStar_Syntax_Subst.open_term bs t2  in
                     (match uu____5879 with
                      | (bs1,t') ->
                          let uu____5888 =
                            let uu____5891 =
                              FStar_TypeChecker_Env.push_binders env bs1  in
                            tac_fold_env d f uu____5891 t'  in
                          bind uu____5888
                            (fun t''  ->
                               let uu____5895 =
                                 let uu____5896 =
                                   let uu____5913 =
                                     FStar_Syntax_Subst.close_binders bs1  in
                                   let uu____5914 =
                                     FStar_Syntax_Subst.close bs1 t''  in
                                   (uu____5913, uu____5914, k)  in
                                 FStar_Syntax_Syntax.Tm_abs uu____5896  in
                               ret uu____5895))
                 | FStar_Syntax_Syntax.Tm_arrow (bs,k) -> ret tn
                 | FStar_Syntax_Syntax.Tm_match (hd1,brs) ->
                     let uu____5973 = ff hd1  in
                     bind uu____5973
                       (fun hd2  ->
                          let ffb br =
                            let uu____5986 =
                              FStar_Syntax_Subst.open_branch br  in
                            match uu____5986 with
                            | (pat,w,e) ->
                                let bvs = FStar_Syntax_Syntax.pat_bvs pat  in
                                let ff1 =
                                  let uu____6016 =
                                    FStar_TypeChecker_Env.push_bvs env bvs
                                     in
                                  tac_fold_env d f uu____6016  in
                                let uu____6017 = ff1 e  in
                                bind uu____6017
                                  (fun e1  ->
                                     let br1 =
                                       FStar_Syntax_Subst.close_branch
                                         (pat, w, e1)
                                        in
                                     ret br1)
                             in
                          let uu____6030 = mapM ffb brs  in
                          bind uu____6030
                            (fun brs1  ->
                               ret (FStar_Syntax_Syntax.Tm_match (hd2, brs1))))
                 | FStar_Syntax_Syntax.Tm_let
                     ((false
                       ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inl bv;
                          FStar_Syntax_Syntax.lbunivs = uu____6044;
                          FStar_Syntax_Syntax.lbtyp = uu____6045;
                          FStar_Syntax_Syntax.lbeff = uu____6046;
                          FStar_Syntax_Syntax.lbdef = def;
                          FStar_Syntax_Syntax.lbattrs = uu____6048;
                          FStar_Syntax_Syntax.lbpos = uu____6049;_}::[]),e)
                     ->
                     let lb =
                       let uu____6074 =
                         let uu____6075 = FStar_Syntax_Subst.compress t1  in
                         uu____6075.FStar_Syntax_Syntax.n  in
                       match uu____6074 with
                       | FStar_Syntax_Syntax.Tm_let
                           ((false ,lb::[]),uu____6079) -> lb
                       | uu____6092 -> failwith "impossible"  in
                     let fflb lb1 =
                       let uu____6099 = ff lb1.FStar_Syntax_Syntax.lbdef  in
                       bind uu____6099
                         (fun def1  ->
                            ret
                              (let uu___113_6105 = lb1  in
                               {
                                 FStar_Syntax_Syntax.lbname =
                                   (uu___113_6105.FStar_Syntax_Syntax.lbname);
                                 FStar_Syntax_Syntax.lbunivs =
                                   (uu___113_6105.FStar_Syntax_Syntax.lbunivs);
                                 FStar_Syntax_Syntax.lbtyp =
                                   (uu___113_6105.FStar_Syntax_Syntax.lbtyp);
                                 FStar_Syntax_Syntax.lbeff =
                                   (uu___113_6105.FStar_Syntax_Syntax.lbeff);
                                 FStar_Syntax_Syntax.lbdef = def1;
                                 FStar_Syntax_Syntax.lbattrs =
                                   (uu___113_6105.FStar_Syntax_Syntax.lbattrs);
                                 FStar_Syntax_Syntax.lbpos =
                                   (uu___113_6105.FStar_Syntax_Syntax.lbpos)
                               }))
                        in
                     let uu____6106 = fflb lb  in
                     bind uu____6106
                       (fun lb1  ->
                          let uu____6116 =
                            let uu____6121 =
                              let uu____6122 =
                                FStar_Syntax_Syntax.mk_binder bv  in
                              [uu____6122]  in
                            FStar_Syntax_Subst.open_term uu____6121 e  in
                          match uu____6116 with
                          | (bs,e1) ->
                              let ff1 =
                                let uu____6132 =
                                  FStar_TypeChecker_Env.push_binders env bs
                                   in
                                tac_fold_env d f uu____6132  in
                              let uu____6133 = ff1 e1  in
                              bind uu____6133
                                (fun e2  ->
                                   let e3 = FStar_Syntax_Subst.close bs e2
                                      in
                                   ret
                                     (FStar_Syntax_Syntax.Tm_let
                                        ((false, [lb1]), e3))))
                 | FStar_Syntax_Syntax.Tm_let ((true ,lbs),e) ->
                     let fflb lb =
                       let uu____6170 = ff lb.FStar_Syntax_Syntax.lbdef  in
                       bind uu____6170
                         (fun def  ->
                            ret
                              (let uu___114_6176 = lb  in
                               {
                                 FStar_Syntax_Syntax.lbname =
                                   (uu___114_6176.FStar_Syntax_Syntax.lbname);
                                 FStar_Syntax_Syntax.lbunivs =
                                   (uu___114_6176.FStar_Syntax_Syntax.lbunivs);
                                 FStar_Syntax_Syntax.lbtyp =
                                   (uu___114_6176.FStar_Syntax_Syntax.lbtyp);
                                 FStar_Syntax_Syntax.lbeff =
                                   (uu___114_6176.FStar_Syntax_Syntax.lbeff);
                                 FStar_Syntax_Syntax.lbdef = def;
                                 FStar_Syntax_Syntax.lbattrs =
                                   (uu___114_6176.FStar_Syntax_Syntax.lbattrs);
                                 FStar_Syntax_Syntax.lbpos =
                                   (uu___114_6176.FStar_Syntax_Syntax.lbpos)
                               }))
                        in
                     let uu____6177 = FStar_Syntax_Subst.open_let_rec lbs e
                        in
                     (match uu____6177 with
                      | (lbs1,e1) ->
                          let uu____6192 = mapM fflb lbs1  in
                          bind uu____6192
                            (fun lbs2  ->
                               let uu____6204 = ff e1  in
                               bind uu____6204
                                 (fun e2  ->
                                    let uu____6212 =
                                      FStar_Syntax_Subst.close_let_rec lbs2
                                        e2
                                       in
                                    match uu____6212 with
                                    | (lbs3,e3) ->
                                        ret
                                          (FStar_Syntax_Syntax.Tm_let
                                             ((true, lbs3), e3)))))
                 | FStar_Syntax_Syntax.Tm_ascribed (t2,asc,eff) ->
                     let uu____6278 = ff t2  in
                     bind uu____6278
                       (fun t3  ->
                          ret
                            (FStar_Syntax_Syntax.Tm_ascribed (t3, asc, eff)))
                 | FStar_Syntax_Syntax.Tm_meta (t2,m) ->
                     let uu____6307 = ff t2  in
                     bind uu____6307
                       (fun t3  -> ret (FStar_Syntax_Syntax.Tm_meta (t3, m)))
                 | uu____6312 -> ret tn  in
               bind tn1
                 (fun tn2  ->
                    let t' =
                      let uu___115_6319 = t1  in
                      {
                        FStar_Syntax_Syntax.n = tn2;
                        FStar_Syntax_Syntax.pos =
                          (uu___115_6319.FStar_Syntax_Syntax.pos);
                        FStar_Syntax_Syntax.vars =
                          (uu___115_6319.FStar_Syntax_Syntax.vars)
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
            let uu____6348 = FStar_TypeChecker_TcTerm.tc_term env t  in
            match uu____6348 with
            | (t1,lcomp,g) ->
                let uu____6360 =
                  (let uu____6363 =
                     FStar_Syntax_Util.is_pure_or_ghost_lcomp lcomp  in
                   Prims.op_Negation uu____6363) ||
                    (let uu____6365 = FStar_TypeChecker_Rel.is_trivial g  in
                     Prims.op_Negation uu____6365)
                   in
                if uu____6360
                then ret t1
                else
                  (let rewrite_eq =
                     let typ = lcomp.FStar_Syntax_Syntax.res_typ  in
                     let uu____6375 = new_uvar "pointwise_rec" env typ  in
                     bind uu____6375
                       (fun ut  ->
                          log ps
                            (fun uu____6386  ->
                               let uu____6387 =
                                 FStar_Syntax_Print.term_to_string t1  in
                               let uu____6388 =
                                 FStar_Syntax_Print.term_to_string ut  in
                               FStar_Util.print2
                                 "Pointwise_rec: making equality\n\t%s ==\n\t%s\n"
                                 uu____6387 uu____6388);
                          (let uu____6389 =
                             let uu____6392 =
                               let uu____6393 =
                                 FStar_TypeChecker_TcTerm.universe_of env typ
                                  in
                               FStar_Syntax_Util.mk_eq2 uu____6393 typ t1 ut
                                in
                             add_irrelevant_goal "pointwise_rec equation" env
                               uu____6392 opts
                              in
                           bind uu____6389
                             (fun uu____6396  ->
                                let uu____6397 =
                                  bind tau
                                    (fun uu____6403  ->
                                       let ut1 =
                                         FStar_TypeChecker_Normalize.reduce_uvar_solutions
                                           env ut
                                          in
                                       log ps
                                         (fun uu____6409  ->
                                            let uu____6410 =
                                              FStar_Syntax_Print.term_to_string
                                                t1
                                               in
                                            let uu____6411 =
                                              FStar_Syntax_Print.term_to_string
                                                ut1
                                               in
                                            FStar_Util.print2
                                              "Pointwise_rec: succeeded rewriting\n\t%s to\n\t%s\n"
                                              uu____6410 uu____6411);
                                       ret ut1)
                                   in
                                focus uu____6397)))
                      in
                   let uu____6412 = trytac' rewrite_eq  in
                   bind uu____6412
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
          let uu____6560 = FStar_Syntax_Subst.compress t  in
          maybe_continue ctrl uu____6560
            (fun t1  ->
               let uu____6564 =
                 f env
                   (let uu___119_6573 = t1  in
                    {
                      FStar_Syntax_Syntax.n = (t1.FStar_Syntax_Syntax.n);
                      FStar_Syntax_Syntax.pos =
                        (uu___119_6573.FStar_Syntax_Syntax.pos);
                      FStar_Syntax_Syntax.vars =
                        (uu___119_6573.FStar_Syntax_Syntax.vars)
                    })
                  in
               bind uu____6564
                 (fun uu____6585  ->
                    match uu____6585 with
                    | (t2,ctrl1) ->
                        maybe_continue ctrl1 t2
                          (fun t3  ->
                             let uu____6604 =
                               let uu____6605 =
                                 FStar_Syntax_Subst.compress t3  in
                               uu____6605.FStar_Syntax_Syntax.n  in
                             match uu____6604 with
                             | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
                                 let uu____6638 =
                                   ctrl_tac_fold f env ctrl1 hd1  in
                                 bind uu____6638
                                   (fun uu____6663  ->
                                      match uu____6663 with
                                      | (hd2,ctrl2) ->
                                          let ctrl3 = keep_going ctrl2  in
                                          let uu____6679 =
                                            ctrl_tac_fold_args f env ctrl3
                                              args
                                             in
                                          bind uu____6679
                                            (fun uu____6706  ->
                                               match uu____6706 with
                                               | (args1,ctrl4) ->
                                                   ret
                                                     ((let uu___117_6736 = t3
                                                          in
                                                       {
                                                         FStar_Syntax_Syntax.n
                                                           =
                                                           (FStar_Syntax_Syntax.Tm_app
                                                              (hd2, args1));
                                                         FStar_Syntax_Syntax.pos
                                                           =
                                                           (uu___117_6736.FStar_Syntax_Syntax.pos);
                                                         FStar_Syntax_Syntax.vars
                                                           =
                                                           (uu___117_6736.FStar_Syntax_Syntax.vars)
                                                       }), ctrl4)))
                             | FStar_Syntax_Syntax.Tm_abs (bs,t4,k) ->
                                 let uu____6762 =
                                   FStar_Syntax_Subst.open_term bs t4  in
                                 (match uu____6762 with
                                  | (bs1,t') ->
                                      let uu____6777 =
                                        let uu____6784 =
                                          FStar_TypeChecker_Env.push_binders
                                            env bs1
                                           in
                                        ctrl_tac_fold f uu____6784 ctrl1 t'
                                         in
                                      bind uu____6777
                                        (fun uu____6802  ->
                                           match uu____6802 with
                                           | (t'',ctrl2) ->
                                               let uu____6817 =
                                                 let uu____6824 =
                                                   let uu___118_6827 = t4  in
                                                   let uu____6830 =
                                                     let uu____6831 =
                                                       let uu____6848 =
                                                         FStar_Syntax_Subst.close_binders
                                                           bs1
                                                          in
                                                       let uu____6849 =
                                                         FStar_Syntax_Subst.close
                                                           bs1 t''
                                                          in
                                                       (uu____6848,
                                                         uu____6849, k)
                                                        in
                                                     FStar_Syntax_Syntax.Tm_abs
                                                       uu____6831
                                                      in
                                                   {
                                                     FStar_Syntax_Syntax.n =
                                                       uu____6830;
                                                     FStar_Syntax_Syntax.pos
                                                       =
                                                       (uu___118_6827.FStar_Syntax_Syntax.pos);
                                                     FStar_Syntax_Syntax.vars
                                                       =
                                                       (uu___118_6827.FStar_Syntax_Syntax.vars)
                                                   }  in
                                                 (uu____6824, ctrl2)  in
                                               ret uu____6817))
                             | FStar_Syntax_Syntax.Tm_arrow (bs,k) ->
                                 ret (t3, ctrl1)
                             | uu____6882 -> ret (t3, ctrl1))))

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
              let uu____6933 = ctrl_tac_fold f env ctrl t  in
              bind uu____6933
                (fun uu____6961  ->
                   match uu____6961 with
                   | (t1,ctrl1) ->
                       let uu____6980 = ctrl_tac_fold_args f env ctrl1 ts1
                          in
                       bind uu____6980
                         (fun uu____7011  ->
                            match uu____7011 with
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
              let uu____7095 =
                let uu____7102 =
                  add_irrelevant_goal "dummy" env FStar_Syntax_Util.t_true
                    opts
                   in
                bind uu____7102
                  (fun uu____7111  ->
                     let uu____7112 = ctrl t1  in
                     bind uu____7112
                       (fun res  ->
                          let uu____7135 = trivial ()  in
                          bind uu____7135 (fun uu____7143  -> ret res)))
                 in
              bind uu____7095
                (fun uu____7159  ->
                   match uu____7159 with
                   | (should_rewrite,ctrl1) ->
                       if Prims.op_Negation should_rewrite
                       then ret (t1, ctrl1)
                       else
                         (let uu____7183 =
                            FStar_TypeChecker_TcTerm.tc_term env t1  in
                          match uu____7183 with
                          | (t2,lcomp,g) ->
                              let uu____7199 =
                                (let uu____7202 =
                                   FStar_Syntax_Util.is_pure_or_ghost_lcomp
                                     lcomp
                                    in
                                 Prims.op_Negation uu____7202) ||
                                  (let uu____7204 =
                                     FStar_TypeChecker_Rel.is_trivial g  in
                                   Prims.op_Negation uu____7204)
                                 in
                              if uu____7199
                              then ret (t2, globalStop)
                              else
                                (let typ = lcomp.FStar_Syntax_Syntax.res_typ
                                    in
                                 let uu____7219 =
                                   new_uvar "pointwise_rec" env typ  in
                                 bind uu____7219
                                   (fun ut  ->
                                      log ps
                                        (fun uu____7234  ->
                                           let uu____7235 =
                                             FStar_Syntax_Print.term_to_string
                                               t2
                                              in
                                           let uu____7236 =
                                             FStar_Syntax_Print.term_to_string
                                               ut
                                              in
                                           FStar_Util.print2
                                             "Pointwise_rec: making equality\n\t%s ==\n\t%s\n"
                                             uu____7235 uu____7236);
                                      (let uu____7237 =
                                         let uu____7240 =
                                           let uu____7241 =
                                             FStar_TypeChecker_TcTerm.universe_of
                                               env typ
                                              in
                                           FStar_Syntax_Util.mk_eq2
                                             uu____7241 typ t2 ut
                                            in
                                         add_irrelevant_goal
                                           "rewrite_rec equation" env
                                           uu____7240 opts
                                          in
                                       bind uu____7237
                                         (fun uu____7248  ->
                                            let uu____7249 =
                                              bind rewriter
                                                (fun uu____7263  ->
                                                   let ut1 =
                                                     FStar_TypeChecker_Normalize.reduce_uvar_solutions
                                                       env ut
                                                      in
                                                   log ps
                                                     (fun uu____7269  ->
                                                        let uu____7270 =
                                                          FStar_Syntax_Print.term_to_string
                                                            t2
                                                           in
                                                        let uu____7271 =
                                                          FStar_Syntax_Print.term_to_string
                                                            ut1
                                                           in
                                                        FStar_Util.print2
                                                          "rewrite_rec: succeeded rewriting\n\t%s to\n\t%s\n"
                                                          uu____7270
                                                          uu____7271);
                                                   ret (ut1, ctrl1))
                                               in
                                            focus uu____7249))))))
  
let (topdown_rewrite :
  (FStar_Syntax_Syntax.term ->
     (Prims.bool,FStar_BigInt.t) FStar_Pervasives_Native.tuple2 tac)
    -> Prims.unit tac -> Prims.unit tac)
  =
  fun ctrl  ->
    fun rewriter  ->
      bind get
        (fun ps  ->
           let uu____7315 =
             match ps.FStar_Tactics_Types.goals with
             | g::gs -> (g, gs)
             | [] -> failwith "Pointwise: no goals"  in
           match uu____7315 with
           | (g,gs) ->
               let gt1 = g.FStar_Tactics_Types.goal_ty  in
               (log ps
                  (fun uu____7352  ->
                     let uu____7353 = FStar_Syntax_Print.term_to_string gt1
                        in
                     FStar_Util.print1 "Topdown_rewrite starting with %s\n"
                       uu____7353);
                bind dismiss_all
                  (fun uu____7356  ->
                     let uu____7357 =
                       ctrl_tac_fold
                         (rewrite_rec ps ctrl rewriter
                            g.FStar_Tactics_Types.opts)
                         g.FStar_Tactics_Types.context keepGoing gt1
                        in
                     bind uu____7357
                       (fun uu____7375  ->
                          match uu____7375 with
                          | (gt',uu____7383) ->
                              (log ps
                                 (fun uu____7387  ->
                                    let uu____7388 =
                                      FStar_Syntax_Print.term_to_string gt'
                                       in
                                    FStar_Util.print1
                                      "Topdown_rewrite seems to have succeded with %s\n"
                                      uu____7388);
                               (let uu____7389 = push_goals gs  in
                                bind uu____7389
                                  (fun uu____7393  ->
                                     add_goals
                                       [(let uu___120_7395 = g  in
                                         {
                                           FStar_Tactics_Types.context =
                                             (uu___120_7395.FStar_Tactics_Types.context);
                                           FStar_Tactics_Types.witness =
                                             (uu___120_7395.FStar_Tactics_Types.witness);
                                           FStar_Tactics_Types.goal_ty = gt';
                                           FStar_Tactics_Types.opts =
                                             (uu___120_7395.FStar_Tactics_Types.opts);
                                           FStar_Tactics_Types.is_guard =
                                             (uu___120_7395.FStar_Tactics_Types.is_guard)
                                         })])))))))
  
let (pointwise :
  FStar_Tactics_Types.direction -> Prims.unit tac -> Prims.unit tac) =
  fun d  ->
    fun tau  ->
      bind get
        (fun ps  ->
           let uu____7417 =
             match ps.FStar_Tactics_Types.goals with
             | g::gs -> (g, gs)
             | [] -> failwith "Pointwise: no goals"  in
           match uu____7417 with
           | (g,gs) ->
               let gt1 = g.FStar_Tactics_Types.goal_ty  in
               (log ps
                  (fun uu____7454  ->
                     let uu____7455 = FStar_Syntax_Print.term_to_string gt1
                        in
                     FStar_Util.print1 "Pointwise starting with %s\n"
                       uu____7455);
                bind dismiss_all
                  (fun uu____7458  ->
                     let uu____7459 =
                       tac_fold_env d
                         (pointwise_rec ps tau g.FStar_Tactics_Types.opts)
                         g.FStar_Tactics_Types.context gt1
                        in
                     bind uu____7459
                       (fun gt'  ->
                          log ps
                            (fun uu____7469  ->
                               let uu____7470 =
                                 FStar_Syntax_Print.term_to_string gt'  in
                               FStar_Util.print1
                                 "Pointwise seems to have succeded with %s\n"
                                 uu____7470);
                          (let uu____7471 = push_goals gs  in
                           bind uu____7471
                             (fun uu____7475  ->
                                add_goals
                                  [(let uu___121_7477 = g  in
                                    {
                                      FStar_Tactics_Types.context =
                                        (uu___121_7477.FStar_Tactics_Types.context);
                                      FStar_Tactics_Types.witness =
                                        (uu___121_7477.FStar_Tactics_Types.witness);
                                      FStar_Tactics_Types.goal_ty = gt';
                                      FStar_Tactics_Types.opts =
                                        (uu___121_7477.FStar_Tactics_Types.opts);
                                      FStar_Tactics_Types.is_guard =
                                        (uu___121_7477.FStar_Tactics_Types.is_guard)
                                    })]))))))
  
let (trefl : Prims.unit -> Prims.unit tac) =
  fun uu____7482  ->
    let uu____7485 = cur_goal ()  in
    bind uu____7485
      (fun g  ->
         let uu____7503 =
           FStar_Syntax_Util.un_squash g.FStar_Tactics_Types.goal_ty  in
         match uu____7503 with
         | FStar_Pervasives_Native.Some t ->
             let uu____7515 = FStar_Syntax_Util.head_and_args' t  in
             (match uu____7515 with
              | (hd1,args) ->
                  let uu____7548 =
                    let uu____7561 =
                      let uu____7562 = FStar_Syntax_Util.un_uinst hd1  in
                      uu____7562.FStar_Syntax_Syntax.n  in
                    (uu____7561, args)  in
                  (match uu____7548 with
                   | (FStar_Syntax_Syntax.Tm_fvar
                      fv,uu____7576::(l,uu____7578)::(r,uu____7580)::[]) when
                       FStar_Syntax_Syntax.fv_eq_lid fv
                         FStar_Parser_Const.eq2_lid
                       ->
                       let uu____7627 =
                         do_unify g.FStar_Tactics_Types.context l r  in
                       bind uu____7627
                         (fun b  ->
                            if Prims.op_Negation b
                            then
                              let uu____7636 =
                                tts g.FStar_Tactics_Types.context l  in
                              let uu____7637 =
                                tts g.FStar_Tactics_Types.context r  in
                              fail2
                                "trefl: not a trivial equality (%s vs %s)"
                                uu____7636 uu____7637
                            else solve g FStar_Syntax_Util.exp_unit)
                   | (hd2,uu____7640) ->
                       let uu____7657 = tts g.FStar_Tactics_Types.context t
                          in
                       fail1 "trefl: not an equality (%s)" uu____7657))
         | FStar_Pervasives_Native.None  -> fail "not an irrelevant goal")
  
let (dup : Prims.unit -> Prims.unit tac) =
  fun uu____7664  ->
    let uu____7667 = cur_goal ()  in
    bind uu____7667
      (fun g  ->
         let uu____7673 =
           new_uvar "dup" g.FStar_Tactics_Types.context
             g.FStar_Tactics_Types.goal_ty
            in
         bind uu____7673
           (fun u  ->
              let g' =
                let uu___122_7680 = g  in
                {
                  FStar_Tactics_Types.context =
                    (uu___122_7680.FStar_Tactics_Types.context);
                  FStar_Tactics_Types.witness = u;
                  FStar_Tactics_Types.goal_ty =
                    (uu___122_7680.FStar_Tactics_Types.goal_ty);
                  FStar_Tactics_Types.opts =
                    (uu___122_7680.FStar_Tactics_Types.opts);
                  FStar_Tactics_Types.is_guard =
                    (uu___122_7680.FStar_Tactics_Types.is_guard)
                }  in
              bind __dismiss
                (fun uu____7683  ->
                   let uu____7684 =
                     let uu____7687 =
                       let uu____7688 =
                         FStar_TypeChecker_TcTerm.universe_of
                           g.FStar_Tactics_Types.context
                           g.FStar_Tactics_Types.goal_ty
                          in
                       FStar_Syntax_Util.mk_eq2 uu____7688
                         g.FStar_Tactics_Types.goal_ty u
                         g.FStar_Tactics_Types.witness
                        in
                     add_irrelevant_goal "dup equation"
                       g.FStar_Tactics_Types.context uu____7687
                       g.FStar_Tactics_Types.opts
                      in
                   bind uu____7684
                     (fun uu____7691  ->
                        let uu____7692 = add_goals [g']  in
                        bind uu____7692 (fun uu____7696  -> ret ())))))
  
let (flip : Prims.unit -> Prims.unit tac) =
  fun uu____7701  ->
    bind get
      (fun ps  ->
         match ps.FStar_Tactics_Types.goals with
         | g1::g2::gs ->
             set
               (let uu___123_7718 = ps  in
                {
                  FStar_Tactics_Types.main_context =
                    (uu___123_7718.FStar_Tactics_Types.main_context);
                  FStar_Tactics_Types.main_goal =
                    (uu___123_7718.FStar_Tactics_Types.main_goal);
                  FStar_Tactics_Types.all_implicits =
                    (uu___123_7718.FStar_Tactics_Types.all_implicits);
                  FStar_Tactics_Types.goals = (g2 :: g1 :: gs);
                  FStar_Tactics_Types.smt_goals =
                    (uu___123_7718.FStar_Tactics_Types.smt_goals);
                  FStar_Tactics_Types.depth =
                    (uu___123_7718.FStar_Tactics_Types.depth);
                  FStar_Tactics_Types.__dump =
                    (uu___123_7718.FStar_Tactics_Types.__dump);
                  FStar_Tactics_Types.psc =
                    (uu___123_7718.FStar_Tactics_Types.psc);
                  FStar_Tactics_Types.entry_range =
                    (uu___123_7718.FStar_Tactics_Types.entry_range);
                  FStar_Tactics_Types.guard_policy =
                    (uu___123_7718.FStar_Tactics_Types.guard_policy);
                  FStar_Tactics_Types.freshness =
                    (uu___123_7718.FStar_Tactics_Types.freshness)
                })
         | uu____7719 -> fail "flip: less than 2 goals")
  
let (later : Prims.unit -> Prims.unit tac) =
  fun uu____7726  ->
    bind get
      (fun ps  ->
         match ps.FStar_Tactics_Types.goals with
         | [] -> ret ()
         | g::gs ->
             set
               (let uu___124_7739 = ps  in
                {
                  FStar_Tactics_Types.main_context =
                    (uu___124_7739.FStar_Tactics_Types.main_context);
                  FStar_Tactics_Types.main_goal =
                    (uu___124_7739.FStar_Tactics_Types.main_goal);
                  FStar_Tactics_Types.all_implicits =
                    (uu___124_7739.FStar_Tactics_Types.all_implicits);
                  FStar_Tactics_Types.goals = (FStar_List.append gs [g]);
                  FStar_Tactics_Types.smt_goals =
                    (uu___124_7739.FStar_Tactics_Types.smt_goals);
                  FStar_Tactics_Types.depth =
                    (uu___124_7739.FStar_Tactics_Types.depth);
                  FStar_Tactics_Types.__dump =
                    (uu___124_7739.FStar_Tactics_Types.__dump);
                  FStar_Tactics_Types.psc =
                    (uu___124_7739.FStar_Tactics_Types.psc);
                  FStar_Tactics_Types.entry_range =
                    (uu___124_7739.FStar_Tactics_Types.entry_range);
                  FStar_Tactics_Types.guard_policy =
                    (uu___124_7739.FStar_Tactics_Types.guard_policy);
                  FStar_Tactics_Types.freshness =
                    (uu___124_7739.FStar_Tactics_Types.freshness)
                }))
  
let (qed : Prims.unit -> Prims.unit tac) =
  fun uu____7744  ->
    bind get
      (fun ps  ->
         match ps.FStar_Tactics_Types.goals with
         | [] -> ret ()
         | uu____7751 -> fail "Not done!")
  
let (cases :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 tac)
  =
  fun t  ->
    let uu____7769 =
      let uu____7776 = cur_goal ()  in
      bind uu____7776
        (fun g  ->
           let uu____7786 = __tc g.FStar_Tactics_Types.context t  in
           bind uu____7786
             (fun uu____7822  ->
                match uu____7822 with
                | (t1,typ,guard) ->
                    let uu____7838 = FStar_Syntax_Util.head_and_args typ  in
                    (match uu____7838 with
                     | (hd1,args) ->
                         let uu____7881 =
                           let uu____7894 =
                             let uu____7895 = FStar_Syntax_Util.un_uinst hd1
                                in
                             uu____7895.FStar_Syntax_Syntax.n  in
                           (uu____7894, args)  in
                         (match uu____7881 with
                          | (FStar_Syntax_Syntax.Tm_fvar
                             fv,(p,uu____7914)::(q,uu____7916)::[]) when
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
                                let uu___125_7954 = g  in
                                let uu____7955 =
                                  FStar_TypeChecker_Env.push_bv
                                    g.FStar_Tactics_Types.context v_p
                                   in
                                {
                                  FStar_Tactics_Types.context = uu____7955;
                                  FStar_Tactics_Types.witness =
                                    (uu___125_7954.FStar_Tactics_Types.witness);
                                  FStar_Tactics_Types.goal_ty =
                                    (uu___125_7954.FStar_Tactics_Types.goal_ty);
                                  FStar_Tactics_Types.opts =
                                    (uu___125_7954.FStar_Tactics_Types.opts);
                                  FStar_Tactics_Types.is_guard =
                                    (uu___125_7954.FStar_Tactics_Types.is_guard)
                                }  in
                              let g2 =
                                let uu___126_7957 = g  in
                                let uu____7958 =
                                  FStar_TypeChecker_Env.push_bv
                                    g.FStar_Tactics_Types.context v_q
                                   in
                                {
                                  FStar_Tactics_Types.context = uu____7958;
                                  FStar_Tactics_Types.witness =
                                    (uu___126_7957.FStar_Tactics_Types.witness);
                                  FStar_Tactics_Types.goal_ty =
                                    (uu___126_7957.FStar_Tactics_Types.goal_ty);
                                  FStar_Tactics_Types.opts =
                                    (uu___126_7957.FStar_Tactics_Types.opts);
                                  FStar_Tactics_Types.is_guard =
                                    (uu___126_7957.FStar_Tactics_Types.is_guard)
                                }  in
                              bind __dismiss
                                (fun uu____7965  ->
                                   let uu____7966 = add_goals [g1; g2]  in
                                   bind uu____7966
                                     (fun uu____7975  ->
                                        let uu____7976 =
                                          let uu____7981 =
                                            FStar_Syntax_Syntax.bv_to_name
                                              v_p
                                             in
                                          let uu____7982 =
                                            FStar_Syntax_Syntax.bv_to_name
                                              v_q
                                             in
                                          (uu____7981, uu____7982)  in
                                        ret uu____7976))
                          | uu____7987 ->
                              let uu____8000 =
                                tts g.FStar_Tactics_Types.context typ  in
                              fail1 "Not a disjunction: %s" uu____8000))))
       in
    FStar_All.pipe_left (wrap_err "cases") uu____7769
  
let (set_options : Prims.string -> Prims.unit tac) =
  fun s  ->
    let uu____8028 = cur_goal ()  in
    bind uu____8028
      (fun g  ->
         FStar_Options.push ();
         (let uu____8041 = FStar_Util.smap_copy g.FStar_Tactics_Types.opts
             in
          FStar_Options.set uu____8041);
         (let res = FStar_Options.set_options FStar_Options.Set s  in
          let opts' = FStar_Options.peek ()  in
          FStar_Options.pop ();
          (match res with
           | FStar_Getopt.Success  ->
               let g' =
                 let uu___127_8048 = g  in
                 {
                   FStar_Tactics_Types.context =
                     (uu___127_8048.FStar_Tactics_Types.context);
                   FStar_Tactics_Types.witness =
                     (uu___127_8048.FStar_Tactics_Types.witness);
                   FStar_Tactics_Types.goal_ty =
                     (uu___127_8048.FStar_Tactics_Types.goal_ty);
                   FStar_Tactics_Types.opts = opts';
                   FStar_Tactics_Types.is_guard =
                     (uu___127_8048.FStar_Tactics_Types.is_guard)
                 }  in
               replace_cur g'
           | FStar_Getopt.Error err ->
               fail2 "Setting options `%s` failed: %s" s err
           | FStar_Getopt.Help  ->
               fail1 "Setting options `%s` failed (got `Help`?)" s)))
  
let (top_env : Prims.unit -> env tac) =
  fun uu____8054  ->
    bind get
      (fun ps  -> FStar_All.pipe_left ret ps.FStar_Tactics_Types.main_context)
  
let (cur_env : Prims.unit -> env tac) =
  fun uu____8065  ->
    let uu____8068 = cur_goal ()  in
    bind uu____8068
      (fun g  -> FStar_All.pipe_left ret g.FStar_Tactics_Types.context)
  
let (cur_goal' : Prims.unit -> FStar_Syntax_Syntax.term tac) =
  fun uu____8079  ->
    let uu____8082 = cur_goal ()  in
    bind uu____8082
      (fun g  -> FStar_All.pipe_left ret g.FStar_Tactics_Types.goal_ty)
  
let (cur_witness : Prims.unit -> FStar_Syntax_Syntax.term tac) =
  fun uu____8093  ->
    let uu____8096 = cur_goal ()  in
    bind uu____8096
      (fun g  -> FStar_All.pipe_left ret g.FStar_Tactics_Types.witness)
  
let (unquote :
  FStar_Reflection_Data.typ ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term tac)
  =
  fun ty  ->
    fun tm  ->
      let uu____8113 =
        let uu____8116 = cur_goal ()  in
        bind uu____8116
          (fun goal  ->
             let env =
               FStar_TypeChecker_Env.set_expected_typ
                 goal.FStar_Tactics_Types.context ty
                in
             let uu____8124 = __tc env tm  in
             bind uu____8124
               (fun uu____8144  ->
                  match uu____8144 with
                  | (tm1,typ,guard) ->
                      let uu____8156 =
                        proc_guard "unquote" env guard
                          goal.FStar_Tactics_Types.opts
                         in
                      bind uu____8156 (fun uu____8160  -> ret tm1)))
         in
      FStar_All.pipe_left (wrap_err "unquote") uu____8113
  
let (uvar_env :
  env ->
    FStar_Reflection_Data.typ FStar_Pervasives_Native.option ->
      FStar_Syntax_Syntax.term tac)
  =
  fun env  ->
    fun ty  ->
      let uu____8179 =
        match ty with
        | FStar_Pervasives_Native.Some ty1 -> ret ty1
        | FStar_Pervasives_Native.None  ->
            let uu____8185 =
              let uu____8186 = FStar_Syntax_Util.type_u ()  in
              FStar_All.pipe_left FStar_Pervasives_Native.fst uu____8186  in
            new_uvar "uvar_env.2" env uu____8185
         in
      bind uu____8179
        (fun typ  ->
           let uu____8198 = new_uvar "uvar_env" env typ  in
           bind uu____8198 (fun t  -> ret t))
  
let (unshelve : FStar_Syntax_Syntax.term -> Prims.unit tac) =
  fun t  ->
    let uu____8210 =
      bind get
        (fun ps  ->
           let env = ps.FStar_Tactics_Types.main_context  in
           let opts =
             match ps.FStar_Tactics_Types.goals with
             | g::uu____8227 -> g.FStar_Tactics_Types.opts
             | uu____8230 -> FStar_Options.peek ()  in
           let uu____8233 = FStar_Syntax_Util.head_and_args t  in
           match uu____8233 with
           | ({
                FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                  (uu____8250,typ);
                FStar_Syntax_Syntax.pos = uu____8252;
                FStar_Syntax_Syntax.vars = uu____8253;_},uu____8254)
               ->
               let uu____8299 =
                 let uu____8302 =
                   let uu____8303 = bnorm env t  in
                   let uu____8304 = bnorm env typ  in
                   {
                     FStar_Tactics_Types.context = env;
                     FStar_Tactics_Types.witness = uu____8303;
                     FStar_Tactics_Types.goal_ty = uu____8304;
                     FStar_Tactics_Types.opts = opts;
                     FStar_Tactics_Types.is_guard = false
                   }  in
                 [uu____8302]  in
               add_goals uu____8299
           | uu____8305 -> fail "not a uvar")
       in
    FStar_All.pipe_left (wrap_err "unshelve") uu____8210
  
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
          (fun uu____8352  ->
             let uu____8353 = FStar_Options.unsafe_tactic_exec ()  in
             if uu____8353
             then
               let s =
                 FStar_Util.launch_process true "tactic_launch" prog args
                   input (fun uu____8359  -> fun uu____8360  -> false)
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
        (fun uu____8374  ->
           let uu____8375 =
             FStar_Syntax_Syntax.gen_bv nm FStar_Pervasives_Native.None t  in
           ret uu____8375)
  
let (change : FStar_Reflection_Data.typ -> Prims.unit tac) =
  fun ty  ->
    let uu____8383 =
      mlog
        (fun uu____8388  ->
           let uu____8389 = FStar_Syntax_Print.term_to_string ty  in
           FStar_Util.print1 "change: ty = %s\n" uu____8389)
        (fun uu____8392  ->
           let uu____8393 = cur_goal ()  in
           bind uu____8393
             (fun g  ->
                let uu____8399 = __tc g.FStar_Tactics_Types.context ty  in
                bind uu____8399
                  (fun uu____8419  ->
                     match uu____8419 with
                     | (ty1,uu____8429,guard) ->
                         let uu____8431 =
                           proc_guard "change" g.FStar_Tactics_Types.context
                             guard g.FStar_Tactics_Types.opts
                            in
                         bind uu____8431
                           (fun uu____8436  ->
                              let uu____8437 =
                                do_unify g.FStar_Tactics_Types.context
                                  g.FStar_Tactics_Types.goal_ty ty1
                                 in
                              bind uu____8437
                                (fun bb  ->
                                   if bb
                                   then
                                     replace_cur
                                       (let uu___128_8446 = g  in
                                        {
                                          FStar_Tactics_Types.context =
                                            (uu___128_8446.FStar_Tactics_Types.context);
                                          FStar_Tactics_Types.witness =
                                            (uu___128_8446.FStar_Tactics_Types.witness);
                                          FStar_Tactics_Types.goal_ty = ty1;
                                          FStar_Tactics_Types.opts =
                                            (uu___128_8446.FStar_Tactics_Types.opts);
                                          FStar_Tactics_Types.is_guard =
                                            (uu___128_8446.FStar_Tactics_Types.is_guard)
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
                                      let uu____8453 =
                                        do_unify
                                          g.FStar_Tactics_Types.context ng
                                          nty
                                         in
                                      bind uu____8453
                                        (fun b  ->
                                           if b
                                           then
                                             replace_cur
                                               (let uu___129_8462 = g  in
                                                {
                                                  FStar_Tactics_Types.context
                                                    =
                                                    (uu___129_8462.FStar_Tactics_Types.context);
                                                  FStar_Tactics_Types.witness
                                                    =
                                                    (uu___129_8462.FStar_Tactics_Types.witness);
                                                  FStar_Tactics_Types.goal_ty
                                                    = ty1;
                                                  FStar_Tactics_Types.opts =
                                                    (uu___129_8462.FStar_Tactics_Types.opts);
                                                  FStar_Tactics_Types.is_guard
                                                    =
                                                    (uu___129_8462.FStar_Tactics_Types.is_guard)
                                                })
                                           else fail "not convertible")))))))
       in
    FStar_All.pipe_left (wrap_err "change") uu____8383
  
let rec last : 'a . 'a Prims.list -> 'a =
  fun l  ->
    match l with
    | [] -> failwith "last: empty list"
    | x::[] -> x
    | uu____8481::xs -> last xs
  
let rec init : 'a . 'a Prims.list -> 'a Prims.list =
  fun l  ->
    match l with
    | [] -> failwith "init: empty list"
    | x::[] -> []
    | x::xs -> let uu____8506 = init xs  in x :: uu____8506
  
let rec (inspect :
  FStar_Syntax_Syntax.term -> FStar_Reflection_Data.term_view tac) =
  fun t  ->
    let t1 = FStar_Syntax_Util.unascribe t  in
    let t2 = FStar_Syntax_Util.un_uinst t1  in
    match t2.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_meta (t3,uu____8521) -> inspect t3
    | FStar_Syntax_Syntax.Tm_name bv ->
        FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_Var bv)
    | FStar_Syntax_Syntax.Tm_bvar bv ->
        FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_BVar bv)
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_FVar fv)
    | FStar_Syntax_Syntax.Tm_app (hd1,[]) ->
        failwith "inspect: empty arguments on Tm_app"
    | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
        let uu____8578 = last args  in
        (match uu____8578 with
         | (a,q) ->
             let q' = FStar_Reflection_Basic.inspect_aqual q  in
             let uu____8600 =
               let uu____8601 =
                 let uu____8606 =
                   let uu____8609 =
                     let uu____8610 = init args  in
                     FStar_Syntax_Syntax.mk_Tm_app hd1 uu____8610  in
                   uu____8609 FStar_Pervasives_Native.None
                     t2.FStar_Syntax_Syntax.pos
                    in
                 (uu____8606, (a, q'))  in
               FStar_Reflection_Data.Tv_App uu____8601  in
             FStar_All.pipe_left ret uu____8600)
    | FStar_Syntax_Syntax.Tm_abs ([],uu____8631,uu____8632) ->
        failwith "inspect: empty arguments on Tm_abs"
    | FStar_Syntax_Syntax.Tm_abs (bs,t3,k) ->
        let uu____8676 = FStar_Syntax_Subst.open_term bs t3  in
        (match uu____8676 with
         | (bs1,t4) ->
             (match bs1 with
              | [] -> failwith "impossible"
              | b::bs2 ->
                  let uu____8709 =
                    let uu____8710 =
                      let uu____8715 = FStar_Syntax_Util.abs bs2 t4 k  in
                      (b, uu____8715)  in
                    FStar_Reflection_Data.Tv_Abs uu____8710  in
                  FStar_All.pipe_left ret uu____8709))
    | FStar_Syntax_Syntax.Tm_type uu____8722 ->
        FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_Type ())
    | FStar_Syntax_Syntax.Tm_arrow ([],k) ->
        failwith "inspect: empty binders on arrow"
    | FStar_Syntax_Syntax.Tm_arrow uu____8742 ->
        let uu____8755 = FStar_Syntax_Util.arrow_one t2  in
        (match uu____8755 with
         | FStar_Pervasives_Native.Some (b,c) ->
             FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_Arrow (b, c))
         | FStar_Pervasives_Native.None  -> failwith "impossible")
    | FStar_Syntax_Syntax.Tm_refine (bv,t3) ->
        let b = FStar_Syntax_Syntax.mk_binder bv  in
        let uu____8785 = FStar_Syntax_Subst.open_term [b] t3  in
        (match uu____8785 with
         | (b',t4) ->
             let b1 =
               match b' with
               | b'1::[] -> b'1
               | uu____8816 -> failwith "impossible"  in
             FStar_All.pipe_left ret
               (FStar_Reflection_Data.Tv_Refine
                  ((FStar_Pervasives_Native.fst b1), t4)))
    | FStar_Syntax_Syntax.Tm_constant c ->
        let uu____8824 =
          let uu____8825 = FStar_Reflection_Basic.inspect_const c  in
          FStar_Reflection_Data.Tv_Const uu____8825  in
        FStar_All.pipe_left ret uu____8824
    | FStar_Syntax_Syntax.Tm_uvar (u,t3) ->
        let uu____8854 =
          let uu____8855 =
            let uu____8860 =
              let uu____8861 = FStar_Syntax_Unionfind.uvar_id u  in
              FStar_BigInt.of_int_fs uu____8861  in
            (uu____8860, t3)  in
          FStar_Reflection_Data.Tv_Uvar uu____8855  in
        FStar_All.pipe_left ret uu____8854
    | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),t21) ->
        if lb.FStar_Syntax_Syntax.lbunivs <> []
        then FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown
        else
          (match lb.FStar_Syntax_Syntax.lbname with
           | FStar_Util.Inr uu____8889 ->
               FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown
           | FStar_Util.Inl bv ->
               let b = FStar_Syntax_Syntax.mk_binder bv  in
               let uu____8894 = FStar_Syntax_Subst.open_term [b] t21  in
               (match uu____8894 with
                | (bs,t22) ->
                    let b1 =
                      match bs with
                      | b1::[] -> b1
                      | uu____8925 ->
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
           | FStar_Util.Inr uu____8957 ->
               FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown
           | FStar_Util.Inl bv ->
               let uu____8961 = FStar_Syntax_Subst.open_let_rec [lb] t21  in
               (match uu____8961 with
                | (lbs,t22) ->
                    (match lbs with
                     | lb1::[] ->
                         (match lb1.FStar_Syntax_Syntax.lbname with
                          | FStar_Util.Inr uu____8981 ->
                              ret FStar_Reflection_Data.Tv_Unknown
                          | FStar_Util.Inl bv1 ->
                              FStar_All.pipe_left ret
                                (FStar_Reflection_Data.Tv_Let
                                   (true, bv1,
                                     (lb1.FStar_Syntax_Syntax.lbdef), t22)))
                     | uu____8987 ->
                         failwith
                           "impossible: open_term returned different amount of binders")))
    | FStar_Syntax_Syntax.Tm_match (t3,brs) ->
        let rec inspect_pat p =
          match p.FStar_Syntax_Syntax.v with
          | FStar_Syntax_Syntax.Pat_constant c ->
              let uu____9039 = FStar_Reflection_Basic.inspect_const c  in
              FStar_Reflection_Data.Pat_Constant uu____9039
          | FStar_Syntax_Syntax.Pat_cons (fv,ps) ->
              let uu____9058 =
                let uu____9065 =
                  FStar_List.map
                    (fun uu____9077  ->
                       match uu____9077 with
                       | (p1,uu____9085) -> inspect_pat p1) ps
                   in
                (fv, uu____9065)  in
              FStar_Reflection_Data.Pat_Cons uu____9058
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
            (fun uu___63_9139  ->
               match uu___63_9139 with
               | (pat,uu____9161,t4) ->
                   let uu____9179 = inspect_pat pat  in (uu____9179, t4))
            brs1
           in
        FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_Match (t3, brs2))
    | FStar_Syntax_Syntax.Tm_unknown  ->
        FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown
    | uu____9196 ->
        ((let uu____9198 =
            let uu____9203 =
              let uu____9204 = FStar_Syntax_Print.tag_of_term t2  in
              let uu____9205 = FStar_Syntax_Print.term_to_string t2  in
              FStar_Util.format2
                "inspect: outside of expected syntax (%s, %s)\n" uu____9204
                uu____9205
               in
            (FStar_Errors.Warning_CantInspect, uu____9203)  in
          FStar_Errors.log_issue t2.FStar_Syntax_Syntax.pos uu____9198);
         FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown)
  
let (pack : FStar_Reflection_Data.term_view -> FStar_Syntax_Syntax.term tac)
  =
  fun tv  ->
    match tv with
    | FStar_Reflection_Data.Tv_Var bv ->
        let uu____9216 = FStar_Syntax_Syntax.bv_to_name bv  in
        FStar_All.pipe_left ret uu____9216
    | FStar_Reflection_Data.Tv_BVar bv ->
        let uu____9220 = FStar_Syntax_Syntax.bv_to_tm bv  in
        FStar_All.pipe_left ret uu____9220
    | FStar_Reflection_Data.Tv_FVar fv ->
        let uu____9224 = FStar_Syntax_Syntax.fv_to_tm fv  in
        FStar_All.pipe_left ret uu____9224
    | FStar_Reflection_Data.Tv_App (l,(r,q)) ->
        let q' = FStar_Reflection_Basic.pack_aqual q  in
        let uu____9235 = FStar_Syntax_Util.mk_app l [(r, q')]  in
        FStar_All.pipe_left ret uu____9235
    | FStar_Reflection_Data.Tv_Abs (b,t) ->
        let uu____9256 =
          FStar_Syntax_Util.abs [b] t FStar_Pervasives_Native.None  in
        FStar_All.pipe_left ret uu____9256
    | FStar_Reflection_Data.Tv_Arrow (b,c) ->
        let uu____9261 = FStar_Syntax_Util.arrow [b] c  in
        FStar_All.pipe_left ret uu____9261
    | FStar_Reflection_Data.Tv_Type () ->
        FStar_All.pipe_left ret FStar_Syntax_Util.ktype
    | FStar_Reflection_Data.Tv_Refine (bv,t) ->
        let uu____9282 = FStar_Syntax_Util.refine bv t  in
        FStar_All.pipe_left ret uu____9282
    | FStar_Reflection_Data.Tv_Const c ->
        let uu____9294 =
          let uu____9297 =
            let uu____9300 =
              let uu____9301 = FStar_Reflection_Basic.pack_const c  in
              FStar_Syntax_Syntax.Tm_constant uu____9301  in
            FStar_Syntax_Syntax.mk uu____9300  in
          uu____9297 FStar_Pervasives_Native.None FStar_Range.dummyRange  in
        FStar_All.pipe_left ret uu____9294
    | FStar_Reflection_Data.Tv_Uvar (u,t) ->
        let uu____9315 =
          let uu____9318 = FStar_BigInt.to_int_fs u  in
          FStar_Syntax_Util.uvar_from_id uu____9318 t  in
        FStar_All.pipe_left ret uu____9315
    | FStar_Reflection_Data.Tv_Let (false ,bv,t1,t2) ->
        let lb =
          FStar_Syntax_Util.mk_letbinding (FStar_Util.Inl bv) []
            bv.FStar_Syntax_Syntax.sort FStar_Parser_Const.effect_Tot_lid t1
            [] FStar_Range.dummyRange
           in
        let uu____9333 =
          let uu____9336 =
            let uu____9339 =
              let uu____9340 =
                let uu____9353 =
                  let uu____9354 =
                    let uu____9355 = FStar_Syntax_Syntax.mk_binder bv  in
                    [uu____9355]  in
                  FStar_Syntax_Subst.close uu____9354 t2  in
                ((false, [lb]), uu____9353)  in
              FStar_Syntax_Syntax.Tm_let uu____9340  in
            FStar_Syntax_Syntax.mk uu____9339  in
          uu____9336 FStar_Pervasives_Native.None FStar_Range.dummyRange  in
        FStar_All.pipe_left ret uu____9333
    | FStar_Reflection_Data.Tv_Let (true ,bv,t1,t2) ->
        let lb =
          FStar_Syntax_Util.mk_letbinding (FStar_Util.Inl bv) []
            bv.FStar_Syntax_Syntax.sort FStar_Parser_Const.effect_Tot_lid t1
            [] FStar_Range.dummyRange
           in
        let uu____9381 = FStar_Syntax_Subst.close_let_rec [lb] t2  in
        (match uu____9381 with
         | (lbs,body) ->
             let uu____9396 =
               FStar_Syntax_Syntax.mk
                 (FStar_Syntax_Syntax.Tm_let ((true, lbs), body))
                 FStar_Pervasives_Native.None FStar_Range.dummyRange
                in
             FStar_All.pipe_left ret uu____9396)
    | FStar_Reflection_Data.Tv_Match (t,brs) ->
        let wrap v1 =
          {
            FStar_Syntax_Syntax.v = v1;
            FStar_Syntax_Syntax.p = FStar_Range.dummyRange
          }  in
        let rec pack_pat p =
          match p with
          | FStar_Reflection_Data.Pat_Constant c ->
              let uu____9432 =
                let uu____9433 = FStar_Reflection_Basic.pack_const c  in
                FStar_Syntax_Syntax.Pat_constant uu____9433  in
              FStar_All.pipe_left wrap uu____9432
          | FStar_Reflection_Data.Pat_Cons (fv,ps) ->
              let uu____9442 =
                let uu____9443 =
                  let uu____9456 =
                    FStar_List.map
                      (fun p1  ->
                         let uu____9470 = pack_pat p1  in (uu____9470, false))
                      ps
                     in
                  (fv, uu____9456)  in
                FStar_Syntax_Syntax.Pat_cons uu____9443  in
              FStar_All.pipe_left wrap uu____9442
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
            (fun uu___64_9520  ->
               match uu___64_9520 with
               | (pat,t1) ->
                   let uu____9537 = pack_pat pat  in
                   (uu____9537, FStar_Pervasives_Native.None, t1)) brs
           in
        let brs2 = FStar_List.map FStar_Syntax_Subst.close_branch brs1  in
        let uu____9547 =
          FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_match (t, brs2))
            FStar_Pervasives_Native.None FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____9547
    | FStar_Reflection_Data.Tv_AscribedT (e,t,tacopt) ->
        let uu____9567 =
          FStar_Syntax_Syntax.mk
            (FStar_Syntax_Syntax.Tm_ascribed
               (e, ((FStar_Util.Inl t), tacopt),
                 FStar_Pervasives_Native.None)) FStar_Pervasives_Native.None
            FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____9567
    | FStar_Reflection_Data.Tv_AscribedC (e,c,tacopt) ->
        let uu____9609 =
          FStar_Syntax_Syntax.mk
            (FStar_Syntax_Syntax.Tm_ascribed
               (e, ((FStar_Util.Inr c), tacopt),
                 FStar_Pervasives_Native.None)) FStar_Pervasives_Native.None
            FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____9609
    | FStar_Reflection_Data.Tv_Unknown  ->
        let uu____9644 =
          FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown
            FStar_Pervasives_Native.None FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____9644
  
let (goal_of_goal_ty :
  env ->
    FStar_Reflection_Data.typ ->
      (FStar_Tactics_Types.goal,FStar_TypeChecker_Env.guard_t)
        FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun typ  ->
      let uu____9669 =
        FStar_TypeChecker_Util.new_implicit_var "proofstate_of_goal_ty"
          typ.FStar_Syntax_Syntax.pos env typ
         in
      match uu____9669 with
      | (u,uu____9687,g_u) ->
          let g =
            let uu____9702 = FStar_Options.peek ()  in
            {
              FStar_Tactics_Types.context = env;
              FStar_Tactics_Types.witness = u;
              FStar_Tactics_Types.goal_ty = typ;
              FStar_Tactics_Types.opts = uu____9702;
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
      let uu____9713 = goal_of_goal_ty env typ  in
      match uu____9713 with
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
  