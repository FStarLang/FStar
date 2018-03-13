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
  
let (idtac : Prims.unit tac) = ret () 
let (goal_to_string : FStar_Tactics_Types.goal -> Prims.string) =
  fun g  ->
    let g_binders =
      let uu____158 =
        FStar_TypeChecker_Env.all_binders g.FStar_Tactics_Types.context  in
      FStar_All.pipe_right uu____158
        (FStar_Syntax_Print.binders_to_string ", ")
       in
    let w = bnorm g.FStar_Tactics_Types.context g.FStar_Tactics_Types.witness
       in
    let t = bnorm g.FStar_Tactics_Types.context g.FStar_Tactics_Types.goal_ty
       in
    let uu____161 = tts g.FStar_Tactics_Types.context w  in
    let uu____162 = tts g.FStar_Tactics_Types.context t  in
    FStar_Util.format3 "%s |- %s : %s" g_binders uu____161 uu____162
  
let (tacprint : Prims.string -> Prims.unit) =
  fun s  -> FStar_Util.print1 "TAC>> %s\n" s 
let (tacprint1 : Prims.string -> Prims.string -> Prims.unit) =
  fun s  ->
    fun x  ->
      let uu____172 = FStar_Util.format1 s x  in
      FStar_Util.print1 "TAC>> %s\n" uu____172
  
let (tacprint2 : Prims.string -> Prims.string -> Prims.string -> Prims.unit)
  =
  fun s  ->
    fun x  ->
      fun y  ->
        let uu____182 = FStar_Util.format2 s x y  in
        FStar_Util.print1 "TAC>> %s\n" uu____182
  
let (tacprint3 :
  Prims.string -> Prims.string -> Prims.string -> Prims.string -> Prims.unit)
  =
  fun s  ->
    fun x  ->
      fun y  ->
        fun z  ->
          let uu____195 = FStar_Util.format3 s x y z  in
          FStar_Util.print1 "TAC>> %s\n" uu____195
  
let (comp_to_typ : FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.typ) =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Total (t,uu____200) -> t
    | FStar_Syntax_Syntax.GTotal (t,uu____210) -> t
    | FStar_Syntax_Syntax.Comp ct -> ct.FStar_Syntax_Syntax.result_typ
  
let (is_irrelevant : FStar_Tactics_Types.goal -> Prims.bool) =
  fun g  ->
    let uu____223 =
      let uu____228 =
        FStar_TypeChecker_Normalize.unfold_whnf g.FStar_Tactics_Types.context
          g.FStar_Tactics_Types.goal_ty
         in
      FStar_Syntax_Util.un_squash uu____228  in
    match uu____223 with
    | FStar_Pervasives_Native.Some t -> true
    | uu____234 -> false
  
let dump_goal :
  'Auu____242 . 'Auu____242 -> FStar_Tactics_Types.goal -> Prims.unit =
  fun ps  ->
    fun goal  -> let uu____252 = goal_to_string goal  in tacprint uu____252
  
let (dump_cur : FStar_Tactics_Types.proofstate -> Prims.string -> Prims.unit)
  =
  fun ps  ->
    fun msg  ->
      match ps.FStar_Tactics_Types.goals with
      | [] -> tacprint1 "No more goals (%s)" msg
      | h::uu____260 ->
          (tacprint1 "Current goal (%s):" msg;
           (let uu____264 = FStar_List.hd ps.FStar_Tactics_Types.goals  in
            dump_goal ps uu____264))
  
let (ps_to_string :
  (Prims.string,FStar_Tactics_Types.proofstate)
    FStar_Pervasives_Native.tuple2 -> Prims.string)
  =
  fun uu____271  ->
    match uu____271 with
    | (msg,ps) ->
        let uu____278 =
          let uu____281 =
            let uu____282 =
              FStar_Util.string_of_int ps.FStar_Tactics_Types.depth  in
            FStar_Util.format2 "State dump @ depth %s (%s):\n" uu____282 msg
             in
          let uu____283 =
            let uu____286 =
              let uu____287 =
                FStar_Range.string_of_range
                  ps.FStar_Tactics_Types.entry_range
                 in
              FStar_Util.format1 "Location: %s\n" uu____287  in
            let uu____288 =
              let uu____291 =
                let uu____292 =
                  FStar_Util.string_of_int
                    (FStar_List.length ps.FStar_Tactics_Types.goals)
                   in
                let uu____293 =
                  let uu____294 =
                    FStar_List.map goal_to_string
                      ps.FStar_Tactics_Types.goals
                     in
                  FStar_String.concat "\n" uu____294  in
                FStar_Util.format2 "ACTIVE goals (%s):\n%s\n" uu____292
                  uu____293
                 in
              let uu____297 =
                let uu____300 =
                  let uu____301 =
                    FStar_Util.string_of_int
                      (FStar_List.length ps.FStar_Tactics_Types.smt_goals)
                     in
                  let uu____302 =
                    let uu____303 =
                      FStar_List.map goal_to_string
                        ps.FStar_Tactics_Types.smt_goals
                       in
                    FStar_String.concat "\n" uu____303  in
                  FStar_Util.format2 "SMT goals (%s):\n%s\n" uu____301
                    uu____302
                   in
                [uu____300]  in
              uu____291 :: uu____297  in
            uu____286 :: uu____288  in
          uu____281 :: uu____283  in
        FStar_String.concat "" uu____278
  
let (goal_to_json : FStar_Tactics_Types.goal -> FStar_Util.json) =
  fun g  ->
    let g_binders =
      let uu____310 =
        FStar_TypeChecker_Env.all_binders g.FStar_Tactics_Types.context  in
      let uu____311 =
        let uu____314 =
          FStar_TypeChecker_Env.dsenv g.FStar_Tactics_Types.context  in
        FStar_Syntax_Print.binders_to_json uu____314  in
      FStar_All.pipe_right uu____310 uu____311  in
    let uu____315 =
      let uu____322 =
        let uu____329 =
          let uu____334 =
            let uu____335 =
              let uu____342 =
                let uu____347 =
                  let uu____348 =
                    tts g.FStar_Tactics_Types.context
                      g.FStar_Tactics_Types.witness
                     in
                  FStar_Util.JsonStr uu____348  in
                ("witness", uu____347)  in
              let uu____349 =
                let uu____356 =
                  let uu____361 =
                    let uu____362 =
                      tts g.FStar_Tactics_Types.context
                        g.FStar_Tactics_Types.goal_ty
                       in
                    FStar_Util.JsonStr uu____362  in
                  ("type", uu____361)  in
                [uu____356]  in
              uu____342 :: uu____349  in
            FStar_Util.JsonAssoc uu____335  in
          ("goal", uu____334)  in
        [uu____329]  in
      ("hyps", g_binders) :: uu____322  in
    FStar_Util.JsonAssoc uu____315
  
let (ps_to_json :
  (Prims.string,FStar_Tactics_Types.proofstate)
    FStar_Pervasives_Native.tuple2 -> FStar_Util.json)
  =
  fun uu____393  ->
    match uu____393 with
    | (msg,ps) ->
        let uu____400 =
          let uu____407 =
            let uu____414 =
              let uu____421 =
                let uu____428 =
                  let uu____433 =
                    let uu____434 =
                      FStar_List.map goal_to_json
                        ps.FStar_Tactics_Types.goals
                       in
                    FStar_Util.JsonList uu____434  in
                  ("goals", uu____433)  in
                let uu____437 =
                  let uu____444 =
                    let uu____449 =
                      let uu____450 =
                        FStar_List.map goal_to_json
                          ps.FStar_Tactics_Types.smt_goals
                         in
                      FStar_Util.JsonList uu____450  in
                    ("smt-goals", uu____449)  in
                  [uu____444]  in
                uu____428 :: uu____437  in
              ("depth", (FStar_Util.JsonInt (ps.FStar_Tactics_Types.depth)))
                :: uu____421
               in
            ("label", (FStar_Util.JsonStr msg)) :: uu____414  in
          let uu____473 =
            if ps.FStar_Tactics_Types.entry_range <> FStar_Range.dummyRange
            then
              let uu____486 =
                let uu____491 =
                  FStar_Range.json_of_def_range
                    ps.FStar_Tactics_Types.entry_range
                   in
                ("location", uu____491)  in
              [uu____486]
            else []  in
          FStar_List.append uu____407 uu____473  in
        FStar_Util.JsonAssoc uu____400
  
let (dump_proofstate :
  FStar_Tactics_Types.proofstate -> Prims.string -> Prims.unit) =
  fun ps  ->
    fun msg  ->
      FStar_Options.with_saved_options
        (fun uu____517  ->
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
         (let uu____538 = FStar_Tactics_Types.subst_proof_state subst1 ps  in
          dump_cur uu____538 msg);
         FStar_Tactics_Result.Success ((), ps))
  
let (print_proof_state : Prims.string -> Prims.unit tac) =
  fun msg  ->
    mk_tac
      (fun ps  ->
         let psc = ps.FStar_Tactics_Types.psc  in
         let subst1 = FStar_TypeChecker_Normalize.psc_subst psc  in
         (let uu____554 = FStar_Tactics_Types.subst_proof_state subst1 ps  in
          dump_proofstate uu____554 msg);
         FStar_Tactics_Result.Success ((), ps))
  
let (get : FStar_Tactics_Types.proofstate tac) =
  mk_tac (fun p  -> FStar_Tactics_Result.Success (p, p)) 
let (tac_verb_dbg : Prims.bool FStar_Pervasives_Native.option FStar_ST.ref) =
  FStar_Util.mk_ref FStar_Pervasives_Native.None 
let rec (log :
  FStar_Tactics_Types.proofstate -> (Prims.unit -> Prims.unit) -> Prims.unit)
  =
  fun ps  ->
    fun f  ->
      let uu____589 = FStar_ST.op_Bang tac_verb_dbg  in
      match uu____589 with
      | FStar_Pervasives_Native.None  ->
          ((let uu____616 =
              let uu____619 =
                FStar_TypeChecker_Env.debug
                  ps.FStar_Tactics_Types.main_context
                  (FStar_Options.Other "TacVerbose")
                 in
              FStar_Pervasives_Native.Some uu____619  in
            FStar_ST.op_Colon_Equals tac_verb_dbg uu____616);
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
         (let uu____688 =
            FStar_TypeChecker_Env.debug ps.FStar_Tactics_Types.main_context
              (FStar_Options.Other "TacFail")
             in
          if uu____688
          then dump_proofstate ps (Prims.strcat "TACTIC FAILING: " msg)
          else ());
         FStar_Tactics_Result.Failed (msg, ps))
  
let fail1 : 'Auu____693 . Prims.string -> Prims.string -> 'Auu____693 tac =
  fun msg  ->
    fun x  -> let uu____704 = FStar_Util.format1 msg x  in fail uu____704
  
let fail2 :
  'Auu____709 .
    Prims.string -> Prims.string -> Prims.string -> 'Auu____709 tac
  =
  fun msg  ->
    fun x  ->
      fun y  -> let uu____724 = FStar_Util.format2 msg x y  in fail uu____724
  
let fail3 :
  'Auu____730 .
    Prims.string ->
      Prims.string -> Prims.string -> Prims.string -> 'Auu____730 tac
  =
  fun msg  ->
    fun x  ->
      fun y  ->
        fun z  ->
          let uu____749 = FStar_Util.format3 msg x y z  in fail uu____749
  
let fail4 :
  'Auu____756 .
    Prims.string ->
      Prims.string ->
        Prims.string -> Prims.string -> Prims.string -> 'Auu____756 tac
  =
  fun msg  ->
    fun x  ->
      fun y  ->
        fun z  ->
          fun w  ->
            let uu____779 = FStar_Util.format4 msg x y z w  in fail uu____779
  
let trytac' : 'a . 'a tac -> (Prims.string,'a) FStar_Util.either tac =
  fun t  ->
    mk_tac
      (fun ps  ->
         let tx = FStar_Syntax_Unionfind.new_transaction ()  in
         let uu____809 = run t ps  in
         match uu____809 with
         | FStar_Tactics_Result.Success (a,q) ->
             (FStar_Syntax_Unionfind.commit tx;
              FStar_Tactics_Result.Success ((FStar_Util.Inr a), q))
         | FStar_Tactics_Result.Failed (m,uu____830) ->
             (FStar_Syntax_Unionfind.rollback tx;
              FStar_Tactics_Result.Success ((FStar_Util.Inl m), ps)))
  
let trytac : 'a . 'a tac -> 'a FStar_Pervasives_Native.option tac =
  fun t  ->
    let uu____855 = trytac' t  in
    bind uu____855
      (fun r  ->
         match r with
         | FStar_Util.Inr v1 -> ret (FStar_Pervasives_Native.Some v1)
         | FStar_Util.Inl uu____882 -> ret FStar_Pervasives_Native.None)
  
let trytac_exn : 'a . 'a tac -> 'a FStar_Pervasives_Native.option tac =
  fun t  ->
    mk_tac
      (fun ps  ->
         try let uu____915 = trytac t  in run uu____915 ps
         with
         | FStar_Errors.Err (uu____931,msg) ->
             (log ps
                (fun uu____935  ->
                   FStar_Util.print1 "trytac_exn error: (%s)" msg);
              FStar_Tactics_Result.Success (FStar_Pervasives_Native.None, ps))
         | FStar_Errors.Error (uu____940,msg,uu____942) ->
             (log ps
                (fun uu____945  ->
                   FStar_Util.print1 "trytac_exn error: (%s)" msg);
              FStar_Tactics_Result.Success (FStar_Pervasives_Native.None, ps)))
  
let wrap_err : 'a . Prims.string -> 'a tac -> 'a tac =
  fun pref  ->
    fun t  ->
      mk_tac
        (fun ps  ->
           let uu____973 = run t ps  in
           match uu____973 with
           | FStar_Tactics_Result.Success (a,q) ->
               FStar_Tactics_Result.Success (a, q)
           | FStar_Tactics_Result.Failed (msg,q) ->
               FStar_Tactics_Result.Failed
                 ((Prims.strcat pref (Prims.strcat ": " msg)), q))
  
let (set : FStar_Tactics_Types.proofstate -> Prims.unit tac) =
  fun p  -> mk_tac (fun uu____990  -> FStar_Tactics_Result.Success ((), p)) 
let (__do_unify :
  env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.bool tac)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let debug_on uu____1007 =
          let uu____1008 =
            FStar_Options.set_options FStar_Options.Set
              "--debug_level Rel --debug_level RelCheck"
             in
          ()  in
        let debug_off uu____1012 =
          let uu____1013 = FStar_Options.set_options FStar_Options.Reset ""
             in
          ()  in
        (let uu____1015 =
           FStar_TypeChecker_Env.debug env (FStar_Options.Other "1346")  in
         if uu____1015
         then
           (debug_on ();
            (let uu____1017 = FStar_Syntax_Print.term_to_string t1  in
             let uu____1018 = FStar_Syntax_Print.term_to_string t2  in
             FStar_Util.print2 "%%%%%%%%do_unify %s =? %s\n" uu____1017
               uu____1018))
         else ());
        (try
           let res = FStar_TypeChecker_Rel.teq_nosmt env t1 t2  in
           debug_off (); ret res
         with
         | FStar_Errors.Err (uu____1037,msg) ->
             (debug_off ();
              mlog
                (fun uu____1041  ->
                   FStar_Util.print1 ">> do_unify error, (%s)\n" msg)
                (fun uu____1043  -> ret false))
         | FStar_Errors.Error (uu____1044,msg,r) ->
             (debug_off ();
              mlog
                (fun uu____1050  ->
                   let uu____1051 = FStar_Range.string_of_range r  in
                   FStar_Util.print2 ">> do_unify error, (%s) at (%s)\n" msg
                     uu____1051) (fun uu____1053  -> ret false)))
  
let (do_unify :
  env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.bool tac)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____1067 = __do_unify env t1 t2  in
        bind uu____1067
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
  
let (dismiss : Prims.unit tac) =
  bind get
    (fun p  ->
       let uu____1096 =
         let uu___63_1097 = p  in
         let uu____1098 = FStar_List.tl p.FStar_Tactics_Types.goals  in
         {
           FStar_Tactics_Types.main_context =
             (uu___63_1097.FStar_Tactics_Types.main_context);
           FStar_Tactics_Types.main_goal =
             (uu___63_1097.FStar_Tactics_Types.main_goal);
           FStar_Tactics_Types.all_implicits =
             (uu___63_1097.FStar_Tactics_Types.all_implicits);
           FStar_Tactics_Types.goals = uu____1098;
           FStar_Tactics_Types.smt_goals =
             (uu___63_1097.FStar_Tactics_Types.smt_goals);
           FStar_Tactics_Types.depth =
             (uu___63_1097.FStar_Tactics_Types.depth);
           FStar_Tactics_Types.__dump =
             (uu___63_1097.FStar_Tactics_Types.__dump);
           FStar_Tactics_Types.psc = (uu___63_1097.FStar_Tactics_Types.psc);
           FStar_Tactics_Types.entry_range =
             (uu___63_1097.FStar_Tactics_Types.entry_range);
           FStar_Tactics_Types.guard_policy =
             (uu___63_1097.FStar_Tactics_Types.guard_policy)
         }  in
       set uu____1096)
  
let (solve :
  FStar_Tactics_Types.goal -> FStar_Syntax_Syntax.term -> Prims.unit tac) =
  fun goal  ->
    fun solution  ->
      let uu____1111 = trysolve goal solution  in
      bind uu____1111
        (fun b  ->
           if b
           then dismiss
           else
             (let uu____1119 =
                let uu____1120 =
                  tts goal.FStar_Tactics_Types.context solution  in
                let uu____1121 =
                  tts goal.FStar_Tactics_Types.context
                    goal.FStar_Tactics_Types.witness
                   in
                let uu____1122 =
                  tts goal.FStar_Tactics_Types.context
                    goal.FStar_Tactics_Types.goal_ty
                   in
                FStar_Util.format3 "%s does not solve %s : %s" uu____1120
                  uu____1121 uu____1122
                 in
              fail uu____1119))
  
let (dismiss_all : Prims.unit tac) =
  bind get
    (fun p  ->
       set
         (let uu___64_1129 = p  in
          {
            FStar_Tactics_Types.main_context =
              (uu___64_1129.FStar_Tactics_Types.main_context);
            FStar_Tactics_Types.main_goal =
              (uu___64_1129.FStar_Tactics_Types.main_goal);
            FStar_Tactics_Types.all_implicits =
              (uu___64_1129.FStar_Tactics_Types.all_implicits);
            FStar_Tactics_Types.goals = [];
            FStar_Tactics_Types.smt_goals =
              (uu___64_1129.FStar_Tactics_Types.smt_goals);
            FStar_Tactics_Types.depth =
              (uu___64_1129.FStar_Tactics_Types.depth);
            FStar_Tactics_Types.__dump =
              (uu___64_1129.FStar_Tactics_Types.__dump);
            FStar_Tactics_Types.psc = (uu___64_1129.FStar_Tactics_Types.psc);
            FStar_Tactics_Types.entry_range =
              (uu___64_1129.FStar_Tactics_Types.entry_range);
            FStar_Tactics_Types.guard_policy =
              (uu___64_1129.FStar_Tactics_Types.guard_policy)
          }))
  
let (nwarn : Prims.int FStar_ST.ref) =
  FStar_Util.mk_ref (Prims.parse_int "0") 
let (check_valid_goal : FStar_Tactics_Types.goal -> Prims.unit) =
  fun g  ->
    let uu____1146 = FStar_Options.defensive ()  in
    if uu____1146
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
        let uu____1158 = FStar_TypeChecker_Env.pop_bv e  in
        match uu____1158 with
        | FStar_Pervasives_Native.None  -> b3
        | FStar_Pervasives_Native.Some (bv,e1) ->
            let b4 =
              b3 &&
                (FStar_TypeChecker_Env.closed e1 bv.FStar_Syntax_Syntax.sort)
               in
            aux b4 e1
         in
      let uu____1176 =
        (let uu____1179 = aux b2 env  in Prims.op_Negation uu____1179) &&
          (let uu____1181 = FStar_ST.op_Bang nwarn  in
           uu____1181 < (Prims.parse_int "5"))
         in
      (if uu____1176
       then
         ((let uu____1202 =
             let uu____1207 =
               let uu____1208 = goal_to_string g  in
               FStar_Util.format1
                 "The following goal is ill-formed. Keeping calm and carrying on...\n<%s>\n\n"
                 uu____1208
                in
             (FStar_Errors.Warning_IllFormedGoal, uu____1207)  in
           FStar_Errors.log_issue
             (g.FStar_Tactics_Types.goal_ty).FStar_Syntax_Syntax.pos
             uu____1202);
          (let uu____1209 =
             let uu____1210 = FStar_ST.op_Bang nwarn  in
             uu____1210 + (Prims.parse_int "1")  in
           FStar_ST.op_Colon_Equals nwarn uu____1209))
       else ())
    else ()
  
let (add_goals : FStar_Tactics_Types.goal Prims.list -> Prims.unit tac) =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___65_1268 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___65_1268.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___65_1268.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___65_1268.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (FStar_List.append gs p.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (uu___65_1268.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___65_1268.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___65_1268.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___65_1268.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___65_1268.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___65_1268.FStar_Tactics_Types.guard_policy)
            }))
  
let (add_smt_goals : FStar_Tactics_Types.goal Prims.list -> Prims.unit tac) =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___66_1286 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___66_1286.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___66_1286.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___66_1286.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___66_1286.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (FStar_List.append gs p.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___66_1286.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___66_1286.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___66_1286.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___66_1286.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___66_1286.FStar_Tactics_Types.guard_policy)
            }))
  
let (push_goals : FStar_Tactics_Types.goal Prims.list -> Prims.unit tac) =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___67_1304 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___67_1304.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___67_1304.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___67_1304.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (FStar_List.append p.FStar_Tactics_Types.goals gs);
              FStar_Tactics_Types.smt_goals =
                (uu___67_1304.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___67_1304.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___67_1304.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___67_1304.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___67_1304.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___67_1304.FStar_Tactics_Types.guard_policy)
            }))
  
let (push_smt_goals : FStar_Tactics_Types.goal Prims.list -> Prims.unit tac)
  =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___68_1322 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___68_1322.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___68_1322.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___68_1322.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___68_1322.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (FStar_List.append p.FStar_Tactics_Types.smt_goals gs);
              FStar_Tactics_Types.depth =
                (uu___68_1322.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___68_1322.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___68_1322.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___68_1322.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___68_1322.FStar_Tactics_Types.guard_policy)
            }))
  
let (replace_cur : FStar_Tactics_Types.goal -> Prims.unit tac) =
  fun g  -> bind dismiss (fun uu____1331  -> add_goals [g]) 
let (add_implicits : implicits -> Prims.unit tac) =
  fun i  ->
    bind get
      (fun p  ->
         set
           (let uu___69_1343 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___69_1343.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___69_1343.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (FStar_List.append i p.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___69_1343.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (uu___69_1343.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___69_1343.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___69_1343.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___69_1343.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___69_1343.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___69_1343.FStar_Tactics_Types.guard_policy)
            }))
  
let (new_uvar :
  Prims.string ->
    env -> FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.term tac)
  =
  fun reason  ->
    fun env  ->
      fun typ  ->
        let uu____1369 =
          FStar_TypeChecker_Util.new_implicit_var reason
            typ.FStar_Syntax_Syntax.pos env typ
           in
        match uu____1369 with
        | (u,uu____1385,g_u) ->
            let uu____1399 =
              add_implicits g_u.FStar_TypeChecker_Env.implicits  in
            bind uu____1399 (fun uu____1403  -> ret u)
  
let (is_true : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____1407 = FStar_Syntax_Util.un_squash t  in
    match uu____1407 with
    | FStar_Pervasives_Native.Some t' ->
        let uu____1417 =
          let uu____1418 = FStar_Syntax_Subst.compress t'  in
          uu____1418.FStar_Syntax_Syntax.n  in
        (match uu____1417 with
         | FStar_Syntax_Syntax.Tm_fvar fv ->
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.true_lid
         | uu____1422 -> false)
    | uu____1423 -> false
  
let (is_false : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____1431 = FStar_Syntax_Util.un_squash t  in
    match uu____1431 with
    | FStar_Pervasives_Native.Some t' ->
        let uu____1441 =
          let uu____1442 = FStar_Syntax_Subst.compress t'  in
          uu____1442.FStar_Syntax_Syntax.n  in
        (match uu____1441 with
         | FStar_Syntax_Syntax.Tm_fvar fv ->
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.false_lid
         | uu____1446 -> false)
    | uu____1447 -> false
  
let (cur_goal : FStar_Tactics_Types.goal tac) =
  bind get
    (fun p  ->
       match p.FStar_Tactics_Types.goals with
       | [] -> fail "No more goals (1)"
       | hd1::tl1 -> ret hd1)
  
let (is_guard : Prims.bool tac) =
  bind cur_goal (fun g  -> ret g.FStar_Tactics_Types.is_guard) 
let (mk_irrelevant_goal :
  Prims.string ->
    env ->
      FStar_Syntax_Syntax.typ ->
        FStar_Options.optionstate -> FStar_Tactics_Types.goal tac)
  =
  fun reason  ->
    fun env  ->
      fun phi  ->
        fun opts  ->
          let typ =
            let uu____1487 = env.FStar_TypeChecker_Env.universe_of env phi
               in
            FStar_Syntax_Util.mk_squash uu____1487 phi  in
          let uu____1488 = new_uvar reason env typ  in
          bind uu____1488
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
      (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.typ,FStar_TypeChecker_Env.guard_t)
        FStar_Pervasives_Native.tuple3 tac)
  =
  fun e  ->
    fun t  ->
      bind get
        (fun ps  ->
           try
             let uu____1544 =
               (ps.FStar_Tactics_Types.main_context).FStar_TypeChecker_Env.type_of
                 e t
                in
             ret uu____1544
           with
           | FStar_Errors.Err (uu____1571,msg) ->
               let uu____1573 = tts e t  in
               let uu____1574 =
                 let uu____1575 = FStar_TypeChecker_Env.all_binders e  in
                 FStar_All.pipe_right uu____1575
                   (FStar_Syntax_Print.binders_to_string ", ")
                  in
               fail3 "Cannot type %s in context (%s). Error = (%s)"
                 uu____1573 uu____1574 msg
           | FStar_Errors.Error (uu____1582,msg,uu____1584) ->
               let uu____1585 = tts e t  in
               let uu____1586 =
                 let uu____1587 = FStar_TypeChecker_Env.all_binders e  in
                 FStar_All.pipe_right uu____1587
                   (FStar_Syntax_Print.binders_to_string ", ")
                  in
               fail3 "Cannot type %s in context (%s). Error = (%s)"
                 uu____1585 uu____1586 msg)
  
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
  
let (get_guard_policy : FStar_Tactics_Types.guard_policy tac) =
  bind get (fun ps  -> ret ps.FStar_Tactics_Types.guard_policy) 
let (set_guard_policy : FStar_Tactics_Types.guard_policy -> Prims.unit tac) =
  fun pol  ->
    bind get
      (fun ps  ->
         set
           (let uu___72_1621 = ps  in
            {
              FStar_Tactics_Types.main_context =
                (uu___72_1621.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___72_1621.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___72_1621.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___72_1621.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (uu___72_1621.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___72_1621.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___72_1621.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___72_1621.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___72_1621.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy = pol
            }))
  
let with_policy : 'a . FStar_Tactics_Types.guard_policy -> 'a tac -> 'a tac =
  fun pol  ->
    fun t  ->
      bind get_guard_policy
        (fun old_pol  ->
           let uu____1643 = set_guard_policy pol  in
           bind uu____1643
             (fun uu____1647  ->
                bind t
                  (fun r  ->
                     let uu____1651 = set_guard_policy old_pol  in
                     bind uu____1651 (fun uu____1655  -> ret r))))
  
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
          let uu____1672 =
            let uu____1673 = FStar_TypeChecker_Rel.simplify_guard e g  in
            uu____1673.FStar_TypeChecker_Env.guard_f  in
          match uu____1672 with
          | FStar_TypeChecker_Common.Trivial  -> ret ()
          | FStar_TypeChecker_Common.NonTrivial f ->
              let uu____1677 = istrivial e f  in
              if uu____1677
              then ret ()
              else
                bind get
                  (fun ps  ->
                     match ps.FStar_Tactics_Types.guard_policy with
                     | FStar_Tactics_Types.Drop  -> ret ()
                     | FStar_Tactics_Types.Goal  ->
                         let uu____1685 = mk_irrelevant_goal reason e f opts
                            in
                         bind uu____1685
                           (fun goal  ->
                              let goal1 =
                                let uu___73_1692 = goal  in
                                {
                                  FStar_Tactics_Types.context =
                                    (uu___73_1692.FStar_Tactics_Types.context);
                                  FStar_Tactics_Types.witness =
                                    (uu___73_1692.FStar_Tactics_Types.witness);
                                  FStar_Tactics_Types.goal_ty =
                                    (uu___73_1692.FStar_Tactics_Types.goal_ty);
                                  FStar_Tactics_Types.opts =
                                    (uu___73_1692.FStar_Tactics_Types.opts);
                                  FStar_Tactics_Types.is_guard = true
                                }  in
                              push_goals [goal1])
                     | FStar_Tactics_Types.SMT  ->
                         let uu____1693 = mk_irrelevant_goal reason e f opts
                            in
                         bind uu____1693
                           (fun goal  ->
                              let goal1 =
                                let uu___74_1700 = goal  in
                                {
                                  FStar_Tactics_Types.context =
                                    (uu___74_1700.FStar_Tactics_Types.context);
                                  FStar_Tactics_Types.witness =
                                    (uu___74_1700.FStar_Tactics_Types.witness);
                                  FStar_Tactics_Types.goal_ty =
                                    (uu___74_1700.FStar_Tactics_Types.goal_ty);
                                  FStar_Tactics_Types.opts =
                                    (uu___74_1700.FStar_Tactics_Types.opts);
                                  FStar_Tactics_Types.is_guard = true
                                }  in
                              push_smt_goals [goal1])
                     | FStar_Tactics_Types.Force  ->
                         (try
                            let uu____1708 =
                              let uu____1709 =
                                let uu____1710 =
                                  FStar_TypeChecker_Rel.discharge_guard_no_smt
                                    e g
                                   in
                                FStar_All.pipe_left
                                  FStar_TypeChecker_Rel.is_trivial uu____1710
                                 in
                              Prims.op_Negation uu____1709  in
                            if uu____1708
                            then
                              mlog
                                (fun uu____1715  ->
                                   let uu____1716 =
                                     FStar_TypeChecker_Rel.guard_to_string e
                                       g
                                      in
                                   FStar_Util.print1 "guard = %s\n"
                                     uu____1716)
                                (fun uu____1718  ->
                                   fail1 "Forcing the guard failed %s)"
                                     reason)
                            else ret ()
                          with
                          | uu____1725 ->
                              mlog
                                (fun uu____1728  ->
                                   let uu____1729 =
                                     FStar_TypeChecker_Rel.guard_to_string e
                                       g
                                      in
                                   FStar_Util.print1 "guard = %s\n"
                                     uu____1729)
                                (fun uu____1731  ->
                                   fail1 "Forcing the guard failed (%s)"
                                     reason)))
  
let (tc : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.typ tac) =
  fun t  ->
    let uu____1739 =
      bind cur_goal
        (fun goal  ->
           let uu____1745 = __tc goal.FStar_Tactics_Types.context t  in
           bind uu____1745
             (fun uu____1765  ->
                match uu____1765 with
                | (t1,typ,guard) ->
                    let uu____1777 =
                      proc_guard "tc" goal.FStar_Tactics_Types.context guard
                        goal.FStar_Tactics_Types.opts
                       in
                    bind uu____1777 (fun uu____1781  -> ret typ)))
       in
    FStar_All.pipe_left (wrap_err "tc") uu____1739
  
let (add_irrelevant_goal :
  Prims.string ->
    env ->
      FStar_Syntax_Syntax.typ -> FStar_Options.optionstate -> Prims.unit tac)
  =
  fun reason  ->
    fun env  ->
      fun phi  ->
        fun opts  ->
          let uu____1802 = mk_irrelevant_goal reason env phi opts  in
          bind uu____1802 (fun goal  -> add_goals [goal])
  
let (trivial : Prims.unit tac) =
  bind cur_goal
    (fun goal  ->
       let uu____1814 =
         istrivial goal.FStar_Tactics_Types.context
           goal.FStar_Tactics_Types.goal_ty
          in
       if uu____1814
       then solve goal FStar_Syntax_Util.exp_unit
       else
         (let uu____1818 =
            tts goal.FStar_Tactics_Types.context
              goal.FStar_Tactics_Types.goal_ty
             in
          fail1 "Not a trivial goal: %s" uu____1818))
  
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
          let uu____1839 =
            let uu____1840 = FStar_TypeChecker_Rel.simplify_guard e g  in
            uu____1840.FStar_TypeChecker_Env.guard_f  in
          match uu____1839 with
          | FStar_TypeChecker_Common.Trivial  ->
              ret FStar_Pervasives_Native.None
          | FStar_TypeChecker_Common.NonTrivial f ->
              let uu____1848 = istrivial e f  in
              if uu____1848
              then ret FStar_Pervasives_Native.None
              else
                (let uu____1856 = mk_irrelevant_goal reason e f opts  in
                 bind uu____1856
                   (fun goal  ->
                      ret
                        (FStar_Pervasives_Native.Some
                           (let uu___77_1866 = goal  in
                            {
                              FStar_Tactics_Types.context =
                                (uu___77_1866.FStar_Tactics_Types.context);
                              FStar_Tactics_Types.witness =
                                (uu___77_1866.FStar_Tactics_Types.witness);
                              FStar_Tactics_Types.goal_ty =
                                (uu___77_1866.FStar_Tactics_Types.goal_ty);
                              FStar_Tactics_Types.opts =
                                (uu___77_1866.FStar_Tactics_Types.opts);
                              FStar_Tactics_Types.is_guard = true
                            }))))
  
let (smt : Prims.unit tac) =
  bind cur_goal
    (fun g  ->
       let uu____1874 = is_irrelevant g  in
       if uu____1874
       then bind dismiss (fun uu____1878  -> add_smt_goals [g])
       else
         (let uu____1880 =
            tts g.FStar_Tactics_Types.context g.FStar_Tactics_Types.goal_ty
             in
          fail1 "goal is not irrelevant: cannot dispatch to smt (%s)"
            uu____1880))
  
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
             let uu____1921 =
               try
                 let uu____1955 =
                   let uu____1964 = FStar_BigInt.to_int_fs n1  in
                   FStar_List.splitAt uu____1964 p.FStar_Tactics_Types.goals
                    in
                 ret uu____1955
               with | uu____1986 -> fail "divide: not enough goals"  in
             bind uu____1921
               (fun uu____2013  ->
                  match uu____2013 with
                  | (lgs,rgs) ->
                      let lp =
                        let uu___78_2039 = p  in
                        {
                          FStar_Tactics_Types.main_context =
                            (uu___78_2039.FStar_Tactics_Types.main_context);
                          FStar_Tactics_Types.main_goal =
                            (uu___78_2039.FStar_Tactics_Types.main_goal);
                          FStar_Tactics_Types.all_implicits =
                            (uu___78_2039.FStar_Tactics_Types.all_implicits);
                          FStar_Tactics_Types.goals = lgs;
                          FStar_Tactics_Types.smt_goals = [];
                          FStar_Tactics_Types.depth =
                            (uu___78_2039.FStar_Tactics_Types.depth);
                          FStar_Tactics_Types.__dump =
                            (uu___78_2039.FStar_Tactics_Types.__dump);
                          FStar_Tactics_Types.psc =
                            (uu___78_2039.FStar_Tactics_Types.psc);
                          FStar_Tactics_Types.entry_range =
                            (uu___78_2039.FStar_Tactics_Types.entry_range);
                          FStar_Tactics_Types.guard_policy =
                            (uu___78_2039.FStar_Tactics_Types.guard_policy)
                        }  in
                      let rp =
                        let uu___79_2041 = p  in
                        {
                          FStar_Tactics_Types.main_context =
                            (uu___79_2041.FStar_Tactics_Types.main_context);
                          FStar_Tactics_Types.main_goal =
                            (uu___79_2041.FStar_Tactics_Types.main_goal);
                          FStar_Tactics_Types.all_implicits =
                            (uu___79_2041.FStar_Tactics_Types.all_implicits);
                          FStar_Tactics_Types.goals = rgs;
                          FStar_Tactics_Types.smt_goals = [];
                          FStar_Tactics_Types.depth =
                            (uu___79_2041.FStar_Tactics_Types.depth);
                          FStar_Tactics_Types.__dump =
                            (uu___79_2041.FStar_Tactics_Types.__dump);
                          FStar_Tactics_Types.psc =
                            (uu___79_2041.FStar_Tactics_Types.psc);
                          FStar_Tactics_Types.entry_range =
                            (uu___79_2041.FStar_Tactics_Types.entry_range);
                          FStar_Tactics_Types.guard_policy =
                            (uu___79_2041.FStar_Tactics_Types.guard_policy)
                        }  in
                      let uu____2042 = set lp  in
                      bind uu____2042
                        (fun uu____2050  ->
                           bind l
                             (fun a  ->
                                bind get
                                  (fun lp'  ->
                                     let uu____2064 = set rp  in
                                     bind uu____2064
                                       (fun uu____2072  ->
                                          bind r
                                            (fun b  ->
                                               bind get
                                                 (fun rp'  ->
                                                    let p' =
                                                      let uu___80_2088 = p
                                                         in
                                                      {
                                                        FStar_Tactics_Types.main_context
                                                          =
                                                          (uu___80_2088.FStar_Tactics_Types.main_context);
                                                        FStar_Tactics_Types.main_goal
                                                          =
                                                          (uu___80_2088.FStar_Tactics_Types.main_goal);
                                                        FStar_Tactics_Types.all_implicits
                                                          =
                                                          (uu___80_2088.FStar_Tactics_Types.all_implicits);
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
                                                          (uu___80_2088.FStar_Tactics_Types.depth);
                                                        FStar_Tactics_Types.__dump
                                                          =
                                                          (uu___80_2088.FStar_Tactics_Types.__dump);
                                                        FStar_Tactics_Types.psc
                                                          =
                                                          (uu___80_2088.FStar_Tactics_Types.psc);
                                                        FStar_Tactics_Types.entry_range
                                                          =
                                                          (uu___80_2088.FStar_Tactics_Types.entry_range);
                                                        FStar_Tactics_Types.guard_policy
                                                          =
                                                          (uu___80_2088.FStar_Tactics_Types.guard_policy)
                                                      }  in
                                                    let uu____2089 = set p'
                                                       in
                                                    bind uu____2089
                                                      (fun uu____2097  ->
                                                         ret (a, b))))))))))
  
let focus : 'a . 'a tac -> 'a tac =
  fun f  ->
    let uu____2115 = divide FStar_BigInt.one f idtac  in
    bind uu____2115
      (fun uu____2128  -> match uu____2128 with | (a,()) -> ret a)
  
let rec map : 'a . 'a tac -> 'a Prims.list tac =
  fun tau  ->
    bind get
      (fun p  ->
         match p.FStar_Tactics_Types.goals with
         | [] -> ret []
         | uu____2162::uu____2163 ->
             let uu____2166 =
               let uu____2175 = map tau  in
               divide FStar_BigInt.one tau uu____2175  in
             bind uu____2166
               (fun uu____2193  ->
                  match uu____2193 with | (h,t) -> ret (h :: t)))
  
let (seq : Prims.unit tac -> Prims.unit tac -> Prims.unit tac) =
  fun t1  ->
    fun t2  ->
      let uu____2230 =
        bind t1
          (fun uu____2235  ->
             let uu____2236 = map t2  in
             bind uu____2236 (fun uu____2244  -> ret ()))
         in
      focus uu____2230
  
let (intro : FStar_Syntax_Syntax.binder tac) =
  let uu____2251 =
    bind cur_goal
      (fun goal  ->
         let uu____2260 =
           FStar_Syntax_Util.arrow_one goal.FStar_Tactics_Types.goal_ty  in
         match uu____2260 with
         | FStar_Pervasives_Native.Some (b,c) ->
             let uu____2275 =
               let uu____2276 = FStar_Syntax_Util.is_total_comp c  in
               Prims.op_Negation uu____2276  in
             if uu____2275
             then fail "Codomain is effectful"
             else
               (let env' =
                  FStar_TypeChecker_Env.push_binders
                    goal.FStar_Tactics_Types.context [b]
                   in
                let typ' = comp_to_typ c  in
                let uu____2282 = new_uvar "intro" env' typ'  in
                bind uu____2282
                  (fun u  ->
                     let uu____2288 =
                       let uu____2291 =
                         FStar_Syntax_Util.abs [b] u
                           FStar_Pervasives_Native.None
                          in
                       trysolve goal uu____2291  in
                     bind uu____2288
                       (fun bb  ->
                          if bb
                          then
                            let uu____2297 =
                              let uu____2300 =
                                let uu___83_2301 = goal  in
                                let uu____2302 = bnorm env' u  in
                                let uu____2303 = bnorm env' typ'  in
                                {
                                  FStar_Tactics_Types.context = env';
                                  FStar_Tactics_Types.witness = uu____2302;
                                  FStar_Tactics_Types.goal_ty = uu____2303;
                                  FStar_Tactics_Types.opts =
                                    (uu___83_2301.FStar_Tactics_Types.opts);
                                  FStar_Tactics_Types.is_guard =
                                    (uu___83_2301.FStar_Tactics_Types.is_guard)
                                }  in
                              replace_cur uu____2300  in
                            bind uu____2297 (fun uu____2305  -> ret b)
                          else fail "unification failed")))
         | FStar_Pervasives_Native.None  ->
             let uu____2311 =
               tts goal.FStar_Tactics_Types.context
                 goal.FStar_Tactics_Types.goal_ty
                in
             fail1 "goal is not an arrow (%s)" uu____2311)
     in
  FStar_All.pipe_left (wrap_err "intro") uu____2251 
let (intro_rec :
  (FStar_Syntax_Syntax.binder,FStar_Syntax_Syntax.binder)
    FStar_Pervasives_Native.tuple2 tac)
  =
  bind cur_goal
    (fun goal  ->
       FStar_Util.print_string
         "WARNING (intro_rec): calling this is known to cause normalizer loops\n";
       FStar_Util.print_string
         "WARNING (intro_rec): proceed at your own risk...\n";
       (let uu____2342 =
          FStar_Syntax_Util.arrow_one goal.FStar_Tactics_Types.goal_ty  in
        match uu____2342 with
        | FStar_Pervasives_Native.Some (b,c) ->
            let uu____2361 =
              let uu____2362 = FStar_Syntax_Util.is_total_comp c  in
              Prims.op_Negation uu____2362  in
            if uu____2361
            then fail "Codomain is effectful"
            else
              (let bv =
                 FStar_Syntax_Syntax.gen_bv "__recf"
                   FStar_Pervasives_Native.None
                   goal.FStar_Tactics_Types.goal_ty
                  in
               let bs =
                 let uu____2378 = FStar_Syntax_Syntax.mk_binder bv  in
                 [uu____2378; b]  in
               let env' =
                 FStar_TypeChecker_Env.push_binders
                   goal.FStar_Tactics_Types.context bs
                  in
               let uu____2380 =
                 let uu____2383 = comp_to_typ c  in
                 new_uvar "intro_rec" env' uu____2383  in
               bind uu____2380
                 (fun u  ->
                    let lb =
                      let uu____2398 =
                        FStar_Syntax_Util.abs [b] u
                          FStar_Pervasives_Native.None
                         in
                      FStar_Syntax_Util.mk_letbinding (FStar_Util.Inl bv) []
                        goal.FStar_Tactics_Types.goal_ty
                        FStar_Parser_Const.effect_Tot_lid uu____2398 []
                        FStar_Range.dummyRange
                       in
                    let body = FStar_Syntax_Syntax.bv_to_name bv  in
                    let uu____2404 =
                      FStar_Syntax_Subst.close_let_rec [lb] body  in
                    match uu____2404 with
                    | (lbs,body1) ->
                        let tm =
                          FStar_Syntax_Syntax.mk
                            (FStar_Syntax_Syntax.Tm_let ((true, lbs), body1))
                            FStar_Pervasives_Native.None
                            (goal.FStar_Tactics_Types.witness).FStar_Syntax_Syntax.pos
                           in
                        let uu____2434 = trysolve goal tm  in
                        bind uu____2434
                          (fun bb  ->
                             if bb
                             then
                               let uu____2450 =
                                 let uu____2453 =
                                   let uu___84_2454 = goal  in
                                   let uu____2455 = bnorm env' u  in
                                   let uu____2456 =
                                     let uu____2457 = comp_to_typ c  in
                                     bnorm env' uu____2457  in
                                   {
                                     FStar_Tactics_Types.context = env';
                                     FStar_Tactics_Types.witness = uu____2455;
                                     FStar_Tactics_Types.goal_ty = uu____2456;
                                     FStar_Tactics_Types.opts =
                                       (uu___84_2454.FStar_Tactics_Types.opts);
                                     FStar_Tactics_Types.is_guard =
                                       (uu___84_2454.FStar_Tactics_Types.is_guard)
                                   }  in
                                 replace_cur uu____2453  in
                               bind uu____2450
                                 (fun uu____2464  ->
                                    let uu____2465 =
                                      let uu____2470 =
                                        FStar_Syntax_Syntax.mk_binder bv  in
                                      (uu____2470, b)  in
                                    ret uu____2465)
                             else fail "intro_rec: unification failed")))
        | FStar_Pervasives_Native.None  ->
            let uu____2484 =
              tts goal.FStar_Tactics_Types.context
                goal.FStar_Tactics_Types.goal_ty
               in
            fail1 "intro_rec: goal is not an arrow (%s)" uu____2484))
  
let (norm : FStar_Syntax_Embeddings.norm_step Prims.list -> Prims.unit tac) =
  fun s  ->
    bind cur_goal
      (fun goal  ->
         mlog
           (fun uu____2504  ->
              let uu____2505 =
                FStar_Syntax_Print.term_to_string
                  goal.FStar_Tactics_Types.witness
                 in
              FStar_Util.print1 "norm: witness = %s\n" uu____2505)
           (fun uu____2510  ->
              let steps =
                let uu____2514 = FStar_TypeChecker_Normalize.tr_norm_steps s
                   in
                FStar_List.append
                  [FStar_TypeChecker_Normalize.Reify;
                  FStar_TypeChecker_Normalize.UnfoldTac] uu____2514
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
                (let uu___85_2521 = goal  in
                 {
                   FStar_Tactics_Types.context =
                     (uu___85_2521.FStar_Tactics_Types.context);
                   FStar_Tactics_Types.witness = w;
                   FStar_Tactics_Types.goal_ty = t;
                   FStar_Tactics_Types.opts =
                     (uu___85_2521.FStar_Tactics_Types.opts);
                   FStar_Tactics_Types.is_guard =
                     (uu___85_2521.FStar_Tactics_Types.is_guard)
                 })))
  
let (norm_term_env :
  env ->
    FStar_Syntax_Embeddings.norm_step Prims.list ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term tac)
  =
  fun e  ->
    fun s  ->
      fun t  ->
        let uu____2539 =
          mlog
            (fun uu____2544  ->
               let uu____2545 = FStar_Syntax_Print.term_to_string t  in
               FStar_Util.print1 "norm_term: tm = %s\n" uu____2545)
            (fun uu____2547  ->
               bind get
                 (fun ps  ->
                    let opts =
                      match ps.FStar_Tactics_Types.goals with
                      | g::uu____2553 -> g.FStar_Tactics_Types.opts
                      | uu____2556 -> FStar_Options.peek ()  in
                    mlog
                      (fun uu____2561  ->
                         let uu____2562 =
                           tts ps.FStar_Tactics_Types.main_context t  in
                         FStar_Util.print1 "norm_term_env: t = %s\n"
                           uu____2562)
                      (fun uu____2565  ->
                         let uu____2566 = __tc e t  in
                         bind uu____2566
                           (fun uu____2587  ->
                              match uu____2587 with
                              | (t1,uu____2597,uu____2598) ->
                                  let steps =
                                    let uu____2602 =
                                      FStar_TypeChecker_Normalize.tr_norm_steps
                                        s
                                       in
                                    FStar_List.append
                                      [FStar_TypeChecker_Normalize.Reify;
                                      FStar_TypeChecker_Normalize.UnfoldTac]
                                      uu____2602
                                     in
                                  let t2 =
                                    normalize steps
                                      ps.FStar_Tactics_Types.main_context t1
                                     in
                                  ret t2))))
           in
        FStar_All.pipe_left (wrap_err "norm_term") uu____2539
  
let (refine_intro : Prims.unit tac) =
  let uu____2614 =
    bind cur_goal
      (fun g  ->
         let uu____2621 =
           FStar_TypeChecker_Rel.base_and_refinement
             g.FStar_Tactics_Types.context g.FStar_Tactics_Types.goal_ty
            in
         match uu____2621 with
         | (uu____2634,FStar_Pervasives_Native.None ) ->
             fail "not a refinement"
         | (t,FStar_Pervasives_Native.Some (bv,phi)) ->
             let g1 =
               let uu___86_2659 = g  in
               {
                 FStar_Tactics_Types.context =
                   (uu___86_2659.FStar_Tactics_Types.context);
                 FStar_Tactics_Types.witness =
                   (uu___86_2659.FStar_Tactics_Types.witness);
                 FStar_Tactics_Types.goal_ty = t;
                 FStar_Tactics_Types.opts =
                   (uu___86_2659.FStar_Tactics_Types.opts);
                 FStar_Tactics_Types.is_guard =
                   (uu___86_2659.FStar_Tactics_Types.is_guard)
               }  in
             let uu____2660 =
               let uu____2665 =
                 let uu____2670 =
                   let uu____2671 = FStar_Syntax_Syntax.mk_binder bv  in
                   [uu____2671]  in
                 FStar_Syntax_Subst.open_term uu____2670 phi  in
               match uu____2665 with
               | (bvs,phi1) ->
                   let uu____2678 =
                     let uu____2679 = FStar_List.hd bvs  in
                     FStar_Pervasives_Native.fst uu____2679  in
                   (uu____2678, phi1)
                in
             (match uu____2660 with
              | (bv1,phi1) ->
                  let uu____2692 =
                    let uu____2695 =
                      FStar_Syntax_Subst.subst
                        [FStar_Syntax_Syntax.NT
                           (bv1, (g.FStar_Tactics_Types.witness))] phi1
                       in
                    mk_irrelevant_goal "refine_intro refinement"
                      g.FStar_Tactics_Types.context uu____2695
                      g.FStar_Tactics_Types.opts
                     in
                  bind uu____2692
                    (fun g2  ->
                       bind dismiss (fun uu____2699  -> add_goals [g1; g2]))))
     in
  FStar_All.pipe_left (wrap_err "refine_intro") uu____2614 
let (__exact_now : Prims.bool -> FStar_Syntax_Syntax.term -> Prims.unit tac)
  =
  fun set_expected_typ1  ->
    fun t  ->
      bind cur_goal
        (fun goal  ->
           let env =
             if set_expected_typ1
             then
               FStar_TypeChecker_Env.set_expected_typ
                 goal.FStar_Tactics_Types.context
                 goal.FStar_Tactics_Types.goal_ty
             else goal.FStar_Tactics_Types.context  in
           let uu____2720 = __tc env t  in
           bind uu____2720
             (fun uu____2740  ->
                match uu____2740 with
                | (t1,typ,guard) ->
                    let uu____2752 =
                      proc_guard "__exact typing"
                        goal.FStar_Tactics_Types.context guard
                        goal.FStar_Tactics_Types.opts
                       in
                    bind uu____2752
                      (fun uu____2756  ->
                         mlog
                           (fun uu____2760  ->
                              let uu____2761 =
                                tts goal.FStar_Tactics_Types.context typ  in
                              let uu____2762 =
                                tts goal.FStar_Tactics_Types.context
                                  goal.FStar_Tactics_Types.goal_ty
                                 in
                              FStar_Util.print2 "exact: unifying %s and %s\n"
                                uu____2761 uu____2762)
                           (fun uu____2765  ->
                              let uu____2766 =
                                do_unify goal.FStar_Tactics_Types.context typ
                                  goal.FStar_Tactics_Types.goal_ty
                                 in
                              bind uu____2766
                                (fun b  ->
                                   if b
                                   then solve goal t1
                                   else
                                     (let uu____2774 =
                                        tts goal.FStar_Tactics_Types.context
                                          t1
                                         in
                                      let uu____2775 =
                                        tts goal.FStar_Tactics_Types.context
                                          typ
                                         in
                                      let uu____2776 =
                                        tts goal.FStar_Tactics_Types.context
                                          goal.FStar_Tactics_Types.goal_ty
                                         in
                                      let uu____2777 =
                                        tts goal.FStar_Tactics_Types.context
                                          goal.FStar_Tactics_Types.witness
                                         in
                                      fail4
                                        "%s : %s does not exactly solve the goal %s (witness = %s)"
                                        uu____2774 uu____2775 uu____2776
                                        uu____2777))))))
  
let (t_exact : Prims.bool -> FStar_Syntax_Syntax.term -> Prims.unit tac) =
  fun set_expected_typ1  ->
    fun tm  ->
      let uu____2788 =
        mlog
          (fun uu____2793  ->
             let uu____2794 = FStar_Syntax_Print.term_to_string tm  in
             FStar_Util.print1 "t_exact: tm = %s\n" uu____2794)
          (fun uu____2797  ->
             let uu____2798 =
               let uu____2805 = __exact_now set_expected_typ1 tm  in
               trytac' uu____2805  in
             bind uu____2798
               (fun uu___56_2814  ->
                  match uu___56_2814 with
                  | FStar_Util.Inr r -> ret ()
                  | FStar_Util.Inl e ->
                      let uu____2823 =
                        let uu____2830 =
                          let uu____2833 =
                            norm [FStar_Syntax_Embeddings.Delta]  in
                          bind uu____2833
                            (fun uu____2837  ->
                               bind refine_intro
                                 (fun uu____2839  ->
                                    __exact_now set_expected_typ1 tm))
                           in
                        trytac' uu____2830  in
                      bind uu____2823
                        (fun uu___55_2846  ->
                           match uu___55_2846 with
                           | FStar_Util.Inr r -> ret ()
                           | FStar_Util.Inl uu____2854 -> fail e)))
         in
      FStar_All.pipe_left (wrap_err "exact") uu____2788
  
let (uvar_free_in_goal :
  FStar_Syntax_Syntax.uvar -> FStar_Tactics_Types.goal -> Prims.bool) =
  fun u  ->
    fun g  ->
      if g.FStar_Tactics_Types.is_guard
      then false
      else
        (let free_uvars =
           let uu____2869 =
             let uu____2876 =
               FStar_Syntax_Free.uvars g.FStar_Tactics_Types.goal_ty  in
             FStar_Util.set_elements uu____2876  in
           FStar_List.map FStar_Pervasives_Native.fst uu____2869  in
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
          let uu____2936 = f x  in
          bind uu____2936
            (fun y  ->
               let uu____2944 = mapM f xs  in
               bind uu____2944 (fun ys  -> ret (y :: ys)))
  
exception NoUnif 
let (uu___is_NoUnif : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with | NoUnif  -> true | uu____2962 -> false
  
let rec (__apply :
  Prims.bool ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.typ -> Prims.unit tac)
  =
  fun uopt  ->
    fun tm  ->
      fun typ  ->
        bind cur_goal
          (fun goal  ->
             mlog
               (fun uu____2980  ->
                  let uu____2981 = FStar_Syntax_Print.term_to_string tm  in
                  FStar_Util.print1 ">>> Calling __exact(%s)\n" uu____2981)
               (fun uu____2984  ->
                  let uu____2985 =
                    let uu____2990 =
                      let uu____2993 = t_exact false tm  in
                      with_policy FStar_Tactics_Types.Force uu____2993  in
                    trytac_exn uu____2990  in
                  bind uu____2985
                    (fun uu___57_3000  ->
                       match uu___57_3000 with
                       | FStar_Pervasives_Native.Some r -> ret ()
                       | FStar_Pervasives_Native.None  ->
                           mlog
                             (fun uu____3008  ->
                                let uu____3009 =
                                  FStar_Syntax_Print.term_to_string typ  in
                                FStar_Util.print1 ">>> typ = %s\n" uu____3009)
                             (fun uu____3012  ->
                                let uu____3013 =
                                  FStar_Syntax_Util.arrow_one typ  in
                                match uu____3013 with
                                | FStar_Pervasives_Native.None  ->
                                    FStar_Exn.raise NoUnif
                                | FStar_Pervasives_Native.Some ((bv,aq),c) ->
                                    mlog
                                      (fun uu____3045  ->
                                         let uu____3046 =
                                           FStar_Syntax_Print.binder_to_string
                                             (bv, aq)
                                            in
                                         FStar_Util.print1
                                           "__apply: pushing binder %s\n"
                                           uu____3046)
                                      (fun uu____3049  ->
                                         let uu____3050 =
                                           let uu____3051 =
                                             FStar_Syntax_Util.is_total_comp
                                               c
                                              in
                                           Prims.op_Negation uu____3051  in
                                         if uu____3050
                                         then
                                           fail "apply: not total codomain"
                                         else
                                           (let uu____3055 =
                                              new_uvar "apply"
                                                goal.FStar_Tactics_Types.context
                                                bv.FStar_Syntax_Syntax.sort
                                               in
                                            bind uu____3055
                                              (fun u  ->
                                                 let tm' =
                                                   FStar_Syntax_Syntax.mk_Tm_app
                                                     tm [(u, aq)]
                                                     FStar_Pervasives_Native.None
                                                     tm.FStar_Syntax_Syntax.pos
                                                    in
                                                 let typ' =
                                                   let uu____3075 =
                                                     comp_to_typ c  in
                                                   FStar_All.pipe_left
                                                     (FStar_Syntax_Subst.subst
                                                        [FStar_Syntax_Syntax.NT
                                                           (bv, u)])
                                                     uu____3075
                                                    in
                                                 let uu____3076 =
                                                   __apply uopt tm' typ'  in
                                                 bind uu____3076
                                                   (fun uu____3084  ->
                                                      let u1 =
                                                        bnorm
                                                          goal.FStar_Tactics_Types.context
                                                          u
                                                         in
                                                      let uu____3086 =
                                                        let uu____3087 =
                                                          let uu____3090 =
                                                            let uu____3091 =
                                                              FStar_Syntax_Util.head_and_args
                                                                u1
                                                               in
                                                            FStar_Pervasives_Native.fst
                                                              uu____3091
                                                             in
                                                          FStar_Syntax_Subst.compress
                                                            uu____3090
                                                           in
                                                        uu____3087.FStar_Syntax_Syntax.n
                                                         in
                                                      match uu____3086 with
                                                      | FStar_Syntax_Syntax.Tm_uvar
                                                          (uvar,uu____3119)
                                                          ->
                                                          bind get
                                                            (fun ps  ->
                                                               let uu____3147
                                                                 =
                                                                 uopt &&
                                                                   (uvar_free
                                                                    uvar ps)
                                                                  in
                                                               if uu____3147
                                                               then ret ()
                                                               else
                                                                 (let uu____3151
                                                                    =
                                                                    let uu____3154
                                                                    =
                                                                    let uu___87_3155
                                                                    = goal
                                                                     in
                                                                    let uu____3156
                                                                    =
                                                                    bnorm
                                                                    goal.FStar_Tactics_Types.context
                                                                    u1  in
                                                                    let uu____3157
                                                                    =
                                                                    bnorm
                                                                    goal.FStar_Tactics_Types.context
                                                                    bv.FStar_Syntax_Syntax.sort
                                                                     in
                                                                    {
                                                                    FStar_Tactics_Types.context
                                                                    =
                                                                    (uu___87_3155.FStar_Tactics_Types.context);
                                                                    FStar_Tactics_Types.witness
                                                                    =
                                                                    uu____3156;
                                                                    FStar_Tactics_Types.goal_ty
                                                                    =
                                                                    uu____3157;
                                                                    FStar_Tactics_Types.opts
                                                                    =
                                                                    (uu___87_3155.FStar_Tactics_Types.opts);
                                                                    FStar_Tactics_Types.is_guard
                                                                    = false
                                                                    }  in
                                                                    [uu____3154]
                                                                     in
                                                                  add_goals
                                                                    uu____3151))
                                                      | t -> ret ()))))))))
  
let try_unif : 'a . 'a tac -> 'a tac -> 'a tac =
  fun t  ->
    fun t'  -> mk_tac (fun ps  -> try run t ps with | NoUnif  -> run t' ps)
  
let (apply : Prims.bool -> FStar_Syntax_Syntax.term -> Prims.unit tac) =
  fun uopt  ->
    fun tm  ->
      let uu____3203 =
        mlog
          (fun uu____3208  ->
             let uu____3209 = FStar_Syntax_Print.term_to_string tm  in
             FStar_Util.print1 "apply: tm = %s\n" uu____3209)
          (fun uu____3211  ->
             bind cur_goal
               (fun goal  ->
                  let uu____3215 = __tc goal.FStar_Tactics_Types.context tm
                     in
                  bind uu____3215
                    (fun uu____3237  ->
                       match uu____3237 with
                       | (tm1,typ,guard) ->
                           let typ1 =
                             bnorm goal.FStar_Tactics_Types.context typ  in
                           let uu____3250 =
                             let uu____3253 =
                               let uu____3256 = __apply uopt tm1 typ1  in
                               bind uu____3256
                                 (fun uu____3260  ->
                                    proc_guard "apply guard"
                                      goal.FStar_Tactics_Types.context guard
                                      goal.FStar_Tactics_Types.opts)
                                in
                             focus uu____3253  in
                           let uu____3261 =
                             let uu____3264 =
                               tts goal.FStar_Tactics_Types.context tm1  in
                             let uu____3265 =
                               tts goal.FStar_Tactics_Types.context typ1  in
                             let uu____3266 =
                               tts goal.FStar_Tactics_Types.context
                                 goal.FStar_Tactics_Types.goal_ty
                                in
                             fail3
                               "Cannot instantiate %s (of type %s) to match goal (%s)"
                               uu____3264 uu____3265 uu____3266
                              in
                           try_unif uu____3250 uu____3261)))
         in
      FStar_All.pipe_left (wrap_err "apply") uu____3203
  
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
      let uu____3293 =
        match ct.FStar_Syntax_Syntax.effect_args with
        | pre::post::uu____3312 ->
            ((FStar_Pervasives_Native.fst pre),
              (FStar_Pervasives_Native.fst post))
        | uu____3353 -> failwith "apply_lemma: impossible: not a lemma"  in
      match uu____3293 with
      | (pre,post) ->
          let post1 =
            let uu____3389 =
              let uu____3398 =
                FStar_Syntax_Syntax.as_arg FStar_Syntax_Util.exp_unit  in
              [uu____3398]  in
            FStar_Syntax_Util.mk_app post uu____3389  in
          FStar_Pervasives_Native.Some (pre, post1)
    else
      if FStar_Syntax_Util.is_pure_effect ct.FStar_Syntax_Syntax.effect_name
      then
        (let uu____3418 =
           FStar_Syntax_Util.un_squash ct.FStar_Syntax_Syntax.result_typ  in
         FStar_Util.map_opt uu____3418
           (fun post  -> (FStar_Syntax_Util.t_true, post)))
      else FStar_Pervasives_Native.None
  
let (apply_lemma : FStar_Syntax_Syntax.term -> Prims.unit tac) =
  fun tm  ->
    let uu____3449 =
      let uu____3452 =
        mlog
          (fun uu____3457  ->
             let uu____3458 = FStar_Syntax_Print.term_to_string tm  in
             FStar_Util.print1 "apply_lemma: tm = %s\n" uu____3458)
          (fun uu____3461  ->
             let is_unit_t t =
               let uu____3466 =
                 let uu____3467 = FStar_Syntax_Subst.compress t  in
                 uu____3467.FStar_Syntax_Syntax.n  in
               match uu____3466 with
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.unit_lid
                   -> true
               | uu____3471 -> false  in
             bind cur_goal
               (fun goal  ->
                  let uu____3475 = __tc goal.FStar_Tactics_Types.context tm
                     in
                  bind uu____3475
                    (fun uu____3498  ->
                       match uu____3498 with
                       | (tm1,t,guard) ->
                           let uu____3510 =
                             FStar_Syntax_Util.arrow_formals_comp t  in
                           (match uu____3510 with
                            | (bs,comp) ->
                                let uu____3537 = lemma_or_sq comp  in
                                (match uu____3537 with
                                 | FStar_Pervasives_Native.None  ->
                                     fail "not a lemma or squashed function"
                                 | FStar_Pervasives_Native.Some (pre,post) ->
                                     let uu____3556 =
                                       FStar_List.fold_left
                                         (fun uu____3602  ->
                                            fun uu____3603  ->
                                              match (uu____3602, uu____3603)
                                              with
                                              | ((uvs,guard1,subst1),(b,aq))
                                                  ->
                                                  let b_t =
                                                    FStar_Syntax_Subst.subst
                                                      subst1
                                                      b.FStar_Syntax_Syntax.sort
                                                     in
                                                  let uu____3706 =
                                                    is_unit_t b_t  in
                                                  if uu____3706
                                                  then
                                                    (((FStar_Syntax_Util.exp_unit,
                                                        aq) :: uvs), guard1,
                                                      ((FStar_Syntax_Syntax.NT
                                                          (b,
                                                            FStar_Syntax_Util.exp_unit))
                                                      :: subst1))
                                                  else
                                                    (let uu____3744 =
                                                       FStar_TypeChecker_Util.new_implicit_var
                                                         "apply_lemma"
                                                         (goal.FStar_Tactics_Types.goal_ty).FStar_Syntax_Syntax.pos
                                                         goal.FStar_Tactics_Types.context
                                                         b_t
                                                        in
                                                     match uu____3744 with
                                                     | (u,uu____3774,g_u) ->
                                                         let uu____3788 =
                                                           FStar_TypeChecker_Rel.conj_guard
                                                             guard1 g_u
                                                            in
                                                         (((u, aq) :: uvs),
                                                           uu____3788,
                                                           ((FStar_Syntax_Syntax.NT
                                                               (b, u)) ::
                                                           subst1))))
                                         ([], guard, []) bs
                                        in
                                     (match uu____3556 with
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
                                          let uu____3859 =
                                            let uu____3862 =
                                              FStar_Syntax_Util.mk_squash
                                                FStar_Syntax_Syntax.U_zero
                                                post1
                                               in
                                            do_unify
                                              goal.FStar_Tactics_Types.context
                                              uu____3862
                                              goal.FStar_Tactics_Types.goal_ty
                                             in
                                          bind uu____3859
                                            (fun b  ->
                                               if Prims.op_Negation b
                                               then
                                                 let uu____3870 =
                                                   tts
                                                     goal.FStar_Tactics_Types.context
                                                     tm1
                                                    in
                                                 let uu____3871 =
                                                   let uu____3872 =
                                                     FStar_Syntax_Util.mk_squash
                                                       FStar_Syntax_Syntax.U_zero
                                                       post1
                                                      in
                                                   tts
                                                     goal.FStar_Tactics_Types.context
                                                     uu____3872
                                                    in
                                                 let uu____3873 =
                                                   tts
                                                     goal.FStar_Tactics_Types.context
                                                     goal.FStar_Tactics_Types.goal_ty
                                                    in
                                                 fail3
                                                   "Cannot instantiate lemma %s (with postcondition: %s) to match goal (%s)"
                                                   uu____3870 uu____3871
                                                   uu____3873
                                               else
                                                 (let uu____3875 =
                                                    add_implicits
                                                      implicits.FStar_TypeChecker_Env.implicits
                                                     in
                                                  bind uu____3875
                                                    (fun uu____3880  ->
                                                       let uu____3881 =
                                                         solve goal
                                                           FStar_Syntax_Util.exp_unit
                                                          in
                                                       bind uu____3881
                                                         (fun uu____3889  ->
                                                            let is_free_uvar
                                                              uv t1 =
                                                              let free_uvars
                                                                =
                                                                let uu____3900
                                                                  =
                                                                  let uu____3907
                                                                    =
                                                                    FStar_Syntax_Free.uvars
                                                                    t1  in
                                                                  FStar_Util.set_elements
                                                                    uu____3907
                                                                   in
                                                                FStar_List.map
                                                                  FStar_Pervasives_Native.fst
                                                                  uu____3900
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
                                                              let uu____3948
                                                                =
                                                                FStar_Syntax_Util.head_and_args
                                                                  t1
                                                                 in
                                                              match uu____3948
                                                              with
                                                              | (hd1,uu____3964)
                                                                  ->
                                                                  (match 
                                                                    hd1.FStar_Syntax_Syntax.n
                                                                   with
                                                                   | 
                                                                   FStar_Syntax_Syntax.Tm_uvar
                                                                    (uv,uu____3986)
                                                                    ->
                                                                    appears
                                                                    uv goals
                                                                   | 
                                                                   uu____4011
                                                                    -> false)
                                                               in
                                                            let uu____4012 =
                                                              FStar_All.pipe_right
                                                                implicits.FStar_TypeChecker_Env.implicits
                                                                (mapM
                                                                   (fun
                                                                    uu____4084
                                                                     ->
                                                                    match uu____4084
                                                                    with
                                                                    | 
                                                                    (_msg,env,_uvar,term,typ,uu____4112)
                                                                    ->
                                                                    let uu____4113
                                                                    =
                                                                    FStar_Syntax_Util.head_and_args
                                                                    term  in
                                                                    (match uu____4113
                                                                    with
                                                                    | 
                                                                    (hd1,uu____4139)
                                                                    ->
                                                                    let uu____4160
                                                                    =
                                                                    let uu____4161
                                                                    =
                                                                    FStar_Syntax_Subst.compress
                                                                    hd1  in
                                                                    uu____4161.FStar_Syntax_Syntax.n
                                                                     in
                                                                    (match uu____4160
                                                                    with
                                                                    | 
                                                                    FStar_Syntax_Syntax.Tm_uvar
                                                                    uu____4174
                                                                    ->
                                                                    let uu____4191
                                                                    =
                                                                    let uu____4200
                                                                    =
                                                                    let uu____4203
                                                                    =
                                                                    let uu___90_4204
                                                                    = goal
                                                                     in
                                                                    let uu____4205
                                                                    =
                                                                    bnorm
                                                                    goal.FStar_Tactics_Types.context
                                                                    term  in
                                                                    let uu____4206
                                                                    =
                                                                    bnorm
                                                                    goal.FStar_Tactics_Types.context
                                                                    typ  in
                                                                    {
                                                                    FStar_Tactics_Types.context
                                                                    =
                                                                    (uu___90_4204.FStar_Tactics_Types.context);
                                                                    FStar_Tactics_Types.witness
                                                                    =
                                                                    uu____4205;
                                                                    FStar_Tactics_Types.goal_ty
                                                                    =
                                                                    uu____4206;
                                                                    FStar_Tactics_Types.opts
                                                                    =
                                                                    (uu___90_4204.FStar_Tactics_Types.opts);
                                                                    FStar_Tactics_Types.is_guard
                                                                    =
                                                                    (uu___90_4204.FStar_Tactics_Types.is_guard)
                                                                    }  in
                                                                    [uu____4203]
                                                                     in
                                                                    (uu____4200,
                                                                    [])  in
                                                                    ret
                                                                    uu____4191
                                                                    | 
                                                                    uu____4219
                                                                    ->
                                                                    let g_typ
                                                                    =
                                                                    let uu____4221
                                                                    =
                                                                    FStar_Options.__temp_fast_implicits
                                                                    ()  in
                                                                    if
                                                                    uu____4221
                                                                    then
                                                                    FStar_TypeChecker_TcTerm.check_type_of_well_typed_term
                                                                    false env
                                                                    term typ
                                                                    else
                                                                    (let term1
                                                                    =
                                                                    bnorm env
                                                                    term  in
                                                                    let uu____4224
                                                                    =
                                                                    let uu____4231
                                                                    =
                                                                    FStar_TypeChecker_Env.set_expected_typ
                                                                    env typ
                                                                     in
                                                                    env.FStar_TypeChecker_Env.type_of
                                                                    uu____4231
                                                                    term1  in
                                                                    match uu____4224
                                                                    with
                                                                    | 
                                                                    (uu____4232,uu____4233,g_typ)
                                                                    -> g_typ)
                                                                     in
                                                                    let uu____4235
                                                                    =
                                                                    goal_from_guard
                                                                    "apply_lemma solved arg"
                                                                    goal.FStar_Tactics_Types.context
                                                                    g_typ
                                                                    goal.FStar_Tactics_Types.opts
                                                                     in
                                                                    bind
                                                                    uu____4235
                                                                    (fun
                                                                    uu___58_4251
                                                                     ->
                                                                    match uu___58_4251
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
                                                            bind uu____4012
                                                              (fun goals_  ->
                                                                 let sub_goals
                                                                   =
                                                                   let uu____4319
                                                                    =
                                                                    FStar_List.map
                                                                    FStar_Pervasives_Native.fst
                                                                    goals_
                                                                     in
                                                                   FStar_List.flatten
                                                                    uu____4319
                                                                    in
                                                                 let smt_goals
                                                                   =
                                                                   let uu____4341
                                                                    =
                                                                    FStar_List.map
                                                                    FStar_Pervasives_Native.snd
                                                                    goals_
                                                                     in
                                                                   FStar_List.flatten
                                                                    uu____4341
                                                                    in
                                                                 let rec filter'
                                                                   a f xs =
                                                                   match xs
                                                                   with
                                                                   | 
                                                                   [] -> []
                                                                   | 
                                                                   x::xs1 ->
                                                                    let uu____4396
                                                                    = f x xs1
                                                                     in
                                                                    if
                                                                    uu____4396
                                                                    then
                                                                    let uu____4399
                                                                    =
                                                                    filter'
                                                                    () f xs1
                                                                     in x ::
                                                                    uu____4399
                                                                    else
                                                                    filter'
                                                                    () f xs1
                                                                    in
                                                                 let sub_goals1
                                                                   =
                                                                   Obj.magic
                                                                    (filter'
                                                                    ()
                                                                    (fun a438
                                                                     ->
                                                                    fun a439 
                                                                    ->
                                                                    (Obj.magic
                                                                    (fun g 
                                                                    ->
                                                                    fun goals
                                                                     ->
                                                                    let uu____4413
                                                                    =
                                                                    checkone
                                                                    g.FStar_Tactics_Types.witness
                                                                    goals  in
                                                                    Prims.op_Negation
                                                                    uu____4413))
                                                                    a438 a439)
                                                                    (Obj.magic
                                                                    sub_goals))
                                                                    in
                                                                 let uu____4414
                                                                   =
                                                                   proc_guard
                                                                    "apply_lemma guard"
                                                                    goal.FStar_Tactics_Types.context
                                                                    guard
                                                                    goal.FStar_Tactics_Types.opts
                                                                    in
                                                                 bind
                                                                   uu____4414
                                                                   (fun
                                                                    uu____4419
                                                                     ->
                                                                    let uu____4420
                                                                    =
                                                                    let uu____4423
                                                                    =
                                                                    let uu____4424
                                                                    =
                                                                    let uu____4425
                                                                    =
                                                                    FStar_Syntax_Util.mk_squash
                                                                    FStar_Syntax_Syntax.U_zero
                                                                    pre1  in
                                                                    istrivial
                                                                    goal.FStar_Tactics_Types.context
                                                                    uu____4425
                                                                     in
                                                                    Prims.op_Negation
                                                                    uu____4424
                                                                     in
                                                                    if
                                                                    uu____4423
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
                                                                    uu____4420
                                                                    (fun
                                                                    uu____4431
                                                                     ->
                                                                    let uu____4432
                                                                    =
                                                                    add_smt_goals
                                                                    smt_goals
                                                                     in
                                                                    bind
                                                                    uu____4432
                                                                    (fun
                                                                    uu____4436
                                                                     ->
                                                                    add_goals
                                                                    sub_goals1))))))))))))))
         in
      focus uu____3452  in
    FStar_All.pipe_left (wrap_err "apply_lemma") uu____3449
  
let (destruct_eq' :
  FStar_Syntax_Syntax.typ ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun typ  ->
    let uu____4456 = FStar_Syntax_Util.destruct_typ_as_formula typ  in
    match uu____4456 with
    | FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn
        (l,uu____4466::(e1,uu____4468)::(e2,uu____4470)::[])) when
        FStar_Ident.lid_equals l FStar_Parser_Const.eq2_lid ->
        FStar_Pervasives_Native.Some (e1, e2)
    | uu____4529 -> FStar_Pervasives_Native.None
  
let (destruct_eq :
  FStar_Syntax_Syntax.typ ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun typ  ->
    let uu____4551 = destruct_eq' typ  in
    match uu____4551 with
    | FStar_Pervasives_Native.Some t -> FStar_Pervasives_Native.Some t
    | FStar_Pervasives_Native.None  ->
        let uu____4581 = FStar_Syntax_Util.un_squash typ  in
        (match uu____4581 with
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
        let uu____4637 = FStar_TypeChecker_Env.pop_bv e1  in
        match uu____4637 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (bv',e') ->
            if FStar_Syntax_Syntax.bv_eq bvar bv'
            then FStar_Pervasives_Native.Some (e', [])
            else
              (let uu____4685 = aux e'  in
               FStar_Util.map_opt uu____4685
                 (fun uu____4709  ->
                    match uu____4709 with | (e'',bvs) -> (e'', (bv' :: bvs))))
         in
      let uu____4730 = aux e  in
      FStar_Util.map_opt uu____4730
        (fun uu____4754  ->
           match uu____4754 with | (e',bvs) -> (e', (FStar_List.rev bvs)))
  
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
          let uu____4809 = split_env b1 g.FStar_Tactics_Types.context  in
          FStar_Util.map_opt uu____4809
            (fun uu____4833  ->
               match uu____4833 with
               | (e0,bvs) ->
                   let s1 bv =
                     let uu___91_4850 = bv  in
                     let uu____4851 =
                       FStar_Syntax_Subst.subst s bv.FStar_Syntax_Syntax.sort
                        in
                     {
                       FStar_Syntax_Syntax.ppname =
                         (uu___91_4850.FStar_Syntax_Syntax.ppname);
                       FStar_Syntax_Syntax.index =
                         (uu___91_4850.FStar_Syntax_Syntax.index);
                       FStar_Syntax_Syntax.sort = uu____4851
                     }  in
                   let bvs1 = FStar_List.map s1 bvs  in
                   let c = push_bvs e0 (b2 :: bvs1)  in
                   let w =
                     FStar_Syntax_Subst.subst s g.FStar_Tactics_Types.witness
                      in
                   let t =
                     FStar_Syntax_Subst.subst s g.FStar_Tactics_Types.goal_ty
                      in
                   let uu___92_4860 = g  in
                   {
                     FStar_Tactics_Types.context = c;
                     FStar_Tactics_Types.witness = w;
                     FStar_Tactics_Types.goal_ty = t;
                     FStar_Tactics_Types.opts =
                       (uu___92_4860.FStar_Tactics_Types.opts);
                     FStar_Tactics_Types.is_guard =
                       (uu___92_4860.FStar_Tactics_Types.is_guard)
                   })
  
let (rewrite : FStar_Syntax_Syntax.binder -> Prims.unit tac) =
  fun h  ->
    bind cur_goal
      (fun goal  ->
         let uu____4873 = h  in
         match uu____4873 with
         | (bv,uu____4877) ->
             mlog
               (fun uu____4881  ->
                  let uu____4882 = FStar_Syntax_Print.bv_to_string bv  in
                  let uu____4883 =
                    tts goal.FStar_Tactics_Types.context
                      bv.FStar_Syntax_Syntax.sort
                     in
                  FStar_Util.print2 "+++Rewrite %s : %s\n" uu____4882
                    uu____4883)
               (fun uu____4886  ->
                  let uu____4887 =
                    split_env bv goal.FStar_Tactics_Types.context  in
                  match uu____4887 with
                  | FStar_Pervasives_Native.None  ->
                      fail "rewrite: binder not found in environment"
                  | FStar_Pervasives_Native.Some (e0,bvs) ->
                      let uu____4916 =
                        destruct_eq bv.FStar_Syntax_Syntax.sort  in
                      (match uu____4916 with
                       | FStar_Pervasives_Native.Some (x,e) ->
                           let uu____4931 =
                             let uu____4932 = FStar_Syntax_Subst.compress x
                                in
                             uu____4932.FStar_Syntax_Syntax.n  in
                           (match uu____4931 with
                            | FStar_Syntax_Syntax.Tm_name x1 ->
                                let s = [FStar_Syntax_Syntax.NT (x1, e)]  in
                                let s1 bv1 =
                                  let uu___93_4945 = bv1  in
                                  let uu____4946 =
                                    FStar_Syntax_Subst.subst s
                                      bv1.FStar_Syntax_Syntax.sort
                                     in
                                  {
                                    FStar_Syntax_Syntax.ppname =
                                      (uu___93_4945.FStar_Syntax_Syntax.ppname);
                                    FStar_Syntax_Syntax.index =
                                      (uu___93_4945.FStar_Syntax_Syntax.index);
                                    FStar_Syntax_Syntax.sort = uu____4946
                                  }  in
                                let bvs1 = FStar_List.map s1 bvs  in
                                let uu____4952 =
                                  let uu___94_4953 = goal  in
                                  let uu____4954 = push_bvs e0 (bv :: bvs1)
                                     in
                                  let uu____4955 =
                                    FStar_Syntax_Subst.subst s
                                      goal.FStar_Tactics_Types.witness
                                     in
                                  let uu____4956 =
                                    FStar_Syntax_Subst.subst s
                                      goal.FStar_Tactics_Types.goal_ty
                                     in
                                  {
                                    FStar_Tactics_Types.context = uu____4954;
                                    FStar_Tactics_Types.witness = uu____4955;
                                    FStar_Tactics_Types.goal_ty = uu____4956;
                                    FStar_Tactics_Types.opts =
                                      (uu___94_4953.FStar_Tactics_Types.opts);
                                    FStar_Tactics_Types.is_guard =
                                      (uu___94_4953.FStar_Tactics_Types.is_guard)
                                  }  in
                                replace_cur uu____4952
                            | uu____4957 ->
                                fail
                                  "rewrite: Not an equality hypothesis with a variable on the LHS")
                       | uu____4958 ->
                           fail "rewrite: Not an equality hypothesis")))
  
let (rename_to :
  FStar_Syntax_Syntax.binder -> Prims.string -> Prims.unit tac) =
  fun b  ->
    fun s  ->
      bind cur_goal
        (fun goal  ->
           let uu____4983 = b  in
           match uu____4983 with
           | (bv,uu____4987) ->
               let bv' =
                 FStar_Syntax_Syntax.freshen_bv
                   (let uu___95_4991 = bv  in
                    {
                      FStar_Syntax_Syntax.ppname =
                        (FStar_Ident.mk_ident
                           (s,
                             ((bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange)));
                      FStar_Syntax_Syntax.index =
                        (uu___95_4991.FStar_Syntax_Syntax.index);
                      FStar_Syntax_Syntax.sort =
                        (uu___95_4991.FStar_Syntax_Syntax.sort)
                    })
                  in
               let s1 =
                 let uu____4995 =
                   let uu____4996 =
                     let uu____5003 = FStar_Syntax_Syntax.bv_to_name bv'  in
                     (bv, uu____5003)  in
                   FStar_Syntax_Syntax.NT uu____4996  in
                 [uu____4995]  in
               let uu____5004 = subst_goal bv bv' s1 goal  in
               (match uu____5004 with
                | FStar_Pervasives_Native.None  ->
                    fail "rename_to: binder not found in environment"
                | FStar_Pervasives_Native.Some goal1 -> replace_cur goal1))
  
let (binder_retype : FStar_Syntax_Syntax.binder -> Prims.unit tac) =
  fun b  ->
    bind cur_goal
      (fun goal  ->
         let uu____5023 = b  in
         match uu____5023 with
         | (bv,uu____5027) ->
             let uu____5028 = split_env bv goal.FStar_Tactics_Types.context
                in
             (match uu____5028 with
              | FStar_Pervasives_Native.None  ->
                  fail "binder_retype: binder is not present in environment"
              | FStar_Pervasives_Native.Some (e0,bvs) ->
                  let uu____5057 = FStar_Syntax_Util.type_u ()  in
                  (match uu____5057 with
                   | (ty,u) ->
                       let uu____5066 = new_uvar "binder_retype" e0 ty  in
                       bind uu____5066
                         (fun t'  ->
                            let bv'' =
                              let uu___96_5076 = bv  in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___96_5076.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___96_5076.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = t'
                              }  in
                            let s =
                              let uu____5080 =
                                let uu____5081 =
                                  let uu____5088 =
                                    FStar_Syntax_Syntax.bv_to_name bv''  in
                                  (bv, uu____5088)  in
                                FStar_Syntax_Syntax.NT uu____5081  in
                              [uu____5080]  in
                            let bvs1 =
                              FStar_List.map
                                (fun b1  ->
                                   let uu___97_5096 = b1  in
                                   let uu____5097 =
                                     FStar_Syntax_Subst.subst s
                                       b1.FStar_Syntax_Syntax.sort
                                      in
                                   {
                                     FStar_Syntax_Syntax.ppname =
                                       (uu___97_5096.FStar_Syntax_Syntax.ppname);
                                     FStar_Syntax_Syntax.index =
                                       (uu___97_5096.FStar_Syntax_Syntax.index);
                                     FStar_Syntax_Syntax.sort = uu____5097
                                   }) bvs
                               in
                            let env' = push_bvs e0 (bv'' :: bvs1)  in
                            bind dismiss
                              (fun uu____5103  ->
                                 let uu____5104 =
                                   let uu____5107 =
                                     let uu____5110 =
                                       let uu___98_5111 = goal  in
                                       let uu____5112 =
                                         FStar_Syntax_Subst.subst s
                                           goal.FStar_Tactics_Types.witness
                                          in
                                       let uu____5113 =
                                         FStar_Syntax_Subst.subst s
                                           goal.FStar_Tactics_Types.goal_ty
                                          in
                                       {
                                         FStar_Tactics_Types.context = env';
                                         FStar_Tactics_Types.witness =
                                           uu____5112;
                                         FStar_Tactics_Types.goal_ty =
                                           uu____5113;
                                         FStar_Tactics_Types.opts =
                                           (uu___98_5111.FStar_Tactics_Types.opts);
                                         FStar_Tactics_Types.is_guard =
                                           (uu___98_5111.FStar_Tactics_Types.is_guard)
                                       }  in
                                     [uu____5110]  in
                                   add_goals uu____5107  in
                                 bind uu____5104
                                   (fun uu____5116  ->
                                      let uu____5117 =
                                        FStar_Syntax_Util.mk_eq2
                                          (FStar_Syntax_Syntax.U_succ u) ty
                                          bv.FStar_Syntax_Syntax.sort t'
                                         in
                                      add_irrelevant_goal
                                        "binder_retype equation" e0
                                        uu____5117
                                        goal.FStar_Tactics_Types.opts))))))
  
let (norm_binder_type :
  FStar_Syntax_Embeddings.norm_step Prims.list ->
    FStar_Syntax_Syntax.binder -> Prims.unit tac)
  =
  fun s  ->
    fun b  ->
      bind cur_goal
        (fun goal  ->
           let uu____5138 = b  in
           match uu____5138 with
           | (bv,uu____5142) ->
               let uu____5143 = split_env bv goal.FStar_Tactics_Types.context
                  in
               (match uu____5143 with
                | FStar_Pervasives_Native.None  ->
                    fail
                      "binder_retype: binder is not present in environment"
                | FStar_Pervasives_Native.Some (e0,bvs) ->
                    let steps =
                      let uu____5175 =
                        FStar_TypeChecker_Normalize.tr_norm_steps s  in
                      FStar_List.append
                        [FStar_TypeChecker_Normalize.Reify;
                        FStar_TypeChecker_Normalize.UnfoldTac] uu____5175
                       in
                    let sort' =
                      normalize steps e0 bv.FStar_Syntax_Syntax.sort  in
                    let bv' =
                      let uu___99_5180 = bv  in
                      {
                        FStar_Syntax_Syntax.ppname =
                          (uu___99_5180.FStar_Syntax_Syntax.ppname);
                        FStar_Syntax_Syntax.index =
                          (uu___99_5180.FStar_Syntax_Syntax.index);
                        FStar_Syntax_Syntax.sort = sort'
                      }  in
                    let env' = push_bvs e0 (bv' :: bvs)  in
                    replace_cur
                      (let uu___100_5184 = goal  in
                       {
                         FStar_Tactics_Types.context = env';
                         FStar_Tactics_Types.witness =
                           (uu___100_5184.FStar_Tactics_Types.witness);
                         FStar_Tactics_Types.goal_ty =
                           (uu___100_5184.FStar_Tactics_Types.goal_ty);
                         FStar_Tactics_Types.opts =
                           (uu___100_5184.FStar_Tactics_Types.opts);
                         FStar_Tactics_Types.is_guard =
                           (uu___100_5184.FStar_Tactics_Types.is_guard)
                       })))
  
let (revert : Prims.unit tac) =
  bind cur_goal
    (fun goal  ->
       let uu____5192 =
         FStar_TypeChecker_Env.pop_bv goal.FStar_Tactics_Types.context  in
       match uu____5192 with
       | FStar_Pervasives_Native.None  -> fail "Cannot revert; empty context"
       | FStar_Pervasives_Native.Some (x,env') ->
           let typ' =
             let uu____5214 =
               FStar_Syntax_Syntax.mk_Total goal.FStar_Tactics_Types.goal_ty
                in
             FStar_Syntax_Util.arrow [(x, FStar_Pervasives_Native.None)]
               uu____5214
              in
           let w' =
             FStar_Syntax_Util.abs [(x, FStar_Pervasives_Native.None)]
               goal.FStar_Tactics_Types.witness FStar_Pervasives_Native.None
              in
           replace_cur
             (let uu___101_5248 = goal  in
              {
                FStar_Tactics_Types.context = env';
                FStar_Tactics_Types.witness = w';
                FStar_Tactics_Types.goal_ty = typ';
                FStar_Tactics_Types.opts =
                  (uu___101_5248.FStar_Tactics_Types.opts);
                FStar_Tactics_Types.is_guard =
                  (uu___101_5248.FStar_Tactics_Types.is_guard)
              }))
  
let (free_in :
  FStar_Syntax_Syntax.bv -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun bv  ->
    fun t  ->
      let uu____5255 = FStar_Syntax_Free.names t  in
      FStar_Util.set_mem bv uu____5255
  
let rec (clear : FStar_Syntax_Syntax.binder -> Prims.unit tac) =
  fun b  ->
    let bv = FStar_Pervasives_Native.fst b  in
    bind cur_goal
      (fun goal  ->
         mlog
           (fun uu____5271  ->
              let uu____5272 = FStar_Syntax_Print.binder_to_string b  in
              let uu____5273 =
                let uu____5274 =
                  let uu____5275 =
                    FStar_TypeChecker_Env.all_binders
                      goal.FStar_Tactics_Types.context
                     in
                  FStar_All.pipe_right uu____5275 FStar_List.length  in
                FStar_All.pipe_right uu____5274 FStar_Util.string_of_int  in
              FStar_Util.print2 "Clear of (%s), env has %s binders\n"
                uu____5272 uu____5273)
           (fun uu____5286  ->
              let uu____5287 = split_env bv goal.FStar_Tactics_Types.context
                 in
              match uu____5287 with
              | FStar_Pervasives_Native.None  ->
                  fail "Cannot clear; binder not in environment"
              | FStar_Pervasives_Native.Some (e',bvs) ->
                  let rec check1 bvs1 =
                    match bvs1 with
                    | [] -> ret ()
                    | bv'::bvs2 ->
                        let uu____5332 =
                          free_in bv bv'.FStar_Syntax_Syntax.sort  in
                        if uu____5332
                        then
                          let uu____5335 =
                            let uu____5336 =
                              FStar_Syntax_Print.bv_to_string bv'  in
                            FStar_Util.format1
                              "Cannot clear; binder present in the type of %s"
                              uu____5336
                             in
                          fail uu____5335
                        else check1 bvs2
                     in
                  let uu____5338 =
                    free_in bv goal.FStar_Tactics_Types.goal_ty  in
                  if uu____5338
                  then fail "Cannot clear; binder present in goal"
                  else
                    (let uu____5342 = check1 bvs  in
                     bind uu____5342
                       (fun uu____5348  ->
                          let env' = push_bvs e' bvs  in
                          let uu____5350 =
                            new_uvar "clear.witness" env'
                              goal.FStar_Tactics_Types.goal_ty
                             in
                          bind uu____5350
                            (fun ut  ->
                               let uu____5356 =
                                 do_unify goal.FStar_Tactics_Types.context
                                   goal.FStar_Tactics_Types.witness ut
                                  in
                               bind uu____5356
                                 (fun b1  ->
                                    if b1
                                    then
                                      replace_cur
                                        (let uu___102_5365 = goal  in
                                         {
                                           FStar_Tactics_Types.context = env';
                                           FStar_Tactics_Types.witness = ut;
                                           FStar_Tactics_Types.goal_ty =
                                             (uu___102_5365.FStar_Tactics_Types.goal_ty);
                                           FStar_Tactics_Types.opts =
                                             (uu___102_5365.FStar_Tactics_Types.opts);
                                           FStar_Tactics_Types.is_guard =
                                             (uu___102_5365.FStar_Tactics_Types.is_guard)
                                         })
                                    else
                                      fail
                                        "Cannot clear; binder appears in witness"))))))
  
let (clear_top : Prims.unit tac) =
  bind cur_goal
    (fun goal  ->
       let uu____5374 =
         FStar_TypeChecker_Env.pop_bv goal.FStar_Tactics_Types.context  in
       match uu____5374 with
       | FStar_Pervasives_Native.None  -> fail "Cannot clear; empty context"
       | FStar_Pervasives_Native.Some (x,uu____5388) ->
           let uu____5393 = FStar_Syntax_Syntax.mk_binder x  in
           clear uu____5393)
  
let (prune : Prims.string -> Prims.unit tac) =
  fun s  ->
    bind cur_goal
      (fun g  ->
         let ctx = g.FStar_Tactics_Types.context  in
         let ctx' =
           FStar_TypeChecker_Env.rem_proof_ns ctx
             (FStar_Ident.path_of_text s)
            in
         let g' =
           let uu___103_5409 = g  in
           {
             FStar_Tactics_Types.context = ctx';
             FStar_Tactics_Types.witness =
               (uu___103_5409.FStar_Tactics_Types.witness);
             FStar_Tactics_Types.goal_ty =
               (uu___103_5409.FStar_Tactics_Types.goal_ty);
             FStar_Tactics_Types.opts =
               (uu___103_5409.FStar_Tactics_Types.opts);
             FStar_Tactics_Types.is_guard =
               (uu___103_5409.FStar_Tactics_Types.is_guard)
           }  in
         bind dismiss (fun uu____5411  -> add_goals [g']))
  
let (addns : Prims.string -> Prims.unit tac) =
  fun s  ->
    bind cur_goal
      (fun g  ->
         let ctx = g.FStar_Tactics_Types.context  in
         let ctx' =
           FStar_TypeChecker_Env.add_proof_ns ctx
             (FStar_Ident.path_of_text s)
            in
         let g' =
           let uu___104_5427 = g  in
           {
             FStar_Tactics_Types.context = ctx';
             FStar_Tactics_Types.witness =
               (uu___104_5427.FStar_Tactics_Types.witness);
             FStar_Tactics_Types.goal_ty =
               (uu___104_5427.FStar_Tactics_Types.goal_ty);
             FStar_Tactics_Types.opts =
               (uu___104_5427.FStar_Tactics_Types.opts);
             FStar_Tactics_Types.is_guard =
               (uu___104_5427.FStar_Tactics_Types.is_guard)
           }  in
         bind dismiss (fun uu____5429  -> add_goals [g']))
  
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
            let uu____5461 = FStar_Syntax_Subst.compress t  in
            uu____5461.FStar_Syntax_Syntax.n  in
          let uu____5464 =
            if d = FStar_Tactics_Types.TopDown
            then
              f env
                (let uu___108_5470 = t  in
                 {
                   FStar_Syntax_Syntax.n = tn;
                   FStar_Syntax_Syntax.pos =
                     (uu___108_5470.FStar_Syntax_Syntax.pos);
                   FStar_Syntax_Syntax.vars =
                     (uu___108_5470.FStar_Syntax_Syntax.vars)
                 })
            else ret t  in
          bind uu____5464
            (fun t1  ->
               let ff = tac_fold_env d f env  in
               let tn1 =
                 let uu____5484 =
                   let uu____5485 = FStar_Syntax_Subst.compress t1  in
                   uu____5485.FStar_Syntax_Syntax.n  in
                 match uu____5484 with
                 | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
                     let uu____5512 = ff hd1  in
                     bind uu____5512
                       (fun hd2  ->
                          let fa uu____5532 =
                            match uu____5532 with
                            | (a,q) ->
                                let uu____5545 = ff a  in
                                bind uu____5545 (fun a1  -> ret (a1, q))
                             in
                          let uu____5558 = mapM fa args  in
                          bind uu____5558
                            (fun args1  ->
                               ret (FStar_Syntax_Syntax.Tm_app (hd2, args1))))
                 | FStar_Syntax_Syntax.Tm_abs (bs,t2,k) ->
                     let uu____5618 = FStar_Syntax_Subst.open_term bs t2  in
                     (match uu____5618 with
                      | (bs1,t') ->
                          let uu____5627 =
                            let uu____5630 =
                              FStar_TypeChecker_Env.push_binders env bs1  in
                            tac_fold_env d f uu____5630 t'  in
                          bind uu____5627
                            (fun t''  ->
                               let uu____5634 =
                                 let uu____5635 =
                                   let uu____5652 =
                                     FStar_Syntax_Subst.close_binders bs1  in
                                   let uu____5653 =
                                     FStar_Syntax_Subst.close bs1 t''  in
                                   (uu____5652, uu____5653, k)  in
                                 FStar_Syntax_Syntax.Tm_abs uu____5635  in
                               ret uu____5634))
                 | FStar_Syntax_Syntax.Tm_arrow (bs,k) -> ret tn
                 | FStar_Syntax_Syntax.Tm_match (hd1,brs) ->
                     let uu____5712 = ff hd1  in
                     bind uu____5712
                       (fun hd2  ->
                          let ffb br =
                            let uu____5725 =
                              FStar_Syntax_Subst.open_branch br  in
                            match uu____5725 with
                            | (pat,w,e) ->
                                let uu____5747 = ff e  in
                                bind uu____5747
                                  (fun e1  ->
                                     let br1 =
                                       FStar_Syntax_Subst.close_branch
                                         (pat, w, e1)
                                        in
                                     ret br1)
                             in
                          let uu____5760 = mapM ffb brs  in
                          bind uu____5760
                            (fun brs1  ->
                               ret (FStar_Syntax_Syntax.Tm_match (hd2, brs1))))
                 | FStar_Syntax_Syntax.Tm_let
                     ((false
                       ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inl bv;
                          FStar_Syntax_Syntax.lbunivs = uu____5774;
                          FStar_Syntax_Syntax.lbtyp = uu____5775;
                          FStar_Syntax_Syntax.lbeff = uu____5776;
                          FStar_Syntax_Syntax.lbdef = def;
                          FStar_Syntax_Syntax.lbattrs = uu____5778;
                          FStar_Syntax_Syntax.lbpos = uu____5779;_}::[]),e)
                     ->
                     let lb =
                       let uu____5804 =
                         let uu____5805 = FStar_Syntax_Subst.compress t1  in
                         uu____5805.FStar_Syntax_Syntax.n  in
                       match uu____5804 with
                       | FStar_Syntax_Syntax.Tm_let
                           ((false ,lb::[]),uu____5809) -> lb
                       | uu____5822 -> failwith "impossible"  in
                     let fflb lb1 =
                       let uu____5829 = ff lb1.FStar_Syntax_Syntax.lbdef  in
                       bind uu____5829
                         (fun def1  ->
                            ret
                              (let uu___105_5835 = lb1  in
                               {
                                 FStar_Syntax_Syntax.lbname =
                                   (uu___105_5835.FStar_Syntax_Syntax.lbname);
                                 FStar_Syntax_Syntax.lbunivs =
                                   (uu___105_5835.FStar_Syntax_Syntax.lbunivs);
                                 FStar_Syntax_Syntax.lbtyp =
                                   (uu___105_5835.FStar_Syntax_Syntax.lbtyp);
                                 FStar_Syntax_Syntax.lbeff =
                                   (uu___105_5835.FStar_Syntax_Syntax.lbeff);
                                 FStar_Syntax_Syntax.lbdef = def1;
                                 FStar_Syntax_Syntax.lbattrs =
                                   (uu___105_5835.FStar_Syntax_Syntax.lbattrs);
                                 FStar_Syntax_Syntax.lbpos =
                                   (uu___105_5835.FStar_Syntax_Syntax.lbpos)
                               }))
                        in
                     let uu____5836 = fflb lb  in
                     bind uu____5836
                       (fun lb1  ->
                          let uu____5845 =
                            let uu____5850 =
                              let uu____5851 =
                                FStar_Syntax_Syntax.mk_binder bv  in
                              [uu____5851]  in
                            FStar_Syntax_Subst.open_term uu____5850 e  in
                          match uu____5845 with
                          | (bs,e1) ->
                              let uu____5856 = ff e1  in
                              bind uu____5856
                                (fun e2  ->
                                   let e3 = FStar_Syntax_Subst.close bs e2
                                      in
                                   ret
                                     (FStar_Syntax_Syntax.Tm_let
                                        ((false, [lb1]), e3))))
                 | FStar_Syntax_Syntax.Tm_let ((true ,lbs),e) ->
                     let fflb lb =
                       let uu____5893 = ff lb.FStar_Syntax_Syntax.lbdef  in
                       bind uu____5893
                         (fun def  ->
                            ret
                              (let uu___106_5899 = lb  in
                               {
                                 FStar_Syntax_Syntax.lbname =
                                   (uu___106_5899.FStar_Syntax_Syntax.lbname);
                                 FStar_Syntax_Syntax.lbunivs =
                                   (uu___106_5899.FStar_Syntax_Syntax.lbunivs);
                                 FStar_Syntax_Syntax.lbtyp =
                                   (uu___106_5899.FStar_Syntax_Syntax.lbtyp);
                                 FStar_Syntax_Syntax.lbeff =
                                   (uu___106_5899.FStar_Syntax_Syntax.lbeff);
                                 FStar_Syntax_Syntax.lbdef = def;
                                 FStar_Syntax_Syntax.lbattrs =
                                   (uu___106_5899.FStar_Syntax_Syntax.lbattrs);
                                 FStar_Syntax_Syntax.lbpos =
                                   (uu___106_5899.FStar_Syntax_Syntax.lbpos)
                               }))
                        in
                     let uu____5900 = FStar_Syntax_Subst.open_let_rec lbs e
                        in
                     (match uu____5900 with
                      | (lbs1,e1) ->
                          let uu____5915 = mapM fflb lbs1  in
                          bind uu____5915
                            (fun lbs2  ->
                               let uu____5927 = ff e1  in
                               bind uu____5927
                                 (fun e2  ->
                                    let uu____5935 =
                                      FStar_Syntax_Subst.close_let_rec lbs2
                                        e2
                                       in
                                    match uu____5935 with
                                    | (lbs3,e3) ->
                                        ret
                                          (FStar_Syntax_Syntax.Tm_let
                                             ((true, lbs3), e3)))))
                 | FStar_Syntax_Syntax.Tm_ascribed (t2,asc,eff) ->
                     let uu____6001 = ff t2  in
                     bind uu____6001
                       (fun t3  ->
                          ret
                            (FStar_Syntax_Syntax.Tm_ascribed (t3, asc, eff)))
                 | FStar_Syntax_Syntax.Tm_meta (t2,m) ->
                     let uu____6030 = ff t2  in
                     bind uu____6030
                       (fun t3  -> ret (FStar_Syntax_Syntax.Tm_meta (t3, m)))
                 | uu____6035 -> ret tn  in
               bind tn1
                 (fun tn2  ->
                    let t' =
                      let uu___107_6042 = t1  in
                      {
                        FStar_Syntax_Syntax.n = tn2;
                        FStar_Syntax_Syntax.pos =
                          (uu___107_6042.FStar_Syntax_Syntax.pos);
                        FStar_Syntax_Syntax.vars =
                          (uu___107_6042.FStar_Syntax_Syntax.vars)
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
            let uu____6071 = FStar_TypeChecker_TcTerm.tc_term env t  in
            match uu____6071 with
            | (t1,lcomp,g) ->
                let uu____6083 =
                  (let uu____6086 =
                     FStar_Syntax_Util.is_pure_or_ghost_lcomp lcomp  in
                   Prims.op_Negation uu____6086) ||
                    (let uu____6088 = FStar_TypeChecker_Rel.is_trivial g  in
                     Prims.op_Negation uu____6088)
                   in
                if uu____6083
                then ret t1
                else
                  (let rewrite_eq =
                     let typ = lcomp.FStar_Syntax_Syntax.res_typ  in
                     let uu____6098 = new_uvar "pointwise_rec" env typ  in
                     bind uu____6098
                       (fun ut  ->
                          log ps
                            (fun uu____6109  ->
                               let uu____6110 =
                                 FStar_Syntax_Print.term_to_string t1  in
                               let uu____6111 =
                                 FStar_Syntax_Print.term_to_string ut  in
                               FStar_Util.print2
                                 "Pointwise_rec: making equality\n\t%s ==\n\t%s\n"
                                 uu____6110 uu____6111);
                          (let uu____6112 =
                             let uu____6115 =
                               let uu____6116 =
                                 FStar_TypeChecker_TcTerm.universe_of env typ
                                  in
                               FStar_Syntax_Util.mk_eq2 uu____6116 typ t1 ut
                                in
                             add_irrelevant_goal "pointwise_rec equation" env
                               uu____6115 opts
                              in
                           bind uu____6112
                             (fun uu____6119  ->
                                let uu____6120 =
                                  bind tau
                                    (fun uu____6126  ->
                                       let ut1 =
                                         FStar_TypeChecker_Normalize.reduce_uvar_solutions
                                           env ut
                                          in
                                       log ps
                                         (fun uu____6132  ->
                                            let uu____6133 =
                                              FStar_Syntax_Print.term_to_string
                                                t1
                                               in
                                            let uu____6134 =
                                              FStar_Syntax_Print.term_to_string
                                                ut1
                                               in
                                            FStar_Util.print2
                                              "Pointwise_rec: succeeded rewriting\n\t%s to\n\t%s\n"
                                              uu____6133 uu____6134);
                                       ret ut1)
                                   in
                                focus uu____6120)))
                      in
                   let uu____6135 = trytac' rewrite_eq  in
                   bind uu____6135
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
          let uu____6283 = FStar_Syntax_Subst.compress t  in
          maybe_continue ctrl uu____6283
            (fun t1  ->
               let uu____6287 =
                 f env
                   (let uu___111_6296 = t1  in
                    {
                      FStar_Syntax_Syntax.n = (t1.FStar_Syntax_Syntax.n);
                      FStar_Syntax_Syntax.pos =
                        (uu___111_6296.FStar_Syntax_Syntax.pos);
                      FStar_Syntax_Syntax.vars =
                        (uu___111_6296.FStar_Syntax_Syntax.vars)
                    })
                  in
               bind uu____6287
                 (fun uu____6308  ->
                    match uu____6308 with
                    | (t2,ctrl1) ->
                        maybe_continue ctrl1 t2
                          (fun t3  ->
                             let uu____6327 =
                               let uu____6328 =
                                 FStar_Syntax_Subst.compress t3  in
                               uu____6328.FStar_Syntax_Syntax.n  in
                             match uu____6327 with
                             | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
                                 let uu____6361 =
                                   ctrl_tac_fold f env ctrl1 hd1  in
                                 bind uu____6361
                                   (fun uu____6386  ->
                                      match uu____6386 with
                                      | (hd2,ctrl2) ->
                                          let ctrl3 = keep_going ctrl2  in
                                          let uu____6402 =
                                            ctrl_tac_fold_args f env ctrl3
                                              args
                                             in
                                          bind uu____6402
                                            (fun uu____6429  ->
                                               match uu____6429 with
                                               | (args1,ctrl4) ->
                                                   ret
                                                     ((let uu___109_6459 = t3
                                                          in
                                                       {
                                                         FStar_Syntax_Syntax.n
                                                           =
                                                           (FStar_Syntax_Syntax.Tm_app
                                                              (hd2, args1));
                                                         FStar_Syntax_Syntax.pos
                                                           =
                                                           (uu___109_6459.FStar_Syntax_Syntax.pos);
                                                         FStar_Syntax_Syntax.vars
                                                           =
                                                           (uu___109_6459.FStar_Syntax_Syntax.vars)
                                                       }), ctrl4)))
                             | FStar_Syntax_Syntax.Tm_abs (bs,t4,k) ->
                                 let uu____6485 =
                                   FStar_Syntax_Subst.open_term bs t4  in
                                 (match uu____6485 with
                                  | (bs1,t') ->
                                      let uu____6500 =
                                        let uu____6507 =
                                          FStar_TypeChecker_Env.push_binders
                                            env bs1
                                           in
                                        ctrl_tac_fold f uu____6507 ctrl1 t'
                                         in
                                      bind uu____6500
                                        (fun uu____6525  ->
                                           match uu____6525 with
                                           | (t'',ctrl2) ->
                                               let uu____6540 =
                                                 let uu____6547 =
                                                   let uu___110_6550 = t4  in
                                                   let uu____6553 =
                                                     let uu____6554 =
                                                       let uu____6571 =
                                                         FStar_Syntax_Subst.close_binders
                                                           bs1
                                                          in
                                                       let uu____6572 =
                                                         FStar_Syntax_Subst.close
                                                           bs1 t''
                                                          in
                                                       (uu____6571,
                                                         uu____6572, k)
                                                        in
                                                     FStar_Syntax_Syntax.Tm_abs
                                                       uu____6554
                                                      in
                                                   {
                                                     FStar_Syntax_Syntax.n =
                                                       uu____6553;
                                                     FStar_Syntax_Syntax.pos
                                                       =
                                                       (uu___110_6550.FStar_Syntax_Syntax.pos);
                                                     FStar_Syntax_Syntax.vars
                                                       =
                                                       (uu___110_6550.FStar_Syntax_Syntax.vars)
                                                   }  in
                                                 (uu____6547, ctrl2)  in
                                               ret uu____6540))
                             | FStar_Syntax_Syntax.Tm_arrow (bs,k) ->
                                 ret (t3, ctrl1)
                             | uu____6605 -> ret (t3, ctrl1))))

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
              let uu____6656 = ctrl_tac_fold f env ctrl t  in
              bind uu____6656
                (fun uu____6684  ->
                   match uu____6684 with
                   | (t1,ctrl1) ->
                       let uu____6703 = ctrl_tac_fold_args f env ctrl1 ts1
                          in
                       bind uu____6703
                         (fun uu____6734  ->
                            match uu____6734 with
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
              let uu____6818 =
                let uu____6825 =
                  add_irrelevant_goal "dummy" env FStar_Syntax_Util.t_true
                    opts
                   in
                bind uu____6825
                  (fun uu____6834  ->
                     let uu____6835 = ctrl t1  in
                     bind uu____6835
                       (fun res  -> bind trivial (fun uu____6862  -> ret res)))
                 in
              bind uu____6818
                (fun uu____6878  ->
                   match uu____6878 with
                   | (should_rewrite,ctrl1) ->
                       if Prims.op_Negation should_rewrite
                       then ret (t1, ctrl1)
                       else
                         (let uu____6902 =
                            FStar_TypeChecker_TcTerm.tc_term env t1  in
                          match uu____6902 with
                          | (t2,lcomp,g) ->
                              let uu____6918 =
                                (let uu____6921 =
                                   FStar_Syntax_Util.is_pure_or_ghost_lcomp
                                     lcomp
                                    in
                                 Prims.op_Negation uu____6921) ||
                                  (let uu____6923 =
                                     FStar_TypeChecker_Rel.is_trivial g  in
                                   Prims.op_Negation uu____6923)
                                 in
                              if uu____6918
                              then ret (t2, globalStop)
                              else
                                (let typ = lcomp.FStar_Syntax_Syntax.res_typ
                                    in
                                 let uu____6938 =
                                   new_uvar "pointwise_rec" env typ  in
                                 bind uu____6938
                                   (fun ut  ->
                                      log ps
                                        (fun uu____6953  ->
                                           let uu____6954 =
                                             FStar_Syntax_Print.term_to_string
                                               t2
                                              in
                                           let uu____6955 =
                                             FStar_Syntax_Print.term_to_string
                                               ut
                                              in
                                           FStar_Util.print2
                                             "Pointwise_rec: making equality\n\t%s ==\n\t%s\n"
                                             uu____6954 uu____6955);
                                      (let uu____6956 =
                                         let uu____6959 =
                                           let uu____6960 =
                                             FStar_TypeChecker_TcTerm.universe_of
                                               env typ
                                              in
                                           FStar_Syntax_Util.mk_eq2
                                             uu____6960 typ t2 ut
                                            in
                                         add_irrelevant_goal
                                           "rewrite_rec equation" env
                                           uu____6959 opts
                                          in
                                       bind uu____6956
                                         (fun uu____6967  ->
                                            let uu____6968 =
                                              bind rewriter
                                                (fun uu____6982  ->
                                                   let ut1 =
                                                     FStar_TypeChecker_Normalize.reduce_uvar_solutions
                                                       env ut
                                                      in
                                                   log ps
                                                     (fun uu____6988  ->
                                                        let uu____6989 =
                                                          FStar_Syntax_Print.term_to_string
                                                            t2
                                                           in
                                                        let uu____6990 =
                                                          FStar_Syntax_Print.term_to_string
                                                            ut1
                                                           in
                                                        FStar_Util.print2
                                                          "rewrite_rec: succeeded rewriting\n\t%s to\n\t%s\n"
                                                          uu____6989
                                                          uu____6990);
                                                   ret (ut1, ctrl1))
                                               in
                                            focus uu____6968))))))
  
let (topdown_rewrite :
  (FStar_Syntax_Syntax.term ->
     (Prims.bool,FStar_BigInt.t) FStar_Pervasives_Native.tuple2 tac)
    -> Prims.unit tac -> Prims.unit tac)
  =
  fun ctrl  ->
    fun rewriter  ->
      bind get
        (fun ps  ->
           let uu____7034 =
             match ps.FStar_Tactics_Types.goals with
             | g::gs -> (g, gs)
             | [] -> failwith "Pointwise: no goals"  in
           match uu____7034 with
           | (g,gs) ->
               let gt1 = g.FStar_Tactics_Types.goal_ty  in
               (log ps
                  (fun uu____7071  ->
                     let uu____7072 = FStar_Syntax_Print.term_to_string gt1
                        in
                     FStar_Util.print1 "Pointwise starting with %s\n"
                       uu____7072);
                bind dismiss_all
                  (fun uu____7075  ->
                     let uu____7076 =
                       ctrl_tac_fold
                         (rewrite_rec ps ctrl rewriter
                            g.FStar_Tactics_Types.opts)
                         g.FStar_Tactics_Types.context keepGoing gt1
                        in
                     bind uu____7076
                       (fun uu____7094  ->
                          match uu____7094 with
                          | (gt',uu____7102) ->
                              (log ps
                                 (fun uu____7106  ->
                                    let uu____7107 =
                                      FStar_Syntax_Print.term_to_string gt'
                                       in
                                    FStar_Util.print1
                                      "Pointwise seems to have succeded with %s\n"
                                      uu____7107);
                               (let uu____7108 = push_goals gs  in
                                bind uu____7108
                                  (fun uu____7112  ->
                                     add_goals
                                       [(let uu___112_7114 = g  in
                                         {
                                           FStar_Tactics_Types.context =
                                             (uu___112_7114.FStar_Tactics_Types.context);
                                           FStar_Tactics_Types.witness =
                                             (uu___112_7114.FStar_Tactics_Types.witness);
                                           FStar_Tactics_Types.goal_ty = gt';
                                           FStar_Tactics_Types.opts =
                                             (uu___112_7114.FStar_Tactics_Types.opts);
                                           FStar_Tactics_Types.is_guard =
                                             (uu___112_7114.FStar_Tactics_Types.is_guard)
                                         })])))))))
  
let (pointwise :
  FStar_Tactics_Types.direction -> Prims.unit tac -> Prims.unit tac) =
  fun d  ->
    fun tau  ->
      bind get
        (fun ps  ->
           let uu____7136 =
             match ps.FStar_Tactics_Types.goals with
             | g::gs -> (g, gs)
             | [] -> failwith "Pointwise: no goals"  in
           match uu____7136 with
           | (g,gs) ->
               let gt1 = g.FStar_Tactics_Types.goal_ty  in
               (log ps
                  (fun uu____7173  ->
                     let uu____7174 = FStar_Syntax_Print.term_to_string gt1
                        in
                     FStar_Util.print1 "Pointwise starting with %s\n"
                       uu____7174);
                bind dismiss_all
                  (fun uu____7177  ->
                     let uu____7178 =
                       tac_fold_env d
                         (pointwise_rec ps tau g.FStar_Tactics_Types.opts)
                         g.FStar_Tactics_Types.context gt1
                        in
                     bind uu____7178
                       (fun gt'  ->
                          log ps
                            (fun uu____7188  ->
                               let uu____7189 =
                                 FStar_Syntax_Print.term_to_string gt'  in
                               FStar_Util.print1
                                 "Pointwise seems to have succeded with %s\n"
                                 uu____7189);
                          (let uu____7190 = push_goals gs  in
                           bind uu____7190
                             (fun uu____7194  ->
                                add_goals
                                  [(let uu___113_7196 = g  in
                                    {
                                      FStar_Tactics_Types.context =
                                        (uu___113_7196.FStar_Tactics_Types.context);
                                      FStar_Tactics_Types.witness =
                                        (uu___113_7196.FStar_Tactics_Types.witness);
                                      FStar_Tactics_Types.goal_ty = gt';
                                      FStar_Tactics_Types.opts =
                                        (uu___113_7196.FStar_Tactics_Types.opts);
                                      FStar_Tactics_Types.is_guard =
                                        (uu___113_7196.FStar_Tactics_Types.is_guard)
                                    })]))))))
  
let (trefl : Prims.unit tac) =
  bind cur_goal
    (fun g  ->
       let uu____7216 =
         FStar_Syntax_Util.un_squash g.FStar_Tactics_Types.goal_ty  in
       match uu____7216 with
       | FStar_Pervasives_Native.Some t ->
           let uu____7228 = FStar_Syntax_Util.head_and_args' t  in
           (match uu____7228 with
            | (hd1,args) ->
                let uu____7261 =
                  let uu____7274 =
                    let uu____7275 = FStar_Syntax_Util.un_uinst hd1  in
                    uu____7275.FStar_Syntax_Syntax.n  in
                  (uu____7274, args)  in
                (match uu____7261 with
                 | (FStar_Syntax_Syntax.Tm_fvar
                    fv,uu____7289::(l,uu____7291)::(r,uu____7293)::[]) when
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Parser_Const.eq2_lid
                     ->
                     let uu____7340 =
                       do_unify g.FStar_Tactics_Types.context l r  in
                     bind uu____7340
                       (fun b  ->
                          if Prims.op_Negation b
                          then
                            let uu____7349 =
                              tts g.FStar_Tactics_Types.context l  in
                            let uu____7350 =
                              tts g.FStar_Tactics_Types.context r  in
                            fail2 "trefl: not a trivial equality (%s vs %s)"
                              uu____7349 uu____7350
                          else solve g FStar_Syntax_Util.exp_unit)
                 | (hd2,uu____7353) ->
                     let uu____7370 = tts g.FStar_Tactics_Types.context t  in
                     fail1 "trefl: not an equality (%s)" uu____7370))
       | FStar_Pervasives_Native.None  -> fail "not an irrelevant goal")
  
let (dup : Prims.unit tac) =
  bind cur_goal
    (fun g  ->
       let uu____7380 =
         new_uvar "dup" g.FStar_Tactics_Types.context
           g.FStar_Tactics_Types.goal_ty
          in
       bind uu____7380
         (fun u  ->
            let g' =
              let uu___114_7387 = g  in
              {
                FStar_Tactics_Types.context =
                  (uu___114_7387.FStar_Tactics_Types.context);
                FStar_Tactics_Types.witness = u;
                FStar_Tactics_Types.goal_ty =
                  (uu___114_7387.FStar_Tactics_Types.goal_ty);
                FStar_Tactics_Types.opts =
                  (uu___114_7387.FStar_Tactics_Types.opts);
                FStar_Tactics_Types.is_guard =
                  (uu___114_7387.FStar_Tactics_Types.is_guard)
              }  in
            bind dismiss
              (fun uu____7390  ->
                 let uu____7391 =
                   let uu____7394 =
                     let uu____7395 =
                       FStar_TypeChecker_TcTerm.universe_of
                         g.FStar_Tactics_Types.context
                         g.FStar_Tactics_Types.goal_ty
                        in
                     FStar_Syntax_Util.mk_eq2 uu____7395
                       g.FStar_Tactics_Types.goal_ty u
                       g.FStar_Tactics_Types.witness
                      in
                   add_irrelevant_goal "dup equation"
                     g.FStar_Tactics_Types.context uu____7394
                     g.FStar_Tactics_Types.opts
                    in
                 bind uu____7391
                   (fun uu____7398  ->
                      let uu____7399 = add_goals [g']  in
                      bind uu____7399 (fun uu____7403  -> ret ())))))
  
let (flip : Prims.unit tac) =
  bind get
    (fun ps  ->
       match ps.FStar_Tactics_Types.goals with
       | g1::g2::gs ->
           set
             (let uu___115_7422 = ps  in
              {
                FStar_Tactics_Types.main_context =
                  (uu___115_7422.FStar_Tactics_Types.main_context);
                FStar_Tactics_Types.main_goal =
                  (uu___115_7422.FStar_Tactics_Types.main_goal);
                FStar_Tactics_Types.all_implicits =
                  (uu___115_7422.FStar_Tactics_Types.all_implicits);
                FStar_Tactics_Types.goals = (g2 :: g1 :: gs);
                FStar_Tactics_Types.smt_goals =
                  (uu___115_7422.FStar_Tactics_Types.smt_goals);
                FStar_Tactics_Types.depth =
                  (uu___115_7422.FStar_Tactics_Types.depth);
                FStar_Tactics_Types.__dump =
                  (uu___115_7422.FStar_Tactics_Types.__dump);
                FStar_Tactics_Types.psc =
                  (uu___115_7422.FStar_Tactics_Types.psc);
                FStar_Tactics_Types.entry_range =
                  (uu___115_7422.FStar_Tactics_Types.entry_range);
                FStar_Tactics_Types.guard_policy =
                  (uu___115_7422.FStar_Tactics_Types.guard_policy)
              })
       | uu____7423 -> fail "flip: less than 2 goals")
  
let (later : Prims.unit tac) =
  bind get
    (fun ps  ->
       match ps.FStar_Tactics_Types.goals with
       | [] -> ret ()
       | g::gs ->
           set
             (let uu___116_7440 = ps  in
              {
                FStar_Tactics_Types.main_context =
                  (uu___116_7440.FStar_Tactics_Types.main_context);
                FStar_Tactics_Types.main_goal =
                  (uu___116_7440.FStar_Tactics_Types.main_goal);
                FStar_Tactics_Types.all_implicits =
                  (uu___116_7440.FStar_Tactics_Types.all_implicits);
                FStar_Tactics_Types.goals = (FStar_List.append gs [g]);
                FStar_Tactics_Types.smt_goals =
                  (uu___116_7440.FStar_Tactics_Types.smt_goals);
                FStar_Tactics_Types.depth =
                  (uu___116_7440.FStar_Tactics_Types.depth);
                FStar_Tactics_Types.__dump =
                  (uu___116_7440.FStar_Tactics_Types.__dump);
                FStar_Tactics_Types.psc =
                  (uu___116_7440.FStar_Tactics_Types.psc);
                FStar_Tactics_Types.entry_range =
                  (uu___116_7440.FStar_Tactics_Types.entry_range);
                FStar_Tactics_Types.guard_policy =
                  (uu___116_7440.FStar_Tactics_Types.guard_policy)
              }))
  
let (qed : Prims.unit tac) =
  bind get
    (fun ps  ->
       match ps.FStar_Tactics_Types.goals with
       | [] -> ret ()
       | uu____7449 -> fail "Not done!")
  
let (cases :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 tac)
  =
  fun t  ->
    let uu____7467 =
      bind cur_goal
        (fun g  ->
           let uu____7481 = __tc g.FStar_Tactics_Types.context t  in
           bind uu____7481
             (fun uu____7517  ->
                match uu____7517 with
                | (t1,typ,guard) ->
                    let uu____7533 = FStar_Syntax_Util.head_and_args typ  in
                    (match uu____7533 with
                     | (hd1,args) ->
                         let uu____7576 =
                           let uu____7589 =
                             let uu____7590 = FStar_Syntax_Util.un_uinst hd1
                                in
                             uu____7590.FStar_Syntax_Syntax.n  in
                           (uu____7589, args)  in
                         (match uu____7576 with
                          | (FStar_Syntax_Syntax.Tm_fvar
                             fv,(p,uu____7609)::(q,uu____7611)::[]) when
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
                                let uu___117_7649 = g  in
                                let uu____7650 =
                                  FStar_TypeChecker_Env.push_bv
                                    g.FStar_Tactics_Types.context v_p
                                   in
                                {
                                  FStar_Tactics_Types.context = uu____7650;
                                  FStar_Tactics_Types.witness =
                                    (uu___117_7649.FStar_Tactics_Types.witness);
                                  FStar_Tactics_Types.goal_ty =
                                    (uu___117_7649.FStar_Tactics_Types.goal_ty);
                                  FStar_Tactics_Types.opts =
                                    (uu___117_7649.FStar_Tactics_Types.opts);
                                  FStar_Tactics_Types.is_guard =
                                    (uu___117_7649.FStar_Tactics_Types.is_guard)
                                }  in
                              let g2 =
                                let uu___118_7652 = g  in
                                let uu____7653 =
                                  FStar_TypeChecker_Env.push_bv
                                    g.FStar_Tactics_Types.context v_q
                                   in
                                {
                                  FStar_Tactics_Types.context = uu____7653;
                                  FStar_Tactics_Types.witness =
                                    (uu___118_7652.FStar_Tactics_Types.witness);
                                  FStar_Tactics_Types.goal_ty =
                                    (uu___118_7652.FStar_Tactics_Types.goal_ty);
                                  FStar_Tactics_Types.opts =
                                    (uu___118_7652.FStar_Tactics_Types.opts);
                                  FStar_Tactics_Types.is_guard =
                                    (uu___118_7652.FStar_Tactics_Types.is_guard)
                                }  in
                              bind dismiss
                                (fun uu____7660  ->
                                   let uu____7661 = add_goals [g1; g2]  in
                                   bind uu____7661
                                     (fun uu____7670  ->
                                        let uu____7671 =
                                          let uu____7676 =
                                            FStar_Syntax_Syntax.bv_to_name
                                              v_p
                                             in
                                          let uu____7677 =
                                            FStar_Syntax_Syntax.bv_to_name
                                              v_q
                                             in
                                          (uu____7676, uu____7677)  in
                                        ret uu____7671))
                          | uu____7682 ->
                              let uu____7695 =
                                tts g.FStar_Tactics_Types.context typ  in
                              fail1 "Not a disjunction: %s" uu____7695))))
       in
    FStar_All.pipe_left (wrap_err "cases") uu____7467
  
let (set_options : Prims.string -> Prims.unit tac) =
  fun s  ->
    bind cur_goal
      (fun g  ->
         FStar_Options.push ();
         (let uu____7733 = FStar_Util.smap_copy g.FStar_Tactics_Types.opts
             in
          FStar_Options.set uu____7733);
         (let res = FStar_Options.set_options FStar_Options.Set s  in
          let opts' = FStar_Options.peek ()  in
          FStar_Options.pop ();
          (match res with
           | FStar_Getopt.Success  ->
               let g' =
                 let uu___119_7740 = g  in
                 {
                   FStar_Tactics_Types.context =
                     (uu___119_7740.FStar_Tactics_Types.context);
                   FStar_Tactics_Types.witness =
                     (uu___119_7740.FStar_Tactics_Types.witness);
                   FStar_Tactics_Types.goal_ty =
                     (uu___119_7740.FStar_Tactics_Types.goal_ty);
                   FStar_Tactics_Types.opts = opts';
                   FStar_Tactics_Types.is_guard =
                     (uu___119_7740.FStar_Tactics_Types.is_guard)
                 }  in
               replace_cur g'
           | FStar_Getopt.Error err ->
               fail2 "Setting options `%s` failed: %s" s err
           | FStar_Getopt.Help  ->
               fail1 "Setting options `%s` failed (got `Help`?)" s)))
  
let (top_env : FStar_TypeChecker_Env.env tac) =
  bind get
    (fun ps  -> FStar_All.pipe_left ret ps.FStar_Tactics_Types.main_context)
  
let (cur_env : FStar_TypeChecker_Env.env tac) =
  bind cur_goal
    (fun g  -> FStar_All.pipe_left ret g.FStar_Tactics_Types.context)
  
let (cur_goal' : FStar_Syntax_Syntax.typ tac) =
  bind cur_goal
    (fun g  -> FStar_All.pipe_left ret g.FStar_Tactics_Types.goal_ty)
  
let (cur_witness : FStar_Syntax_Syntax.term tac) =
  bind cur_goal
    (fun g  -> FStar_All.pipe_left ret g.FStar_Tactics_Types.witness)
  
let (unquote :
  FStar_Syntax_Syntax.typ ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term tac)
  =
  fun ty  ->
    fun tm  ->
      let uu____7784 =
        bind cur_goal
          (fun goal  ->
             let env =
               FStar_TypeChecker_Env.set_expected_typ
                 goal.FStar_Tactics_Types.context ty
                in
             let uu____7792 = __tc env tm  in
             bind uu____7792
               (fun uu____7812  ->
                  match uu____7812 with
                  | (tm1,typ,guard) ->
                      let uu____7824 =
                        proc_guard "unquote" env guard
                          goal.FStar_Tactics_Types.opts
                         in
                      bind uu____7824 (fun uu____7828  -> ret tm1)))
         in
      FStar_All.pipe_left (wrap_err "unquote") uu____7784
  
let (uvar_env :
  env ->
    FStar_Syntax_Syntax.typ FStar_Pervasives_Native.option ->
      FStar_Syntax_Syntax.term tac)
  =
  fun env  ->
    fun ty  ->
      let uu____7847 =
        match ty with
        | FStar_Pervasives_Native.Some ty1 -> ret ty1
        | FStar_Pervasives_Native.None  ->
            let uu____7853 =
              let uu____7854 = FStar_Syntax_Util.type_u ()  in
              FStar_All.pipe_left FStar_Pervasives_Native.fst uu____7854  in
            new_uvar "uvar_env.2" env uu____7853
         in
      bind uu____7847
        (fun typ  ->
           let uu____7866 = new_uvar "uvar_env" env typ  in
           bind uu____7866 (fun t  -> ret t))
  
let (unshelve : FStar_Syntax_Syntax.term -> Prims.unit tac) =
  fun t  ->
    let uu____7878 =
      bind get
        (fun ps  ->
           let env = ps.FStar_Tactics_Types.main_context  in
           let opts =
             match ps.FStar_Tactics_Types.goals with
             | g::uu____7889 -> g.FStar_Tactics_Types.opts
             | uu____7892 -> FStar_Options.peek ()  in
           let uu____7895 = __tc env t  in
           bind uu____7895
             (fun uu____7915  ->
                match uu____7915 with
                | (t1,typ,guard) ->
                    let uu____7927 = proc_guard "unshelve" env guard opts  in
                    bind uu____7927
                      (fun uu____7932  ->
                         let uu____7933 =
                           let uu____7936 =
                             let uu____7937 = bnorm env t1  in
                             let uu____7938 = bnorm env typ  in
                             {
                               FStar_Tactics_Types.context = env;
                               FStar_Tactics_Types.witness = uu____7937;
                               FStar_Tactics_Types.goal_ty = uu____7938;
                               FStar_Tactics_Types.opts = opts;
                               FStar_Tactics_Types.is_guard = false
                             }  in
                           [uu____7936]  in
                         add_goals uu____7933)))
       in
    FStar_All.pipe_left (wrap_err "unshelve") uu____7878
  
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
          (fun uu____7971  ->
             let uu____7972 = FStar_Options.unsafe_tactic_exec ()  in
             if uu____7972
             then
               let s =
                 FStar_Util.launch_process true "tactic_launch" prog args
                   input (fun uu____7978  -> fun uu____7979  -> false)
                  in
               ret s
             else
               fail
                 "launch_process: will not run anything unless --unsafe_tactic_exec is provided")
  
let (fresh_bv_named :
  Prims.string -> FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.bv tac) =
  fun nm  ->
    fun t  ->
      bind idtac
        (fun uu____7993  ->
           let uu____7994 =
             FStar_Syntax_Syntax.gen_bv nm FStar_Pervasives_Native.None t  in
           ret uu____7994)
  
let (change : FStar_Syntax_Syntax.typ -> Prims.unit tac) =
  fun ty  ->
    let uu____8002 =
      mlog
        (fun uu____8007  ->
           let uu____8008 = FStar_Syntax_Print.term_to_string ty  in
           FStar_Util.print1 "change: ty = %s\n" uu____8008)
        (fun uu____8010  ->
           bind cur_goal
             (fun g  ->
                let uu____8014 = __tc g.FStar_Tactics_Types.context ty  in
                bind uu____8014
                  (fun uu____8034  ->
                     match uu____8034 with
                     | (ty1,uu____8044,guard) ->
                         let uu____8046 =
                           proc_guard "change" g.FStar_Tactics_Types.context
                             guard g.FStar_Tactics_Types.opts
                            in
                         bind uu____8046
                           (fun uu____8051  ->
                              let uu____8052 =
                                do_unify g.FStar_Tactics_Types.context
                                  g.FStar_Tactics_Types.goal_ty ty1
                                 in
                              bind uu____8052
                                (fun bb  ->
                                   if bb
                                   then
                                     replace_cur
                                       (let uu___120_8061 = g  in
                                        {
                                          FStar_Tactics_Types.context =
                                            (uu___120_8061.FStar_Tactics_Types.context);
                                          FStar_Tactics_Types.witness =
                                            (uu___120_8061.FStar_Tactics_Types.witness);
                                          FStar_Tactics_Types.goal_ty = ty1;
                                          FStar_Tactics_Types.opts =
                                            (uu___120_8061.FStar_Tactics_Types.opts);
                                          FStar_Tactics_Types.is_guard =
                                            (uu___120_8061.FStar_Tactics_Types.is_guard)
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
                                      let uu____8068 =
                                        do_unify
                                          g.FStar_Tactics_Types.context ng
                                          nty
                                         in
                                      bind uu____8068
                                        (fun b  ->
                                           if b
                                           then
                                             replace_cur
                                               (let uu___121_8077 = g  in
                                                {
                                                  FStar_Tactics_Types.context
                                                    =
                                                    (uu___121_8077.FStar_Tactics_Types.context);
                                                  FStar_Tactics_Types.witness
                                                    =
                                                    (uu___121_8077.FStar_Tactics_Types.witness);
                                                  FStar_Tactics_Types.goal_ty
                                                    = ty1;
                                                  FStar_Tactics_Types.opts =
                                                    (uu___121_8077.FStar_Tactics_Types.opts);
                                                  FStar_Tactics_Types.is_guard
                                                    =
                                                    (uu___121_8077.FStar_Tactics_Types.is_guard)
                                                })
                                           else fail "not convertible")))))))
       in
    FStar_All.pipe_left (wrap_err "change") uu____8002
  
let (goal_of_goal_ty :
  env ->
    FStar_Syntax_Syntax.typ ->
      (FStar_Tactics_Types.goal,FStar_TypeChecker_Env.guard_t)
        FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun typ  ->
      let uu____8097 =
        FStar_TypeChecker_Util.new_implicit_var "proofstate_of_goal_ty"
          typ.FStar_Syntax_Syntax.pos env typ
         in
      match uu____8097 with
      | (u,uu____8115,g_u) ->
          let g =
            let uu____8130 = FStar_Options.peek ()  in
            {
              FStar_Tactics_Types.context = env;
              FStar_Tactics_Types.witness = u;
              FStar_Tactics_Types.goal_ty = typ;
              FStar_Tactics_Types.opts = uu____8130;
              FStar_Tactics_Types.is_guard = false
            }  in
          (g, g_u)
  
let (proofstate_of_goal_ty :
  env ->
    FStar_Syntax_Syntax.typ ->
      (FStar_Tactics_Types.proofstate,FStar_Syntax_Syntax.term)
        FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun typ  ->
      let uu____8141 = goal_of_goal_ty env typ  in
      match uu____8141 with
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
              FStar_Tactics_Types.guard_policy = FStar_Tactics_Types.SMT
            }  in
          (ps, (g.FStar_Tactics_Types.witness))
  