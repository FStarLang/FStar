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
  
let (comp_to_typ : FStar_Syntax_Syntax.comp -> FStar_Reflection_Data.typ) =
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
  
let (print : Prims.string -> Prims.unit tac) =
  fun msg  -> tacprint msg; ret () 
let dump_goal :
  'Auu____250 . 'Auu____250 -> FStar_Tactics_Types.goal -> Prims.unit =
  fun ps  ->
    fun goal  -> let uu____260 = goal_to_string goal  in tacprint uu____260
  
let (dump_cur : FStar_Tactics_Types.proofstate -> Prims.string -> Prims.unit)
  =
  fun ps  ->
    fun msg  ->
      match ps.FStar_Tactics_Types.goals with
      | [] -> tacprint1 "No more goals (%s)" msg
      | h::uu____268 ->
          (tacprint1 "Current goal (%s):" msg;
           (let uu____272 = FStar_List.hd ps.FStar_Tactics_Types.goals  in
            dump_goal ps uu____272))
  
let (ps_to_string :
  (Prims.string,FStar_Tactics_Types.proofstate)
    FStar_Pervasives_Native.tuple2 -> Prims.string)
  =
  fun uu____279  ->
    match uu____279 with
    | (msg,ps) ->
        let uu____286 =
          let uu____289 =
            let uu____290 =
              FStar_Util.string_of_int ps.FStar_Tactics_Types.depth  in
            FStar_Util.format2 "State dump @ depth %s (%s):\n" uu____290 msg
             in
          let uu____291 =
            let uu____294 =
              let uu____295 =
                FStar_Range.string_of_range
                  ps.FStar_Tactics_Types.entry_range
                 in
              FStar_Util.format1 "Location: %s\n" uu____295  in
            let uu____296 =
              let uu____299 =
                let uu____300 =
                  FStar_Util.string_of_int
                    (FStar_List.length ps.FStar_Tactics_Types.goals)
                   in
                let uu____301 =
                  let uu____302 =
                    FStar_List.map goal_to_string
                      ps.FStar_Tactics_Types.goals
                     in
                  FStar_String.concat "\n" uu____302  in
                FStar_Util.format2 "ACTIVE goals (%s):\n%s\n" uu____300
                  uu____301
                 in
              let uu____305 =
                let uu____308 =
                  let uu____309 =
                    FStar_Util.string_of_int
                      (FStar_List.length ps.FStar_Tactics_Types.smt_goals)
                     in
                  let uu____310 =
                    let uu____311 =
                      FStar_List.map goal_to_string
                        ps.FStar_Tactics_Types.smt_goals
                       in
                    FStar_String.concat "\n" uu____311  in
                  FStar_Util.format2 "SMT goals (%s):\n%s\n" uu____309
                    uu____310
                   in
                [uu____308]  in
              uu____299 :: uu____305  in
            uu____294 :: uu____296  in
          uu____289 :: uu____291  in
        FStar_String.concat "" uu____286
  
let (goal_to_json : FStar_Tactics_Types.goal -> FStar_Util.json) =
  fun g  ->
    let g_binders =
      let uu____318 =
        FStar_TypeChecker_Env.all_binders g.FStar_Tactics_Types.context  in
      let uu____319 =
        let uu____322 =
          FStar_TypeChecker_Env.dsenv g.FStar_Tactics_Types.context  in
        FStar_Syntax_Print.binders_to_json uu____322  in
      FStar_All.pipe_right uu____318 uu____319  in
    let uu____323 =
      let uu____330 =
        let uu____337 =
          let uu____342 =
            let uu____343 =
              let uu____350 =
                let uu____355 =
                  let uu____356 =
                    tts g.FStar_Tactics_Types.context
                      g.FStar_Tactics_Types.witness
                     in
                  FStar_Util.JsonStr uu____356  in
                ("witness", uu____355)  in
              let uu____357 =
                let uu____364 =
                  let uu____369 =
                    let uu____370 =
                      tts g.FStar_Tactics_Types.context
                        g.FStar_Tactics_Types.goal_ty
                       in
                    FStar_Util.JsonStr uu____370  in
                  ("type", uu____369)  in
                [uu____364]  in
              uu____350 :: uu____357  in
            FStar_Util.JsonAssoc uu____343  in
          ("goal", uu____342)  in
        [uu____337]  in
      ("hyps", g_binders) :: uu____330  in
    FStar_Util.JsonAssoc uu____323
  
let (ps_to_json :
  (Prims.string,FStar_Tactics_Types.proofstate)
    FStar_Pervasives_Native.tuple2 -> FStar_Util.json)
  =
  fun uu____401  ->
    match uu____401 with
    | (msg,ps) ->
        let uu____408 =
          let uu____415 =
            let uu____422 =
              let uu____429 =
                let uu____436 =
                  let uu____441 =
                    let uu____442 =
                      FStar_List.map goal_to_json
                        ps.FStar_Tactics_Types.goals
                       in
                    FStar_Util.JsonList uu____442  in
                  ("goals", uu____441)  in
                let uu____445 =
                  let uu____452 =
                    let uu____457 =
                      let uu____458 =
                        FStar_List.map goal_to_json
                          ps.FStar_Tactics_Types.smt_goals
                         in
                      FStar_Util.JsonList uu____458  in
                    ("smt-goals", uu____457)  in
                  [uu____452]  in
                uu____436 :: uu____445  in
              ("depth", (FStar_Util.JsonInt (ps.FStar_Tactics_Types.depth)))
                :: uu____429
               in
            ("label", (FStar_Util.JsonStr msg)) :: uu____422  in
          let uu____481 =
            if ps.FStar_Tactics_Types.entry_range <> FStar_Range.dummyRange
            then
              let uu____494 =
                let uu____499 =
                  FStar_Range.json_of_def_range
                    ps.FStar_Tactics_Types.entry_range
                   in
                ("location", uu____499)  in
              [uu____494]
            else []  in
          FStar_List.append uu____415 uu____481  in
        FStar_Util.JsonAssoc uu____408
  
let (dump_proofstate :
  FStar_Tactics_Types.proofstate -> Prims.string -> Prims.unit) =
  fun ps  ->
    fun msg  ->
      FStar_Options.with_saved_options
        (fun uu____525  ->
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
         (let uu____546 = FStar_Tactics_Types.subst_proof_state subst1 ps  in
          dump_cur uu____546 msg);
         FStar_Tactics_Result.Success ((), ps))
  
let (print_proof_state : Prims.string -> Prims.unit tac) =
  fun msg  ->
    mk_tac
      (fun ps  ->
         let psc = ps.FStar_Tactics_Types.psc  in
         let subst1 = FStar_TypeChecker_Normalize.psc_subst psc  in
         (let uu____562 = FStar_Tactics_Types.subst_proof_state subst1 ps  in
          dump_proofstate uu____562 msg);
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
      let uu____597 = FStar_ST.op_Bang tac_verb_dbg  in
      match uu____597 with
      | FStar_Pervasives_Native.None  ->
          ((let uu____624 =
              let uu____627 =
                FStar_TypeChecker_Env.debug
                  ps.FStar_Tactics_Types.main_context
                  (FStar_Options.Other "TacVerbose")
                 in
              FStar_Pervasives_Native.Some uu____627  in
            FStar_ST.op_Colon_Equals tac_verb_dbg uu____624);
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
         (let uu____696 =
            FStar_TypeChecker_Env.debug ps.FStar_Tactics_Types.main_context
              (FStar_Options.Other "TacFail")
             in
          if uu____696
          then dump_proofstate ps (Prims.strcat "TACTIC FAILING: " msg)
          else ());
         FStar_Tactics_Result.Failed (msg, ps))
  
let fail1 : 'Auu____701 . Prims.string -> Prims.string -> 'Auu____701 tac =
  fun msg  ->
    fun x  -> let uu____712 = FStar_Util.format1 msg x  in fail uu____712
  
let fail2 :
  'Auu____717 .
    Prims.string -> Prims.string -> Prims.string -> 'Auu____717 tac
  =
  fun msg  ->
    fun x  ->
      fun y  -> let uu____732 = FStar_Util.format2 msg x y  in fail uu____732
  
let fail3 :
  'Auu____738 .
    Prims.string ->
      Prims.string -> Prims.string -> Prims.string -> 'Auu____738 tac
  =
  fun msg  ->
    fun x  ->
      fun y  ->
        fun z  ->
          let uu____757 = FStar_Util.format3 msg x y z  in fail uu____757
  
let fail4 :
  'Auu____764 .
    Prims.string ->
      Prims.string ->
        Prims.string -> Prims.string -> Prims.string -> 'Auu____764 tac
  =
  fun msg  ->
    fun x  ->
      fun y  ->
        fun z  ->
          fun w  ->
            let uu____787 = FStar_Util.format4 msg x y z w  in fail uu____787
  
let trytac' : 'a . 'a tac -> (Prims.string,'a) FStar_Util.either tac =
  fun t  ->
    mk_tac
      (fun ps  ->
         let tx = FStar_Syntax_Unionfind.new_transaction ()  in
         let uu____817 = run t ps  in
         match uu____817 with
         | FStar_Tactics_Result.Success (a,q) ->
             (FStar_Syntax_Unionfind.commit tx;
              FStar_Tactics_Result.Success ((FStar_Util.Inr a), q))
         | FStar_Tactics_Result.Failed (m,q) ->
             (FStar_Syntax_Unionfind.rollback tx;
              (let ps1 =
                 let uu___119_841 = ps  in
                 {
                   FStar_Tactics_Types.main_context =
                     (uu___119_841.FStar_Tactics_Types.main_context);
                   FStar_Tactics_Types.main_goal =
                     (uu___119_841.FStar_Tactics_Types.main_goal);
                   FStar_Tactics_Types.all_implicits =
                     (uu___119_841.FStar_Tactics_Types.all_implicits);
                   FStar_Tactics_Types.goals =
                     (uu___119_841.FStar_Tactics_Types.goals);
                   FStar_Tactics_Types.smt_goals =
                     (uu___119_841.FStar_Tactics_Types.smt_goals);
                   FStar_Tactics_Types.depth =
                     (uu___119_841.FStar_Tactics_Types.depth);
                   FStar_Tactics_Types.__dump =
                     (uu___119_841.FStar_Tactics_Types.__dump);
                   FStar_Tactics_Types.psc =
                     (uu___119_841.FStar_Tactics_Types.psc);
                   FStar_Tactics_Types.entry_range =
                     (uu___119_841.FStar_Tactics_Types.entry_range);
                   FStar_Tactics_Types.guard_policy =
                     (uu___119_841.FStar_Tactics_Types.guard_policy);
                   FStar_Tactics_Types.freshness =
                     (q.FStar_Tactics_Types.freshness)
                 }  in
               FStar_Tactics_Result.Success ((FStar_Util.Inl m), ps1))))
  
let trytac : 'a . 'a tac -> 'a FStar_Pervasives_Native.option tac =
  fun t  ->
    let uu____865 = trytac' t  in
    bind uu____865
      (fun r  ->
         match r with
         | FStar_Util.Inr v1 -> ret (FStar_Pervasives_Native.Some v1)
         | FStar_Util.Inl uu____892 -> ret FStar_Pervasives_Native.None)
  
let trytac_exn : 'a . 'a tac -> 'a FStar_Pervasives_Native.option tac =
  fun t  ->
    mk_tac
      (fun ps  ->
         try let uu____925 = trytac t  in run uu____925 ps
         with
         | FStar_Errors.Err (uu____941,msg) ->
             (log ps
                (fun uu____945  ->
                   FStar_Util.print1 "trytac_exn error: (%s)" msg);
              FStar_Tactics_Result.Success (FStar_Pervasives_Native.None, ps))
         | FStar_Errors.Error (uu____950,msg,uu____952) ->
             (log ps
                (fun uu____955  ->
                   FStar_Util.print1 "trytac_exn error: (%s)" msg);
              FStar_Tactics_Result.Success (FStar_Pervasives_Native.None, ps)))
  
let wrap_err : 'a . Prims.string -> 'a tac -> 'a tac =
  fun pref  ->
    fun t  ->
      mk_tac
        (fun ps  ->
           let uu____983 = run t ps  in
           match uu____983 with
           | FStar_Tactics_Result.Success (a,q) ->
               FStar_Tactics_Result.Success (a, q)
           | FStar_Tactics_Result.Failed (msg,q) ->
               FStar_Tactics_Result.Failed
                 ((Prims.strcat pref (Prims.strcat ": " msg)), q))
  
let (set : FStar_Tactics_Types.proofstate -> Prims.unit tac) =
  fun p  -> mk_tac (fun uu____1000  -> FStar_Tactics_Result.Success ((), p)) 
let (__do_unify :
  env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.bool tac)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let debug_on uu____1017 =
          let uu____1018 =
            FStar_Options.set_options FStar_Options.Set
              "--debug_level Rel --debug_level RelCheck"
             in
          ()  in
        let debug_off uu____1022 =
          let uu____1023 = FStar_Options.set_options FStar_Options.Reset ""
             in
          ()  in
        (let uu____1025 =
           FStar_TypeChecker_Env.debug env (FStar_Options.Other "1346")  in
         if uu____1025
         then
           (debug_on ();
            (let uu____1027 = FStar_Syntax_Print.term_to_string t1  in
             let uu____1028 = FStar_Syntax_Print.term_to_string t2  in
             FStar_Util.print2 "%%%%%%%%do_unify %s =? %s\n" uu____1027
               uu____1028))
         else ());
        (try
           let res = FStar_TypeChecker_Rel.teq_nosmt env t1 t2  in
           debug_off ();
           (let uu____1042 =
              FStar_TypeChecker_Env.debug env (FStar_Options.Other "1346")
               in
            if uu____1042
            then
              let uu____1043 = FStar_Util.string_of_bool res  in
              let uu____1044 = FStar_Syntax_Print.term_to_string t1  in
              let uu____1045 = FStar_Syntax_Print.term_to_string t2  in
              FStar_Util.print3 "%%%%%%%%do_unify (RESULT %s) %s =? %s\n"
                uu____1043 uu____1044 uu____1045
            else ());
           ret res
         with
         | FStar_Errors.Err (uu____1054,msg) ->
             (debug_off ();
              mlog
                (fun uu____1058  ->
                   FStar_Util.print1 ">> do_unify error, (%s)\n" msg)
                (fun uu____1060  -> ret false))
         | FStar_Errors.Error (uu____1061,msg,r) ->
             (debug_off ();
              mlog
                (fun uu____1067  ->
                   let uu____1068 = FStar_Range.string_of_range r  in
                   FStar_Util.print2 ">> do_unify error, (%s) at (%s)\n" msg
                     uu____1068) (fun uu____1070  -> ret false)))
  
let (do_unify :
  env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.bool tac)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____1084 = __do_unify env t1 t2  in
        bind uu____1084
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
       let uu____1111 =
         let uu___124_1112 = p  in
         let uu____1113 = FStar_List.tl p.FStar_Tactics_Types.goals  in
         {
           FStar_Tactics_Types.main_context =
             (uu___124_1112.FStar_Tactics_Types.main_context);
           FStar_Tactics_Types.main_goal =
             (uu___124_1112.FStar_Tactics_Types.main_goal);
           FStar_Tactics_Types.all_implicits =
             (uu___124_1112.FStar_Tactics_Types.all_implicits);
           FStar_Tactics_Types.goals = uu____1113;
           FStar_Tactics_Types.smt_goals =
             (uu___124_1112.FStar_Tactics_Types.smt_goals);
           FStar_Tactics_Types.depth =
             (uu___124_1112.FStar_Tactics_Types.depth);
           FStar_Tactics_Types.__dump =
             (uu___124_1112.FStar_Tactics_Types.__dump);
           FStar_Tactics_Types.psc = (uu___124_1112.FStar_Tactics_Types.psc);
           FStar_Tactics_Types.entry_range =
             (uu___124_1112.FStar_Tactics_Types.entry_range);
           FStar_Tactics_Types.guard_policy =
             (uu___124_1112.FStar_Tactics_Types.guard_policy);
           FStar_Tactics_Types.freshness =
             (uu___124_1112.FStar_Tactics_Types.freshness)
         }  in
       set uu____1111)
  
let (dismiss : Prims.unit -> Prims.unit tac) =
  fun uu____1120  ->
    bind get
      (fun p  ->
         match p.FStar_Tactics_Types.goals with
         | [] -> fail "dismiss: no more goals"
         | uu____1127 -> __dismiss)
  
let (solve :
  FStar_Tactics_Types.goal -> FStar_Syntax_Syntax.term -> Prims.unit tac) =
  fun goal  ->
    fun solution  ->
      let uu____1140 = trysolve goal solution  in
      bind uu____1140
        (fun b  ->
           if b
           then __dismiss
           else
             (let uu____1148 =
                let uu____1149 =
                  tts goal.FStar_Tactics_Types.context solution  in
                let uu____1150 =
                  tts goal.FStar_Tactics_Types.context
                    goal.FStar_Tactics_Types.witness
                   in
                let uu____1151 =
                  tts goal.FStar_Tactics_Types.context
                    goal.FStar_Tactics_Types.goal_ty
                   in
                FStar_Util.format3 "%s does not solve %s : %s" uu____1149
                  uu____1150 uu____1151
                 in
              fail uu____1148))
  
let (dismiss_all : Prims.unit tac) =
  bind get
    (fun p  ->
       set
         (let uu___125_1158 = p  in
          {
            FStar_Tactics_Types.main_context =
              (uu___125_1158.FStar_Tactics_Types.main_context);
            FStar_Tactics_Types.main_goal =
              (uu___125_1158.FStar_Tactics_Types.main_goal);
            FStar_Tactics_Types.all_implicits =
              (uu___125_1158.FStar_Tactics_Types.all_implicits);
            FStar_Tactics_Types.goals = [];
            FStar_Tactics_Types.smt_goals =
              (uu___125_1158.FStar_Tactics_Types.smt_goals);
            FStar_Tactics_Types.depth =
              (uu___125_1158.FStar_Tactics_Types.depth);
            FStar_Tactics_Types.__dump =
              (uu___125_1158.FStar_Tactics_Types.__dump);
            FStar_Tactics_Types.psc = (uu___125_1158.FStar_Tactics_Types.psc);
            FStar_Tactics_Types.entry_range =
              (uu___125_1158.FStar_Tactics_Types.entry_range);
            FStar_Tactics_Types.guard_policy =
              (uu___125_1158.FStar_Tactics_Types.guard_policy);
            FStar_Tactics_Types.freshness =
              (uu___125_1158.FStar_Tactics_Types.freshness)
          }))
  
let (nwarn : Prims.int FStar_ST.ref) =
  FStar_Util.mk_ref (Prims.parse_int "0") 
let (check_valid_goal : FStar_Tactics_Types.goal -> Prims.unit) =
  fun g  ->
    let uu____1175 = FStar_Options.defensive ()  in
    if uu____1175
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
        let uu____1187 = FStar_TypeChecker_Env.pop_bv e  in
        match uu____1187 with
        | FStar_Pervasives_Native.None  -> b3
        | FStar_Pervasives_Native.Some (bv,e1) ->
            let b4 =
              b3 &&
                (FStar_TypeChecker_Env.closed e1 bv.FStar_Syntax_Syntax.sort)
               in
            aux b4 e1
         in
      let uu____1205 =
        (let uu____1208 = aux b2 env  in Prims.op_Negation uu____1208) &&
          (let uu____1210 = FStar_ST.op_Bang nwarn  in
           uu____1210 < (Prims.parse_int "5"))
         in
      (if uu____1205
       then
         ((let uu____1231 =
             let uu____1236 =
               let uu____1237 = goal_to_string g  in
               FStar_Util.format1
                 "The following goal is ill-formed. Keeping calm and carrying on...\n<%s>\n\n"
                 uu____1237
                in
             (FStar_Errors.Warning_IllFormedGoal, uu____1236)  in
           FStar_Errors.log_issue
             (g.FStar_Tactics_Types.goal_ty).FStar_Syntax_Syntax.pos
             uu____1231);
          (let uu____1238 =
             let uu____1239 = FStar_ST.op_Bang nwarn  in
             uu____1239 + (Prims.parse_int "1")  in
           FStar_ST.op_Colon_Equals nwarn uu____1238))
       else ())
    else ()
  
let (add_goals : FStar_Tactics_Types.goal Prims.list -> Prims.unit tac) =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___126_1297 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___126_1297.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___126_1297.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___126_1297.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (FStar_List.append gs p.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (uu___126_1297.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___126_1297.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___126_1297.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___126_1297.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___126_1297.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___126_1297.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___126_1297.FStar_Tactics_Types.freshness)
            }))
  
let (add_smt_goals : FStar_Tactics_Types.goal Prims.list -> Prims.unit tac) =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___127_1315 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___127_1315.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___127_1315.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___127_1315.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___127_1315.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (FStar_List.append gs p.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___127_1315.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___127_1315.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___127_1315.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___127_1315.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___127_1315.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___127_1315.FStar_Tactics_Types.freshness)
            }))
  
let (push_goals : FStar_Tactics_Types.goal Prims.list -> Prims.unit tac) =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___128_1333 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___128_1333.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___128_1333.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___128_1333.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (FStar_List.append p.FStar_Tactics_Types.goals gs);
              FStar_Tactics_Types.smt_goals =
                (uu___128_1333.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___128_1333.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___128_1333.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___128_1333.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___128_1333.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___128_1333.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___128_1333.FStar_Tactics_Types.freshness)
            }))
  
let (push_smt_goals : FStar_Tactics_Types.goal Prims.list -> Prims.unit tac)
  =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___129_1351 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___129_1351.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___129_1351.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___129_1351.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___129_1351.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (FStar_List.append p.FStar_Tactics_Types.smt_goals gs);
              FStar_Tactics_Types.depth =
                (uu___129_1351.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___129_1351.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___129_1351.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___129_1351.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___129_1351.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___129_1351.FStar_Tactics_Types.freshness)
            }))
  
let (replace_cur : FStar_Tactics_Types.goal -> Prims.unit tac) =
  fun g  -> bind __dismiss (fun uu____1360  -> add_goals [g]) 
let (add_implicits : implicits -> Prims.unit tac) =
  fun i  ->
    bind get
      (fun p  ->
         set
           (let uu___130_1372 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___130_1372.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___130_1372.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (FStar_List.append i p.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___130_1372.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (uu___130_1372.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___130_1372.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___130_1372.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___130_1372.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___130_1372.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___130_1372.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___130_1372.FStar_Tactics_Types.freshness)
            }))
  
let (new_uvar :
  Prims.string ->
    env -> FStar_Reflection_Data.typ -> FStar_Syntax_Syntax.term tac)
  =
  fun reason  ->
    fun env  ->
      fun typ  ->
        let uu____1398 =
          FStar_TypeChecker_Util.new_implicit_var reason
            typ.FStar_Syntax_Syntax.pos env typ
           in
        match uu____1398 with
        | (u,uu____1414,g_u) ->
            let uu____1428 =
              add_implicits g_u.FStar_TypeChecker_Env.implicits  in
            bind uu____1428 (fun uu____1432  -> ret u)
  
let (is_true : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____1436 = FStar_Syntax_Util.un_squash t  in
    match uu____1436 with
    | FStar_Pervasives_Native.Some t' ->
        let uu____1446 =
          let uu____1447 = FStar_Syntax_Subst.compress t'  in
          uu____1447.FStar_Syntax_Syntax.n  in
        (match uu____1446 with
         | FStar_Syntax_Syntax.Tm_fvar fv ->
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.true_lid
         | uu____1451 -> false)
    | uu____1452 -> false
  
let (is_false : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____1460 = FStar_Syntax_Util.un_squash t  in
    match uu____1460 with
    | FStar_Pervasives_Native.Some t' ->
        let uu____1470 =
          let uu____1471 = FStar_Syntax_Subst.compress t'  in
          uu____1471.FStar_Syntax_Syntax.n  in
        (match uu____1470 with
         | FStar_Syntax_Syntax.Tm_fvar fv ->
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.false_lid
         | uu____1475 -> false)
    | uu____1476 -> false
  
let (cur_goal : Prims.unit -> FStar_Tactics_Types.goal tac) =
  fun uu____1485  ->
    bind get
      (fun p  ->
         match p.FStar_Tactics_Types.goals with
         | [] -> fail "No more goals (1)"
         | hd1::tl1 -> ret hd1)
  
let (tadmit : Prims.unit -> Prims.unit tac) =
  fun uu____1500  ->
    let uu____1503 =
      let uu____1506 = cur_goal ()  in
      bind uu____1506
        (fun g  ->
           (let uu____1513 =
              let uu____1518 =
                let uu____1519 = goal_to_string g  in
                FStar_Util.format1 "Tactics admitted goal <%s>\n\n"
                  uu____1519
                 in
              (FStar_Errors.Warning_TacAdmit, uu____1518)  in
            FStar_Errors.log_issue
              (g.FStar_Tactics_Types.goal_ty).FStar_Syntax_Syntax.pos
              uu____1513);
           solve g FStar_Syntax_Util.exp_unit)
       in
    FStar_All.pipe_left (wrap_err "tadmit") uu____1503
  
let (fresh : Prims.unit -> FStar_BigInt.t tac) =
  fun uu____1528  ->
    bind get
      (fun ps  ->
         let n1 = ps.FStar_Tactics_Types.freshness  in
         let ps1 =
           let uu___131_1538 = ps  in
           {
             FStar_Tactics_Types.main_context =
               (uu___131_1538.FStar_Tactics_Types.main_context);
             FStar_Tactics_Types.main_goal =
               (uu___131_1538.FStar_Tactics_Types.main_goal);
             FStar_Tactics_Types.all_implicits =
               (uu___131_1538.FStar_Tactics_Types.all_implicits);
             FStar_Tactics_Types.goals =
               (uu___131_1538.FStar_Tactics_Types.goals);
             FStar_Tactics_Types.smt_goals =
               (uu___131_1538.FStar_Tactics_Types.smt_goals);
             FStar_Tactics_Types.depth =
               (uu___131_1538.FStar_Tactics_Types.depth);
             FStar_Tactics_Types.__dump =
               (uu___131_1538.FStar_Tactics_Types.__dump);
             FStar_Tactics_Types.psc =
               (uu___131_1538.FStar_Tactics_Types.psc);
             FStar_Tactics_Types.entry_range =
               (uu___131_1538.FStar_Tactics_Types.entry_range);
             FStar_Tactics_Types.guard_policy =
               (uu___131_1538.FStar_Tactics_Types.guard_policy);
             FStar_Tactics_Types.freshness = (n1 + (Prims.parse_int "1"))
           }  in
         let uu____1539 = set ps1  in
         bind uu____1539
           (fun uu____1544  ->
              let uu____1545 = FStar_BigInt.of_int_fs n1  in ret uu____1545))
  
let (ngoals : Prims.unit -> FStar_BigInt.t tac) =
  fun uu____1550  ->
    bind get
      (fun ps  ->
         let n1 = FStar_List.length ps.FStar_Tactics_Types.goals  in
         let uu____1558 = FStar_BigInt.of_int_fs n1  in ret uu____1558)
  
let (ngoals_smt : Prims.unit -> FStar_BigInt.t tac) =
  fun uu____1569  ->
    bind get
      (fun ps  ->
         let n1 = FStar_List.length ps.FStar_Tactics_Types.smt_goals  in
         let uu____1577 = FStar_BigInt.of_int_fs n1  in ret uu____1577)
  
let (is_guard : Prims.unit -> Prims.bool tac) =
  fun uu____1588  ->
    let uu____1591 = cur_goal ()  in
    bind uu____1591 (fun g  -> ret g.FStar_Tactics_Types.is_guard)
  
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
            let uu____1615 = env.FStar_TypeChecker_Env.universe_of env phi
               in
            FStar_Syntax_Util.mk_squash uu____1615 phi  in
          let uu____1616 = new_uvar reason env typ  in
          bind uu____1616
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
             (fun uu____1661  ->
                let uu____1662 = tts e t  in
                FStar_Util.print1 "Tac> __tc(%s)\n" uu____1662)
             (fun uu____1664  ->
                try
                  let uu____1684 =
                    (ps.FStar_Tactics_Types.main_context).FStar_TypeChecker_Env.type_of
                      e t
                     in
                  ret uu____1684
                with
                | FStar_Errors.Err (uu____1711,msg) ->
                    let uu____1713 = tts e t  in
                    let uu____1714 =
                      let uu____1715 = FStar_TypeChecker_Env.all_binders e
                         in
                      FStar_All.pipe_right uu____1715
                        (FStar_Syntax_Print.binders_to_string ", ")
                       in
                    fail3 "Cannot type %s in context (%s). Error = (%s)"
                      uu____1713 uu____1714 msg
                | FStar_Errors.Error (uu____1722,msg,uu____1724) ->
                    let uu____1725 = tts e t  in
                    let uu____1726 =
                      let uu____1727 = FStar_TypeChecker_Env.all_binders e
                         in
                      FStar_All.pipe_right uu____1727
                        (FStar_Syntax_Print.binders_to_string ", ")
                       in
                    fail3 "Cannot type %s in context (%s). Error = (%s)"
                      uu____1725 uu____1726 msg))
  
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
  fun uu____1748  ->
    bind get (fun ps  -> ret ps.FStar_Tactics_Types.guard_policy)
  
let (set_guard_policy : FStar_Tactics_Types.guard_policy -> Prims.unit tac) =
  fun pol  ->
    bind get
      (fun ps  ->
         set
           (let uu___134_1764 = ps  in
            {
              FStar_Tactics_Types.main_context =
                (uu___134_1764.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___134_1764.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___134_1764.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___134_1764.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (uu___134_1764.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___134_1764.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___134_1764.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___134_1764.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___134_1764.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy = pol;
              FStar_Tactics_Types.freshness =
                (uu___134_1764.FStar_Tactics_Types.freshness)
            }))
  
let with_policy : 'a . FStar_Tactics_Types.guard_policy -> 'a tac -> 'a tac =
  fun pol  ->
    fun t  ->
      let uu____1783 = get_guard_policy ()  in
      bind uu____1783
        (fun old_pol  ->
           let uu____1789 = set_guard_policy pol  in
           bind uu____1789
             (fun uu____1793  ->
                bind t
                  (fun r  ->
                     let uu____1797 = set_guard_policy old_pol  in
                     bind uu____1797 (fun uu____1801  -> ret r))))
  
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
          let uu____1818 =
            let uu____1819 = FStar_TypeChecker_Rel.simplify_guard e g  in
            uu____1819.FStar_TypeChecker_Env.guard_f  in
          match uu____1818 with
          | FStar_TypeChecker_Common.Trivial  -> ret ()
          | FStar_TypeChecker_Common.NonTrivial f ->
              let uu____1823 = istrivial e f  in
              if uu____1823
              then ret ()
              else
                bind get
                  (fun ps  ->
                     match ps.FStar_Tactics_Types.guard_policy with
                     | FStar_Tactics_Types.Drop  -> ret ()
                     | FStar_Tactics_Types.Goal  ->
                         let uu____1831 = mk_irrelevant_goal reason e f opts
                            in
                         bind uu____1831
                           (fun goal  ->
                              let goal1 =
                                let uu___135_1838 = goal  in
                                {
                                  FStar_Tactics_Types.context =
                                    (uu___135_1838.FStar_Tactics_Types.context);
                                  FStar_Tactics_Types.witness =
                                    (uu___135_1838.FStar_Tactics_Types.witness);
                                  FStar_Tactics_Types.goal_ty =
                                    (uu___135_1838.FStar_Tactics_Types.goal_ty);
                                  FStar_Tactics_Types.opts =
                                    (uu___135_1838.FStar_Tactics_Types.opts);
                                  FStar_Tactics_Types.is_guard = true
                                }  in
                              push_goals [goal1])
                     | FStar_Tactics_Types.SMT  ->
                         let uu____1839 = mk_irrelevant_goal reason e f opts
                            in
                         bind uu____1839
                           (fun goal  ->
                              let goal1 =
                                let uu___136_1846 = goal  in
                                {
                                  FStar_Tactics_Types.context =
                                    (uu___136_1846.FStar_Tactics_Types.context);
                                  FStar_Tactics_Types.witness =
                                    (uu___136_1846.FStar_Tactics_Types.witness);
                                  FStar_Tactics_Types.goal_ty =
                                    (uu___136_1846.FStar_Tactics_Types.goal_ty);
                                  FStar_Tactics_Types.opts =
                                    (uu___136_1846.FStar_Tactics_Types.opts);
                                  FStar_Tactics_Types.is_guard = true
                                }  in
                              push_smt_goals [goal1])
                     | FStar_Tactics_Types.Force  ->
                         (try
                            let uu____1854 =
                              let uu____1855 =
                                let uu____1856 =
                                  FStar_TypeChecker_Rel.discharge_guard_no_smt
                                    e g
                                   in
                                FStar_All.pipe_left
                                  FStar_TypeChecker_Rel.is_trivial uu____1856
                                 in
                              Prims.op_Negation uu____1855  in
                            if uu____1854
                            then
                              mlog
                                (fun uu____1861  ->
                                   let uu____1862 =
                                     FStar_TypeChecker_Rel.guard_to_string e
                                       g
                                      in
                                   FStar_Util.print1 "guard = %s\n"
                                     uu____1862)
                                (fun uu____1864  ->
                                   fail1 "Forcing the guard failed %s)"
                                     reason)
                            else ret ()
                          with
                          | uu____1871 ->
                              mlog
                                (fun uu____1874  ->
                                   let uu____1875 =
                                     FStar_TypeChecker_Rel.guard_to_string e
                                       g
                                      in
                                   FStar_Util.print1 "guard = %s\n"
                                     uu____1875)
                                (fun uu____1877  ->
                                   fail1 "Forcing the guard failed (%s)"
                                     reason)))
  
let (tc : FStar_Syntax_Syntax.term -> FStar_Reflection_Data.typ tac) =
  fun t  ->
    let uu____1885 =
      let uu____1888 = cur_goal ()  in
      bind uu____1888
        (fun goal  ->
           let uu____1894 = __tc goal.FStar_Tactics_Types.context t  in
           bind uu____1894
             (fun uu____1914  ->
                match uu____1914 with
                | (t1,typ,guard) ->
                    let uu____1926 =
                      proc_guard "tc" goal.FStar_Tactics_Types.context guard
                        goal.FStar_Tactics_Types.opts
                       in
                    bind uu____1926 (fun uu____1930  -> ret typ)))
       in
    FStar_All.pipe_left (wrap_err "tc") uu____1885
  
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
          let uu____1951 = mk_irrelevant_goal reason env phi opts  in
          bind uu____1951 (fun goal  -> add_goals [goal])
  
let (trivial : Prims.unit -> Prims.unit tac) =
  fun uu____1960  ->
    let uu____1963 = cur_goal ()  in
    bind uu____1963
      (fun goal  ->
         let uu____1969 =
           istrivial goal.FStar_Tactics_Types.context
             goal.FStar_Tactics_Types.goal_ty
            in
         if uu____1969
         then solve goal FStar_Syntax_Util.exp_unit
         else
           (let uu____1973 =
              tts goal.FStar_Tactics_Types.context
                goal.FStar_Tactics_Types.goal_ty
               in
            fail1 "Not a trivial goal: %s" uu____1973))
  
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
          let uu____1994 =
            let uu____1995 = FStar_TypeChecker_Rel.simplify_guard e g  in
            uu____1995.FStar_TypeChecker_Env.guard_f  in
          match uu____1994 with
          | FStar_TypeChecker_Common.Trivial  ->
              ret FStar_Pervasives_Native.None
          | FStar_TypeChecker_Common.NonTrivial f ->
              let uu____2003 = istrivial e f  in
              if uu____2003
              then ret FStar_Pervasives_Native.None
              else
                (let uu____2011 = mk_irrelevant_goal reason e f opts  in
                 bind uu____2011
                   (fun goal  ->
                      ret
                        (FStar_Pervasives_Native.Some
                           (let uu___139_2021 = goal  in
                            {
                              FStar_Tactics_Types.context =
                                (uu___139_2021.FStar_Tactics_Types.context);
                              FStar_Tactics_Types.witness =
                                (uu___139_2021.FStar_Tactics_Types.witness);
                              FStar_Tactics_Types.goal_ty =
                                (uu___139_2021.FStar_Tactics_Types.goal_ty);
                              FStar_Tactics_Types.opts =
                                (uu___139_2021.FStar_Tactics_Types.opts);
                              FStar_Tactics_Types.is_guard = true
                            }))))
  
let (smt : Prims.unit -> Prims.unit tac) =
  fun uu____2026  ->
    let uu____2029 = cur_goal ()  in
    bind uu____2029
      (fun g  ->
         let uu____2035 = is_irrelevant g  in
         if uu____2035
         then bind __dismiss (fun uu____2039  -> add_smt_goals [g])
         else
           (let uu____2041 =
              tts g.FStar_Tactics_Types.context g.FStar_Tactics_Types.goal_ty
               in
            fail1 "goal is not irrelevant: cannot dispatch to smt (%s)"
              uu____2041))
  
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
             let uu____2082 =
               try
                 let uu____2116 =
                   let uu____2125 = FStar_BigInt.to_int_fs n1  in
                   FStar_List.splitAt uu____2125 p.FStar_Tactics_Types.goals
                    in
                 ret uu____2116
               with | uu____2147 -> fail "divide: not enough goals"  in
             bind uu____2082
               (fun uu____2174  ->
                  match uu____2174 with
                  | (lgs,rgs) ->
                      let lp =
                        let uu___140_2200 = p  in
                        {
                          FStar_Tactics_Types.main_context =
                            (uu___140_2200.FStar_Tactics_Types.main_context);
                          FStar_Tactics_Types.main_goal =
                            (uu___140_2200.FStar_Tactics_Types.main_goal);
                          FStar_Tactics_Types.all_implicits =
                            (uu___140_2200.FStar_Tactics_Types.all_implicits);
                          FStar_Tactics_Types.goals = lgs;
                          FStar_Tactics_Types.smt_goals = [];
                          FStar_Tactics_Types.depth =
                            (uu___140_2200.FStar_Tactics_Types.depth);
                          FStar_Tactics_Types.__dump =
                            (uu___140_2200.FStar_Tactics_Types.__dump);
                          FStar_Tactics_Types.psc =
                            (uu___140_2200.FStar_Tactics_Types.psc);
                          FStar_Tactics_Types.entry_range =
                            (uu___140_2200.FStar_Tactics_Types.entry_range);
                          FStar_Tactics_Types.guard_policy =
                            (uu___140_2200.FStar_Tactics_Types.guard_policy);
                          FStar_Tactics_Types.freshness =
                            (uu___140_2200.FStar_Tactics_Types.freshness)
                        }  in
                      let rp =
                        let uu___141_2202 = p  in
                        {
                          FStar_Tactics_Types.main_context =
                            (uu___141_2202.FStar_Tactics_Types.main_context);
                          FStar_Tactics_Types.main_goal =
                            (uu___141_2202.FStar_Tactics_Types.main_goal);
                          FStar_Tactics_Types.all_implicits =
                            (uu___141_2202.FStar_Tactics_Types.all_implicits);
                          FStar_Tactics_Types.goals = rgs;
                          FStar_Tactics_Types.smt_goals = [];
                          FStar_Tactics_Types.depth =
                            (uu___141_2202.FStar_Tactics_Types.depth);
                          FStar_Tactics_Types.__dump =
                            (uu___141_2202.FStar_Tactics_Types.__dump);
                          FStar_Tactics_Types.psc =
                            (uu___141_2202.FStar_Tactics_Types.psc);
                          FStar_Tactics_Types.entry_range =
                            (uu___141_2202.FStar_Tactics_Types.entry_range);
                          FStar_Tactics_Types.guard_policy =
                            (uu___141_2202.FStar_Tactics_Types.guard_policy);
                          FStar_Tactics_Types.freshness =
                            (uu___141_2202.FStar_Tactics_Types.freshness)
                        }  in
                      let uu____2203 = set lp  in
                      bind uu____2203
                        (fun uu____2211  ->
                           bind l
                             (fun a  ->
                                bind get
                                  (fun lp'  ->
                                     let uu____2225 = set rp  in
                                     bind uu____2225
                                       (fun uu____2233  ->
                                          bind r
                                            (fun b  ->
                                               bind get
                                                 (fun rp'  ->
                                                    let p' =
                                                      let uu___142_2249 = p
                                                         in
                                                      {
                                                        FStar_Tactics_Types.main_context
                                                          =
                                                          (uu___142_2249.FStar_Tactics_Types.main_context);
                                                        FStar_Tactics_Types.main_goal
                                                          =
                                                          (uu___142_2249.FStar_Tactics_Types.main_goal);
                                                        FStar_Tactics_Types.all_implicits
                                                          =
                                                          (uu___142_2249.FStar_Tactics_Types.all_implicits);
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
                                                          (uu___142_2249.FStar_Tactics_Types.depth);
                                                        FStar_Tactics_Types.__dump
                                                          =
                                                          (uu___142_2249.FStar_Tactics_Types.__dump);
                                                        FStar_Tactics_Types.psc
                                                          =
                                                          (uu___142_2249.FStar_Tactics_Types.psc);
                                                        FStar_Tactics_Types.entry_range
                                                          =
                                                          (uu___142_2249.FStar_Tactics_Types.entry_range);
                                                        FStar_Tactics_Types.guard_policy
                                                          =
                                                          (uu___142_2249.FStar_Tactics_Types.guard_policy);
                                                        FStar_Tactics_Types.freshness
                                                          =
                                                          (uu___142_2249.FStar_Tactics_Types.freshness)
                                                      }  in
                                                    let uu____2250 = set p'
                                                       in
                                                    bind uu____2250
                                                      (fun uu____2258  ->
                                                         ret (a, b))))))))))
  
let focus : 'a . 'a tac -> 'a tac =
  fun f  ->
    let uu____2276 = divide FStar_BigInt.one f idtac  in
    bind uu____2276
      (fun uu____2289  -> match uu____2289 with | (a,()) -> ret a)
  
let rec map : 'a . 'a tac -> 'a Prims.list tac =
  fun tau  ->
    bind get
      (fun p  ->
         match p.FStar_Tactics_Types.goals with
         | [] -> ret []
         | uu____2323::uu____2324 ->
             let uu____2327 =
               let uu____2336 = map tau  in
               divide FStar_BigInt.one tau uu____2336  in
             bind uu____2327
               (fun uu____2354  ->
                  match uu____2354 with | (h,t) -> ret (h :: t)))
  
let (seq : Prims.unit tac -> Prims.unit tac -> Prims.unit tac) =
  fun t1  ->
    fun t2  ->
      let uu____2391 =
        bind t1
          (fun uu____2396  ->
             let uu____2397 = map t2  in
             bind uu____2397 (fun uu____2405  -> ret ()))
         in
      focus uu____2391
  
let (intro : Prims.unit -> FStar_Syntax_Syntax.binder tac) =
  fun uu____2412  ->
    let uu____2415 =
      let uu____2418 = cur_goal ()  in
      bind uu____2418
        (fun goal  ->
           let uu____2427 =
             FStar_Syntax_Util.arrow_one goal.FStar_Tactics_Types.goal_ty  in
           match uu____2427 with
           | FStar_Pervasives_Native.Some (b,c) ->
               let uu____2442 =
                 let uu____2443 = FStar_Syntax_Util.is_total_comp c  in
                 Prims.op_Negation uu____2443  in
               if uu____2442
               then fail "Codomain is effectful"
               else
                 (let env' =
                    FStar_TypeChecker_Env.push_binders
                      goal.FStar_Tactics_Types.context [b]
                     in
                  let typ' = comp_to_typ c  in
                  let uu____2449 = new_uvar "intro" env' typ'  in
                  bind uu____2449
                    (fun u  ->
                       let uu____2455 =
                         let uu____2458 =
                           FStar_Syntax_Util.abs [b] u
                             FStar_Pervasives_Native.None
                            in
                         trysolve goal uu____2458  in
                       bind uu____2455
                         (fun bb  ->
                            if bb
                            then
                              let uu____2464 =
                                let uu____2467 =
                                  let uu___145_2468 = goal  in
                                  let uu____2469 = bnorm env' u  in
                                  let uu____2470 = bnorm env' typ'  in
                                  {
                                    FStar_Tactics_Types.context = env';
                                    FStar_Tactics_Types.witness = uu____2469;
                                    FStar_Tactics_Types.goal_ty = uu____2470;
                                    FStar_Tactics_Types.opts =
                                      (uu___145_2468.FStar_Tactics_Types.opts);
                                    FStar_Tactics_Types.is_guard =
                                      (uu___145_2468.FStar_Tactics_Types.is_guard)
                                  }  in
                                replace_cur uu____2467  in
                              bind uu____2464 (fun uu____2472  -> ret b)
                            else fail "unification failed")))
           | FStar_Pervasives_Native.None  ->
               let uu____2478 =
                 tts goal.FStar_Tactics_Types.context
                   goal.FStar_Tactics_Types.goal_ty
                  in
               fail1 "goal is not an arrow (%s)" uu____2478)
       in
    FStar_All.pipe_left (wrap_err "intro") uu____2415
  
let (intro_rec :
  Prims.unit ->
    (FStar_Syntax_Syntax.binder,FStar_Syntax_Syntax.binder)
      FStar_Pervasives_Native.tuple2 tac)
  =
  fun uu____2491  ->
    let uu____2498 = cur_goal ()  in
    bind uu____2498
      (fun goal  ->
         FStar_Util.print_string
           "WARNING (intro_rec): calling this is known to cause normalizer loops\n";
         FStar_Util.print_string
           "WARNING (intro_rec): proceed at your own risk...\n";
         (let uu____2515 =
            FStar_Syntax_Util.arrow_one goal.FStar_Tactics_Types.goal_ty  in
          match uu____2515 with
          | FStar_Pervasives_Native.Some (b,c) ->
              let uu____2534 =
                let uu____2535 = FStar_Syntax_Util.is_total_comp c  in
                Prims.op_Negation uu____2535  in
              if uu____2534
              then fail "Codomain is effectful"
              else
                (let bv =
                   FStar_Syntax_Syntax.gen_bv "__recf"
                     FStar_Pervasives_Native.None
                     goal.FStar_Tactics_Types.goal_ty
                    in
                 let bs =
                   let uu____2551 = FStar_Syntax_Syntax.mk_binder bv  in
                   [uu____2551; b]  in
                 let env' =
                   FStar_TypeChecker_Env.push_binders
                     goal.FStar_Tactics_Types.context bs
                    in
                 let uu____2553 =
                   let uu____2556 = comp_to_typ c  in
                   new_uvar "intro_rec" env' uu____2556  in
                 bind uu____2553
                   (fun u  ->
                      let lb =
                        let uu____2571 =
                          FStar_Syntax_Util.abs [b] u
                            FStar_Pervasives_Native.None
                           in
                        FStar_Syntax_Util.mk_letbinding (FStar_Util.Inl bv)
                          [] goal.FStar_Tactics_Types.goal_ty
                          FStar_Parser_Const.effect_Tot_lid uu____2571 []
                          FStar_Range.dummyRange
                         in
                      let body = FStar_Syntax_Syntax.bv_to_name bv  in
                      let uu____2577 =
                        FStar_Syntax_Subst.close_let_rec [lb] body  in
                      match uu____2577 with
                      | (lbs,body1) ->
                          let tm =
                            FStar_Syntax_Syntax.mk
                              (FStar_Syntax_Syntax.Tm_let
                                 ((true, lbs), body1))
                              FStar_Pervasives_Native.None
                              (goal.FStar_Tactics_Types.witness).FStar_Syntax_Syntax.pos
                             in
                          let uu____2607 = trysolve goal tm  in
                          bind uu____2607
                            (fun bb  ->
                               if bb
                               then
                                 let uu____2623 =
                                   let uu____2626 =
                                     let uu___146_2627 = goal  in
                                     let uu____2628 = bnorm env' u  in
                                     let uu____2629 =
                                       let uu____2630 = comp_to_typ c  in
                                       bnorm env' uu____2630  in
                                     {
                                       FStar_Tactics_Types.context = env';
                                       FStar_Tactics_Types.witness =
                                         uu____2628;
                                       FStar_Tactics_Types.goal_ty =
                                         uu____2629;
                                       FStar_Tactics_Types.opts =
                                         (uu___146_2627.FStar_Tactics_Types.opts);
                                       FStar_Tactics_Types.is_guard =
                                         (uu___146_2627.FStar_Tactics_Types.is_guard)
                                     }  in
                                   replace_cur uu____2626  in
                                 bind uu____2623
                                   (fun uu____2637  ->
                                      let uu____2638 =
                                        let uu____2643 =
                                          FStar_Syntax_Syntax.mk_binder bv
                                           in
                                        (uu____2643, b)  in
                                      ret uu____2638)
                               else fail "intro_rec: unification failed")))
          | FStar_Pervasives_Native.None  ->
              let uu____2657 =
                tts goal.FStar_Tactics_Types.context
                  goal.FStar_Tactics_Types.goal_ty
                 in
              fail1 "intro_rec: goal is not an arrow (%s)" uu____2657))
  
let (norm : FStar_Syntax_Embeddings.norm_step Prims.list -> Prims.unit tac) =
  fun s  ->
    let uu____2673 = cur_goal ()  in
    bind uu____2673
      (fun goal  ->
         mlog
           (fun uu____2680  ->
              let uu____2681 =
                FStar_Syntax_Print.term_to_string
                  goal.FStar_Tactics_Types.witness
                 in
              FStar_Util.print1 "norm: witness = %s\n" uu____2681)
           (fun uu____2686  ->
              let steps =
                let uu____2690 = FStar_TypeChecker_Normalize.tr_norm_steps s
                   in
                FStar_List.append
                  [FStar_TypeChecker_Normalize.Reify;
                  FStar_TypeChecker_Normalize.UnfoldTac] uu____2690
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
                (let uu___147_2697 = goal  in
                 {
                   FStar_Tactics_Types.context =
                     (uu___147_2697.FStar_Tactics_Types.context);
                   FStar_Tactics_Types.witness = w;
                   FStar_Tactics_Types.goal_ty = t;
                   FStar_Tactics_Types.opts =
                     (uu___147_2697.FStar_Tactics_Types.opts);
                   FStar_Tactics_Types.is_guard =
                     (uu___147_2697.FStar_Tactics_Types.is_guard)
                 })))
  
let (norm_term_env :
  env ->
    FStar_Syntax_Embeddings.norm_step Prims.list ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term tac)
  =
  fun e  ->
    fun s  ->
      fun t  ->
        let uu____2715 =
          mlog
            (fun uu____2720  ->
               let uu____2721 = FStar_Syntax_Print.term_to_string t  in
               FStar_Util.print1 "norm_term: tm = %s\n" uu____2721)
            (fun uu____2723  ->
               bind get
                 (fun ps  ->
                    let opts =
                      match ps.FStar_Tactics_Types.goals with
                      | g::uu____2729 -> g.FStar_Tactics_Types.opts
                      | uu____2732 -> FStar_Options.peek ()  in
                    mlog
                      (fun uu____2737  ->
                         let uu____2738 =
                           tts ps.FStar_Tactics_Types.main_context t  in
                         FStar_Util.print1 "norm_term_env: t = %s\n"
                           uu____2738)
                      (fun uu____2741  ->
                         let uu____2742 = __tc e t  in
                         bind uu____2742
                           (fun uu____2763  ->
                              match uu____2763 with
                              | (t1,uu____2773,uu____2774) ->
                                  let steps =
                                    let uu____2778 =
                                      FStar_TypeChecker_Normalize.tr_norm_steps
                                        s
                                       in
                                    FStar_List.append
                                      [FStar_TypeChecker_Normalize.Reify;
                                      FStar_TypeChecker_Normalize.UnfoldTac]
                                      uu____2778
                                     in
                                  let t2 =
                                    normalize steps
                                      ps.FStar_Tactics_Types.main_context t1
                                     in
                                  ret t2))))
           in
        FStar_All.pipe_left (wrap_err "norm_term") uu____2715
  
let (refine_intro : Prims.unit -> Prims.unit tac) =
  fun uu____2790  ->
    let uu____2793 =
      let uu____2796 = cur_goal ()  in
      bind uu____2796
        (fun g  ->
           let uu____2803 =
             FStar_TypeChecker_Rel.base_and_refinement
               g.FStar_Tactics_Types.context g.FStar_Tactics_Types.goal_ty
              in
           match uu____2803 with
           | (uu____2816,FStar_Pervasives_Native.None ) ->
               fail "not a refinement"
           | (t,FStar_Pervasives_Native.Some (bv,phi)) ->
               let g1 =
                 let uu___148_2841 = g  in
                 {
                   FStar_Tactics_Types.context =
                     (uu___148_2841.FStar_Tactics_Types.context);
                   FStar_Tactics_Types.witness =
                     (uu___148_2841.FStar_Tactics_Types.witness);
                   FStar_Tactics_Types.goal_ty = t;
                   FStar_Tactics_Types.opts =
                     (uu___148_2841.FStar_Tactics_Types.opts);
                   FStar_Tactics_Types.is_guard =
                     (uu___148_2841.FStar_Tactics_Types.is_guard)
                 }  in
               let uu____2842 =
                 let uu____2847 =
                   let uu____2852 =
                     let uu____2853 = FStar_Syntax_Syntax.mk_binder bv  in
                     [uu____2853]  in
                   FStar_Syntax_Subst.open_term uu____2852 phi  in
                 match uu____2847 with
                 | (bvs,phi1) ->
                     let uu____2860 =
                       let uu____2861 = FStar_List.hd bvs  in
                       FStar_Pervasives_Native.fst uu____2861  in
                     (uu____2860, phi1)
                  in
               (match uu____2842 with
                | (bv1,phi1) ->
                    let uu____2874 =
                      let uu____2877 =
                        FStar_Syntax_Subst.subst
                          [FStar_Syntax_Syntax.NT
                             (bv1, (g.FStar_Tactics_Types.witness))] phi1
                         in
                      mk_irrelevant_goal "refine_intro refinement"
                        g.FStar_Tactics_Types.context uu____2877
                        g.FStar_Tactics_Types.opts
                       in
                    bind uu____2874
                      (fun g2  ->
                         bind __dismiss
                           (fun uu____2881  -> add_goals [g1; g2]))))
       in
    FStar_All.pipe_left (wrap_err "refine_intro") uu____2793
  
let (__exact_now : Prims.bool -> FStar_Syntax_Syntax.term -> Prims.unit tac)
  =
  fun set_expected_typ1  ->
    fun t  ->
      let uu____2896 = cur_goal ()  in
      bind uu____2896
        (fun goal  ->
           let env =
             if set_expected_typ1
             then
               FStar_TypeChecker_Env.set_expected_typ
                 goal.FStar_Tactics_Types.context
                 goal.FStar_Tactics_Types.goal_ty
             else goal.FStar_Tactics_Types.context  in
           let uu____2905 = __tc env t  in
           bind uu____2905
             (fun uu____2924  ->
                match uu____2924 with
                | (t1,typ,guard) ->
                    mlog
                      (fun uu____2939  ->
                         let uu____2940 =
                           tts goal.FStar_Tactics_Types.context typ  in
                         let uu____2941 =
                           FStar_TypeChecker_Rel.guard_to_string
                             goal.FStar_Tactics_Types.context guard
                            in
                         FStar_Util.print2
                           "__exact_now: got type %s\n__exact_now and guard %s\n"
                           uu____2940 uu____2941)
                      (fun uu____2944  ->
                         let uu____2945 =
                           proc_guard "__exact typing"
                             goal.FStar_Tactics_Types.context guard
                             goal.FStar_Tactics_Types.opts
                            in
                         bind uu____2945
                           (fun uu____2949  ->
                              mlog
                                (fun uu____2953  ->
                                   let uu____2954 =
                                     tts goal.FStar_Tactics_Types.context typ
                                      in
                                   let uu____2955 =
                                     tts goal.FStar_Tactics_Types.context
                                       goal.FStar_Tactics_Types.goal_ty
                                      in
                                   FStar_Util.print2
                                     "__exact_now: unifying %s and %s\n"
                                     uu____2954 uu____2955)
                                (fun uu____2958  ->
                                   let uu____2959 =
                                     do_unify
                                       goal.FStar_Tactics_Types.context typ
                                       goal.FStar_Tactics_Types.goal_ty
                                      in
                                   bind uu____2959
                                     (fun b  ->
                                        if b
                                        then solve goal t1
                                        else
                                          (let uu____2967 =
                                             tts
                                               goal.FStar_Tactics_Types.context
                                               t1
                                              in
                                           let uu____2968 =
                                             tts
                                               goal.FStar_Tactics_Types.context
                                               typ
                                              in
                                           let uu____2969 =
                                             tts
                                               goal.FStar_Tactics_Types.context
                                               goal.FStar_Tactics_Types.goal_ty
                                              in
                                           let uu____2970 =
                                             tts
                                               goal.FStar_Tactics_Types.context
                                               goal.FStar_Tactics_Types.witness
                                              in
                                           fail4
                                             "%s : %s does not exactly solve the goal %s (witness = %s)"
                                             uu____2967 uu____2968 uu____2969
                                             uu____2970)))))))
  
let (t_exact : Prims.bool -> FStar_Syntax_Syntax.term -> Prims.unit tac) =
  fun set_expected_typ1  ->
    fun tm  ->
      let uu____2981 =
        mlog
          (fun uu____2986  ->
             let uu____2987 = FStar_Syntax_Print.term_to_string tm  in
             FStar_Util.print1 "t_exact: tm = %s\n" uu____2987)
          (fun uu____2990  ->
             let uu____2991 =
               let uu____2998 = __exact_now set_expected_typ1 tm  in
               trytac' uu____2998  in
             bind uu____2991
               (fun uu___114_3007  ->
                  match uu___114_3007 with
                  | FStar_Util.Inr r -> ret ()
                  | FStar_Util.Inl e ->
                      let uu____3016 =
                        let uu____3023 =
                          let uu____3026 =
                            norm [FStar_Syntax_Embeddings.Delta]  in
                          bind uu____3026
                            (fun uu____3031  ->
                               let uu____3032 = refine_intro ()  in
                               bind uu____3032
                                 (fun uu____3036  ->
                                    __exact_now set_expected_typ1 tm))
                           in
                        trytac' uu____3023  in
                      bind uu____3016
                        (fun uu___113_3043  ->
                           match uu___113_3043 with
                           | FStar_Util.Inr r -> ret ()
                           | FStar_Util.Inl uu____3051 -> fail e)))
         in
      FStar_All.pipe_left (wrap_err "exact") uu____2981
  
let (uvar_free_in_goal :
  FStar_Syntax_Syntax.uvar -> FStar_Tactics_Types.goal -> Prims.bool) =
  fun u  ->
    fun g  ->
      if g.FStar_Tactics_Types.is_guard
      then false
      else
        (let free_uvars =
           let uu____3066 =
             let uu____3073 =
               FStar_Syntax_Free.uvars g.FStar_Tactics_Types.goal_ty  in
             FStar_Util.set_elements uu____3073  in
           FStar_List.map FStar_Pervasives_Native.fst uu____3066  in
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
          let uu____3133 = f x  in
          bind uu____3133
            (fun y  ->
               let uu____3141 = mapM f xs  in
               bind uu____3141 (fun ys  -> ret (y :: ys)))
  
exception NoUnif 
let (uu___is_NoUnif : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with | NoUnif  -> true | uu____3159 -> false
  
let rec (__apply :
  Prims.bool ->
    FStar_Syntax_Syntax.term -> FStar_Reflection_Data.typ -> Prims.unit tac)
  =
  fun uopt  ->
    fun tm  ->
      fun typ  ->
        let uu____3173 = cur_goal ()  in
        bind uu____3173
          (fun goal  ->
             mlog
               (fun uu____3180  ->
                  let uu____3181 = FStar_Syntax_Print.term_to_string tm  in
                  FStar_Util.print1 ">>> Calling __exact(%s)\n" uu____3181)
               (fun uu____3184  ->
                  let uu____3185 =
                    let uu____3190 =
                      let uu____3193 = t_exact false tm  in
                      with_policy FStar_Tactics_Types.Force uu____3193  in
                    trytac_exn uu____3190  in
                  bind uu____3185
                    (fun uu___115_3200  ->
                       match uu___115_3200 with
                       | FStar_Pervasives_Native.Some r -> ret ()
                       | FStar_Pervasives_Native.None  ->
                           mlog
                             (fun uu____3208  ->
                                let uu____3209 =
                                  FStar_Syntax_Print.term_to_string typ  in
                                FStar_Util.print1 ">>> typ = %s\n" uu____3209)
                             (fun uu____3212  ->
                                let uu____3213 =
                                  FStar_Syntax_Util.arrow_one typ  in
                                match uu____3213 with
                                | FStar_Pervasives_Native.None  ->
                                    FStar_Exn.raise NoUnif
                                | FStar_Pervasives_Native.Some ((bv,aq),c) ->
                                    mlog
                                      (fun uu____3245  ->
                                         let uu____3246 =
                                           FStar_Syntax_Print.binder_to_string
                                             (bv, aq)
                                            in
                                         FStar_Util.print1
                                           "__apply: pushing binder %s\n"
                                           uu____3246)
                                      (fun uu____3249  ->
                                         let uu____3250 =
                                           let uu____3251 =
                                             FStar_Syntax_Util.is_total_comp
                                               c
                                              in
                                           Prims.op_Negation uu____3251  in
                                         if uu____3250
                                         then
                                           fail "apply: not total codomain"
                                         else
                                           (let uu____3255 =
                                              new_uvar "apply"
                                                goal.FStar_Tactics_Types.context
                                                bv.FStar_Syntax_Syntax.sort
                                               in
                                            bind uu____3255
                                              (fun u  ->
                                                 let tm' =
                                                   FStar_Syntax_Syntax.mk_Tm_app
                                                     tm [(u, aq)]
                                                     FStar_Pervasives_Native.None
                                                     tm.FStar_Syntax_Syntax.pos
                                                    in
                                                 let typ' =
                                                   let uu____3275 =
                                                     comp_to_typ c  in
                                                   FStar_All.pipe_left
                                                     (FStar_Syntax_Subst.subst
                                                        [FStar_Syntax_Syntax.NT
                                                           (bv, u)])
                                                     uu____3275
                                                    in
                                                 let uu____3276 =
                                                   __apply uopt tm' typ'  in
                                                 bind uu____3276
                                                   (fun uu____3284  ->
                                                      let u1 =
                                                        bnorm
                                                          goal.FStar_Tactics_Types.context
                                                          u
                                                         in
                                                      let uu____3286 =
                                                        let uu____3287 =
                                                          let uu____3290 =
                                                            let uu____3291 =
                                                              FStar_Syntax_Util.head_and_args
                                                                u1
                                                               in
                                                            FStar_Pervasives_Native.fst
                                                              uu____3291
                                                             in
                                                          FStar_Syntax_Subst.compress
                                                            uu____3290
                                                           in
                                                        uu____3287.FStar_Syntax_Syntax.n
                                                         in
                                                      match uu____3286 with
                                                      | FStar_Syntax_Syntax.Tm_uvar
                                                          (uvar,uu____3319)
                                                          ->
                                                          bind get
                                                            (fun ps  ->
                                                               let uu____3347
                                                                 =
                                                                 uopt &&
                                                                   (uvar_free
                                                                    uvar ps)
                                                                  in
                                                               if uu____3347
                                                               then ret ()
                                                               else
                                                                 (let uu____3351
                                                                    =
                                                                    let uu____3354
                                                                    =
                                                                    let uu___149_3355
                                                                    = goal
                                                                     in
                                                                    let uu____3356
                                                                    =
                                                                    bnorm
                                                                    goal.FStar_Tactics_Types.context
                                                                    u1  in
                                                                    let uu____3357
                                                                    =
                                                                    bnorm
                                                                    goal.FStar_Tactics_Types.context
                                                                    bv.FStar_Syntax_Syntax.sort
                                                                     in
                                                                    {
                                                                    FStar_Tactics_Types.context
                                                                    =
                                                                    (uu___149_3355.FStar_Tactics_Types.context);
                                                                    FStar_Tactics_Types.witness
                                                                    =
                                                                    uu____3356;
                                                                    FStar_Tactics_Types.goal_ty
                                                                    =
                                                                    uu____3357;
                                                                    FStar_Tactics_Types.opts
                                                                    =
                                                                    (uu___149_3355.FStar_Tactics_Types.opts);
                                                                    FStar_Tactics_Types.is_guard
                                                                    = false
                                                                    }  in
                                                                    [uu____3354]
                                                                     in
                                                                  add_goals
                                                                    uu____3351))
                                                      | t -> ret ()))))))))
  
let try_unif : 'a . 'a tac -> 'a tac -> 'a tac =
  fun t  ->
    fun t'  -> mk_tac (fun ps  -> try run t ps with | NoUnif  -> run t' ps)
  
let (apply : Prims.bool -> FStar_Syntax_Syntax.term -> Prims.unit tac) =
  fun uopt  ->
    fun tm  ->
      let uu____3403 =
        mlog
          (fun uu____3408  ->
             let uu____3409 = FStar_Syntax_Print.term_to_string tm  in
             FStar_Util.print1 "apply: tm = %s\n" uu____3409)
          (fun uu____3412  ->
             let uu____3413 = cur_goal ()  in
             bind uu____3413
               (fun goal  ->
                  let uu____3419 = __tc goal.FStar_Tactics_Types.context tm
                     in
                  bind uu____3419
                    (fun uu____3441  ->
                       match uu____3441 with
                       | (tm1,typ,guard) ->
                           let typ1 =
                             bnorm goal.FStar_Tactics_Types.context typ  in
                           let uu____3454 =
                             let uu____3457 =
                               let uu____3460 = __apply uopt tm1 typ1  in
                               bind uu____3460
                                 (fun uu____3464  ->
                                    proc_guard "apply guard"
                                      goal.FStar_Tactics_Types.context guard
                                      goal.FStar_Tactics_Types.opts)
                                in
                             focus uu____3457  in
                           let uu____3465 =
                             let uu____3468 =
                               tts goal.FStar_Tactics_Types.context tm1  in
                             let uu____3469 =
                               tts goal.FStar_Tactics_Types.context typ1  in
                             let uu____3470 =
                               tts goal.FStar_Tactics_Types.context
                                 goal.FStar_Tactics_Types.goal_ty
                                in
                             fail3
                               "Cannot instantiate %s (of type %s) to match goal (%s)"
                               uu____3468 uu____3469 uu____3470
                              in
                           try_unif uu____3454 uu____3465)))
         in
      FStar_All.pipe_left (wrap_err "apply") uu____3403
  
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
      let uu____3497 =
        match ct.FStar_Syntax_Syntax.effect_args with
        | pre::post::uu____3516 ->
            ((FStar_Pervasives_Native.fst pre),
              (FStar_Pervasives_Native.fst post))
        | uu____3557 -> failwith "apply_lemma: impossible: not a lemma"  in
      match uu____3497 with
      | (pre,post) ->
          let post1 =
            let uu____3593 =
              let uu____3602 =
                FStar_Syntax_Syntax.as_arg FStar_Syntax_Util.exp_unit  in
              [uu____3602]  in
            FStar_Syntax_Util.mk_app post uu____3593  in
          FStar_Pervasives_Native.Some (pre, post1)
    else
      if FStar_Syntax_Util.is_pure_effect ct.FStar_Syntax_Syntax.effect_name
      then
        (let uu____3622 =
           FStar_Syntax_Util.un_squash ct.FStar_Syntax_Syntax.result_typ  in
         FStar_Util.map_opt uu____3622
           (fun post  -> (FStar_Syntax_Util.t_true, post)))
      else FStar_Pervasives_Native.None
  
let (apply_lemma : FStar_Syntax_Syntax.term -> Prims.unit tac) =
  fun tm  ->
    let uu____3653 =
      let uu____3656 =
        mlog
          (fun uu____3661  ->
             let uu____3662 = FStar_Syntax_Print.term_to_string tm  in
             FStar_Util.print1 "apply_lemma: tm = %s\n" uu____3662)
          (fun uu____3666  ->
             let is_unit_t t =
               let uu____3671 =
                 let uu____3672 = FStar_Syntax_Subst.compress t  in
                 uu____3672.FStar_Syntax_Syntax.n  in
               match uu____3671 with
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.unit_lid
                   -> true
               | uu____3676 -> false  in
             let uu____3677 = cur_goal ()  in
             bind uu____3677
               (fun goal  ->
                  let uu____3683 = __tc goal.FStar_Tactics_Types.context tm
                     in
                  bind uu____3683
                    (fun uu____3706  ->
                       match uu____3706 with
                       | (tm1,t,guard) ->
                           let uu____3718 =
                             FStar_Syntax_Util.arrow_formals_comp t  in
                           (match uu____3718 with
                            | (bs,comp) ->
                                let uu____3745 = lemma_or_sq comp  in
                                (match uu____3745 with
                                 | FStar_Pervasives_Native.None  ->
                                     fail "not a lemma or squashed function"
                                 | FStar_Pervasives_Native.Some (pre,post) ->
                                     let uu____3764 =
                                       FStar_List.fold_left
                                         (fun uu____3810  ->
                                            fun uu____3811  ->
                                              match (uu____3810, uu____3811)
                                              with
                                              | ((uvs,guard1,subst1),(b,aq))
                                                  ->
                                                  let b_t =
                                                    FStar_Syntax_Subst.subst
                                                      subst1
                                                      b.FStar_Syntax_Syntax.sort
                                                     in
                                                  let uu____3914 =
                                                    is_unit_t b_t  in
                                                  if uu____3914
                                                  then
                                                    (((FStar_Syntax_Util.exp_unit,
                                                        aq) :: uvs), guard1,
                                                      ((FStar_Syntax_Syntax.NT
                                                          (b,
                                                            FStar_Syntax_Util.exp_unit))
                                                      :: subst1))
                                                  else
                                                    (let uu____3952 =
                                                       FStar_TypeChecker_Util.new_implicit_var
                                                         "apply_lemma"
                                                         (goal.FStar_Tactics_Types.goal_ty).FStar_Syntax_Syntax.pos
                                                         goal.FStar_Tactics_Types.context
                                                         b_t
                                                        in
                                                     match uu____3952 with
                                                     | (u,uu____3982,g_u) ->
                                                         let uu____3996 =
                                                           FStar_TypeChecker_Rel.conj_guard
                                                             guard1 g_u
                                                            in
                                                         (((u, aq) :: uvs),
                                                           uu____3996,
                                                           ((FStar_Syntax_Syntax.NT
                                                               (b, u)) ::
                                                           subst1))))
                                         ([], guard, []) bs
                                        in
                                     (match uu____3764 with
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
                                          let uu____4067 =
                                            let uu____4070 =
                                              FStar_Syntax_Util.mk_squash
                                                FStar_Syntax_Syntax.U_zero
                                                post1
                                               in
                                            do_unify
                                              goal.FStar_Tactics_Types.context
                                              uu____4070
                                              goal.FStar_Tactics_Types.goal_ty
                                             in
                                          bind uu____4067
                                            (fun b  ->
                                               if Prims.op_Negation b
                                               then
                                                 let uu____4078 =
                                                   tts
                                                     goal.FStar_Tactics_Types.context
                                                     tm1
                                                    in
                                                 let uu____4079 =
                                                   let uu____4080 =
                                                     FStar_Syntax_Util.mk_squash
                                                       FStar_Syntax_Syntax.U_zero
                                                       post1
                                                      in
                                                   tts
                                                     goal.FStar_Tactics_Types.context
                                                     uu____4080
                                                    in
                                                 let uu____4081 =
                                                   tts
                                                     goal.FStar_Tactics_Types.context
                                                     goal.FStar_Tactics_Types.goal_ty
                                                    in
                                                 fail3
                                                   "Cannot instantiate lemma %s (with postcondition: %s) to match goal (%s)"
                                                   uu____4078 uu____4079
                                                   uu____4081
                                               else
                                                 (let uu____4083 =
                                                    add_implicits
                                                      implicits.FStar_TypeChecker_Env.implicits
                                                     in
                                                  bind uu____4083
                                                    (fun uu____4088  ->
                                                       let uu____4089 =
                                                         solve goal
                                                           FStar_Syntax_Util.exp_unit
                                                          in
                                                       bind uu____4089
                                                         (fun uu____4097  ->
                                                            let is_free_uvar
                                                              uv t1 =
                                                              let free_uvars
                                                                =
                                                                let uu____4108
                                                                  =
                                                                  let uu____4115
                                                                    =
                                                                    FStar_Syntax_Free.uvars
                                                                    t1  in
                                                                  FStar_Util.set_elements
                                                                    uu____4115
                                                                   in
                                                                FStar_List.map
                                                                  FStar_Pervasives_Native.fst
                                                                  uu____4108
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
                                                              let uu____4156
                                                                =
                                                                FStar_Syntax_Util.head_and_args
                                                                  t1
                                                                 in
                                                              match uu____4156
                                                              with
                                                              | (hd1,uu____4172)
                                                                  ->
                                                                  (match 
                                                                    hd1.FStar_Syntax_Syntax.n
                                                                   with
                                                                   | 
                                                                   FStar_Syntax_Syntax.Tm_uvar
                                                                    (uv,uu____4194)
                                                                    ->
                                                                    appears
                                                                    uv goals
                                                                   | 
                                                                   uu____4219
                                                                    -> false)
                                                               in
                                                            let uu____4220 =
                                                              FStar_All.pipe_right
                                                                implicits.FStar_TypeChecker_Env.implicits
                                                                (mapM
                                                                   (fun
                                                                    uu____4292
                                                                     ->
                                                                    match uu____4292
                                                                    with
                                                                    | 
                                                                    (_msg,env,_uvar,term,typ,uu____4320)
                                                                    ->
                                                                    let uu____4321
                                                                    =
                                                                    FStar_Syntax_Util.head_and_args
                                                                    term  in
                                                                    (match uu____4321
                                                                    with
                                                                    | 
                                                                    (hd1,uu____4347)
                                                                    ->
                                                                    let uu____4368
                                                                    =
                                                                    let uu____4369
                                                                    =
                                                                    FStar_Syntax_Subst.compress
                                                                    hd1  in
                                                                    uu____4369.FStar_Syntax_Syntax.n
                                                                     in
                                                                    (match uu____4368
                                                                    with
                                                                    | 
                                                                    FStar_Syntax_Syntax.Tm_uvar
                                                                    uu____4382
                                                                    ->
                                                                    let uu____4399
                                                                    =
                                                                    let uu____4408
                                                                    =
                                                                    let uu____4411
                                                                    =
                                                                    let uu___152_4412
                                                                    = goal
                                                                     in
                                                                    let uu____4413
                                                                    =
                                                                    bnorm
                                                                    goal.FStar_Tactics_Types.context
                                                                    term  in
                                                                    let uu____4414
                                                                    =
                                                                    bnorm
                                                                    goal.FStar_Tactics_Types.context
                                                                    typ  in
                                                                    {
                                                                    FStar_Tactics_Types.context
                                                                    =
                                                                    (uu___152_4412.FStar_Tactics_Types.context);
                                                                    FStar_Tactics_Types.witness
                                                                    =
                                                                    uu____4413;
                                                                    FStar_Tactics_Types.goal_ty
                                                                    =
                                                                    uu____4414;
                                                                    FStar_Tactics_Types.opts
                                                                    =
                                                                    (uu___152_4412.FStar_Tactics_Types.opts);
                                                                    FStar_Tactics_Types.is_guard
                                                                    =
                                                                    (uu___152_4412.FStar_Tactics_Types.is_guard)
                                                                    }  in
                                                                    [uu____4411]
                                                                     in
                                                                    (uu____4408,
                                                                    [])  in
                                                                    ret
                                                                    uu____4399
                                                                    | 
                                                                    uu____4427
                                                                    ->
                                                                    let g_typ
                                                                    =
                                                                    let uu____4429
                                                                    =
                                                                    FStar_Options.__temp_fast_implicits
                                                                    ()  in
                                                                    if
                                                                    uu____4429
                                                                    then
                                                                    FStar_TypeChecker_TcTerm.check_type_of_well_typed_term
                                                                    false env
                                                                    term typ
                                                                    else
                                                                    (let term1
                                                                    =
                                                                    bnorm env
                                                                    term  in
                                                                    let uu____4432
                                                                    =
                                                                    let uu____4439
                                                                    =
                                                                    FStar_TypeChecker_Env.set_expected_typ
                                                                    env typ
                                                                     in
                                                                    env.FStar_TypeChecker_Env.type_of
                                                                    uu____4439
                                                                    term1  in
                                                                    match uu____4432
                                                                    with
                                                                    | 
                                                                    (uu____4440,uu____4441,g_typ)
                                                                    -> g_typ)
                                                                     in
                                                                    let uu____4443
                                                                    =
                                                                    goal_from_guard
                                                                    "apply_lemma solved arg"
                                                                    goal.FStar_Tactics_Types.context
                                                                    g_typ
                                                                    goal.FStar_Tactics_Types.opts
                                                                     in
                                                                    bind
                                                                    uu____4443
                                                                    (fun
                                                                    uu___116_4459
                                                                     ->
                                                                    match uu___116_4459
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
                                                            bind uu____4220
                                                              (fun goals_  ->
                                                                 let sub_goals
                                                                   =
                                                                   let uu____4527
                                                                    =
                                                                    FStar_List.map
                                                                    FStar_Pervasives_Native.fst
                                                                    goals_
                                                                     in
                                                                   FStar_List.flatten
                                                                    uu____4527
                                                                    in
                                                                 let smt_goals
                                                                   =
                                                                   let uu____4549
                                                                    =
                                                                    FStar_List.map
                                                                    FStar_Pervasives_Native.snd
                                                                    goals_
                                                                     in
                                                                   FStar_List.flatten
                                                                    uu____4549
                                                                    in
                                                                 let rec filter'
                                                                   a f xs =
                                                                   match xs
                                                                   with
                                                                   | 
                                                                   [] -> []
                                                                   | 
                                                                   x::xs1 ->
                                                                    let uu____4604
                                                                    = f x xs1
                                                                     in
                                                                    if
                                                                    uu____4604
                                                                    then
                                                                    let uu____4607
                                                                    =
                                                                    filter'
                                                                    () f xs1
                                                                     in x ::
                                                                    uu____4607
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
                                                                    let uu____4621
                                                                    =
                                                                    checkone
                                                                    g.FStar_Tactics_Types.witness
                                                                    goals  in
                                                                    Prims.op_Negation
                                                                    uu____4621))
                                                                    a438 a439)
                                                                    (Obj.magic
                                                                    sub_goals))
                                                                    in
                                                                 let uu____4622
                                                                   =
                                                                   proc_guard
                                                                    "apply_lemma guard"
                                                                    goal.FStar_Tactics_Types.context
                                                                    guard
                                                                    goal.FStar_Tactics_Types.opts
                                                                    in
                                                                 bind
                                                                   uu____4622
                                                                   (fun
                                                                    uu____4627
                                                                     ->
                                                                    let uu____4628
                                                                    =
                                                                    let uu____4631
                                                                    =
                                                                    let uu____4632
                                                                    =
                                                                    let uu____4633
                                                                    =
                                                                    FStar_Syntax_Util.mk_squash
                                                                    FStar_Syntax_Syntax.U_zero
                                                                    pre1  in
                                                                    istrivial
                                                                    goal.FStar_Tactics_Types.context
                                                                    uu____4633
                                                                     in
                                                                    Prims.op_Negation
                                                                    uu____4632
                                                                     in
                                                                    if
                                                                    uu____4631
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
                                                                    uu____4628
                                                                    (fun
                                                                    uu____4639
                                                                     ->
                                                                    let uu____4640
                                                                    =
                                                                    add_smt_goals
                                                                    smt_goals
                                                                     in
                                                                    bind
                                                                    uu____4640
                                                                    (fun
                                                                    uu____4644
                                                                     ->
                                                                    add_goals
                                                                    sub_goals1))))))))))))))
         in
      focus uu____3656  in
    FStar_All.pipe_left (wrap_err "apply_lemma") uu____3653
  
let (destruct_eq' :
  FStar_Reflection_Data.typ ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun typ  ->
    let uu____4664 = FStar_Syntax_Util.destruct_typ_as_formula typ  in
    match uu____4664 with
    | FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn
        (l,uu____4674::(e1,uu____4676)::(e2,uu____4678)::[])) when
        FStar_Ident.lid_equals l FStar_Parser_Const.eq2_lid ->
        FStar_Pervasives_Native.Some (e1, e2)
    | uu____4737 -> FStar_Pervasives_Native.None
  
let (destruct_eq :
  FStar_Reflection_Data.typ ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun typ  ->
    let uu____4759 = destruct_eq' typ  in
    match uu____4759 with
    | FStar_Pervasives_Native.Some t -> FStar_Pervasives_Native.Some t
    | FStar_Pervasives_Native.None  ->
        let uu____4789 = FStar_Syntax_Util.un_squash typ  in
        (match uu____4789 with
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
        let uu____4845 = FStar_TypeChecker_Env.pop_bv e1  in
        match uu____4845 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (bv',e') ->
            if FStar_Syntax_Syntax.bv_eq bvar bv'
            then FStar_Pervasives_Native.Some (e', [])
            else
              (let uu____4893 = aux e'  in
               FStar_Util.map_opt uu____4893
                 (fun uu____4917  ->
                    match uu____4917 with | (e'',bvs) -> (e'', (bv' :: bvs))))
         in
      let uu____4938 = aux e  in
      FStar_Util.map_opt uu____4938
        (fun uu____4962  ->
           match uu____4962 with | (e',bvs) -> (e', (FStar_List.rev bvs)))
  
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
          let uu____5017 = split_env b1 g.FStar_Tactics_Types.context  in
          FStar_Util.map_opt uu____5017
            (fun uu____5041  ->
               match uu____5041 with
               | (e0,bvs) ->
                   let s1 bv =
                     let uu___153_5058 = bv  in
                     let uu____5059 =
                       FStar_Syntax_Subst.subst s bv.FStar_Syntax_Syntax.sort
                        in
                     {
                       FStar_Syntax_Syntax.ppname =
                         (uu___153_5058.FStar_Syntax_Syntax.ppname);
                       FStar_Syntax_Syntax.index =
                         (uu___153_5058.FStar_Syntax_Syntax.index);
                       FStar_Syntax_Syntax.sort = uu____5059
                     }  in
                   let bvs1 = FStar_List.map s1 bvs  in
                   let c = push_bvs e0 (b2 :: bvs1)  in
                   let w =
                     FStar_Syntax_Subst.subst s g.FStar_Tactics_Types.witness
                      in
                   let t =
                     FStar_Syntax_Subst.subst s g.FStar_Tactics_Types.goal_ty
                      in
                   let uu___154_5068 = g  in
                   {
                     FStar_Tactics_Types.context = c;
                     FStar_Tactics_Types.witness = w;
                     FStar_Tactics_Types.goal_ty = t;
                     FStar_Tactics_Types.opts =
                       (uu___154_5068.FStar_Tactics_Types.opts);
                     FStar_Tactics_Types.is_guard =
                       (uu___154_5068.FStar_Tactics_Types.is_guard)
                   })
  
let (rewrite : FStar_Syntax_Syntax.binder -> Prims.unit tac) =
  fun h  ->
    let uu____5076 = cur_goal ()  in
    bind uu____5076
      (fun goal  ->
         let uu____5084 = h  in
         match uu____5084 with
         | (bv,uu____5088) ->
             mlog
               (fun uu____5092  ->
                  let uu____5093 = FStar_Syntax_Print.bv_to_string bv  in
                  let uu____5094 =
                    tts goal.FStar_Tactics_Types.context
                      bv.FStar_Syntax_Syntax.sort
                     in
                  FStar_Util.print2 "+++Rewrite %s : %s\n" uu____5093
                    uu____5094)
               (fun uu____5097  ->
                  let uu____5098 =
                    split_env bv goal.FStar_Tactics_Types.context  in
                  match uu____5098 with
                  | FStar_Pervasives_Native.None  ->
                      fail "rewrite: binder not found in environment"
                  | FStar_Pervasives_Native.Some (e0,bvs) ->
                      let uu____5127 =
                        destruct_eq bv.FStar_Syntax_Syntax.sort  in
                      (match uu____5127 with
                       | FStar_Pervasives_Native.Some (x,e) ->
                           let uu____5142 =
                             let uu____5143 = FStar_Syntax_Subst.compress x
                                in
                             uu____5143.FStar_Syntax_Syntax.n  in
                           (match uu____5142 with
                            | FStar_Syntax_Syntax.Tm_name x1 ->
                                let s = [FStar_Syntax_Syntax.NT (x1, e)]  in
                                let s1 bv1 =
                                  let uu___155_5156 = bv1  in
                                  let uu____5157 =
                                    FStar_Syntax_Subst.subst s
                                      bv1.FStar_Syntax_Syntax.sort
                                     in
                                  {
                                    FStar_Syntax_Syntax.ppname =
                                      (uu___155_5156.FStar_Syntax_Syntax.ppname);
                                    FStar_Syntax_Syntax.index =
                                      (uu___155_5156.FStar_Syntax_Syntax.index);
                                    FStar_Syntax_Syntax.sort = uu____5157
                                  }  in
                                let bvs1 = FStar_List.map s1 bvs  in
                                let uu____5163 =
                                  let uu___156_5164 = goal  in
                                  let uu____5165 = push_bvs e0 (bv :: bvs1)
                                     in
                                  let uu____5166 =
                                    FStar_Syntax_Subst.subst s
                                      goal.FStar_Tactics_Types.witness
                                     in
                                  let uu____5167 =
                                    FStar_Syntax_Subst.subst s
                                      goal.FStar_Tactics_Types.goal_ty
                                     in
                                  {
                                    FStar_Tactics_Types.context = uu____5165;
                                    FStar_Tactics_Types.witness = uu____5166;
                                    FStar_Tactics_Types.goal_ty = uu____5167;
                                    FStar_Tactics_Types.opts =
                                      (uu___156_5164.FStar_Tactics_Types.opts);
                                    FStar_Tactics_Types.is_guard =
                                      (uu___156_5164.FStar_Tactics_Types.is_guard)
                                  }  in
                                replace_cur uu____5163
                            | uu____5168 ->
                                fail
                                  "rewrite: Not an equality hypothesis with a variable on the LHS")
                       | uu____5169 ->
                           fail "rewrite: Not an equality hypothesis")))
  
let (rename_to :
  FStar_Syntax_Syntax.binder -> Prims.string -> Prims.unit tac) =
  fun b  ->
    fun s  ->
      let uu____5186 = cur_goal ()  in
      bind uu____5186
        (fun goal  ->
           let uu____5197 = b  in
           match uu____5197 with
           | (bv,uu____5201) ->
               let bv' =
                 FStar_Syntax_Syntax.freshen_bv
                   (let uu___157_5205 = bv  in
                    {
                      FStar_Syntax_Syntax.ppname =
                        (FStar_Ident.mk_ident
                           (s,
                             ((bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange)));
                      FStar_Syntax_Syntax.index =
                        (uu___157_5205.FStar_Syntax_Syntax.index);
                      FStar_Syntax_Syntax.sort =
                        (uu___157_5205.FStar_Syntax_Syntax.sort)
                    })
                  in
               let s1 =
                 let uu____5209 =
                   let uu____5210 =
                     let uu____5217 = FStar_Syntax_Syntax.bv_to_name bv'  in
                     (bv, uu____5217)  in
                   FStar_Syntax_Syntax.NT uu____5210  in
                 [uu____5209]  in
               let uu____5218 = subst_goal bv bv' s1 goal  in
               (match uu____5218 with
                | FStar_Pervasives_Native.None  ->
                    fail "rename_to: binder not found in environment"
                | FStar_Pervasives_Native.Some goal1 -> replace_cur goal1))
  
let (binder_retype : FStar_Syntax_Syntax.binder -> Prims.unit tac) =
  fun b  ->
    let uu____5231 = cur_goal ()  in
    bind uu____5231
      (fun goal  ->
         let uu____5240 = b  in
         match uu____5240 with
         | (bv,uu____5244) ->
             let uu____5245 = split_env bv goal.FStar_Tactics_Types.context
                in
             (match uu____5245 with
              | FStar_Pervasives_Native.None  ->
                  fail "binder_retype: binder is not present in environment"
              | FStar_Pervasives_Native.Some (e0,bvs) ->
                  let uu____5274 = FStar_Syntax_Util.type_u ()  in
                  (match uu____5274 with
                   | (ty,u) ->
                       let uu____5283 = new_uvar "binder_retype" e0 ty  in
                       bind uu____5283
                         (fun t'  ->
                            let bv'' =
                              let uu___158_5293 = bv  in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___158_5293.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___158_5293.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = t'
                              }  in
                            let s =
                              let uu____5297 =
                                let uu____5298 =
                                  let uu____5305 =
                                    FStar_Syntax_Syntax.bv_to_name bv''  in
                                  (bv, uu____5305)  in
                                FStar_Syntax_Syntax.NT uu____5298  in
                              [uu____5297]  in
                            let bvs1 =
                              FStar_List.map
                                (fun b1  ->
                                   let uu___159_5313 = b1  in
                                   let uu____5314 =
                                     FStar_Syntax_Subst.subst s
                                       b1.FStar_Syntax_Syntax.sort
                                      in
                                   {
                                     FStar_Syntax_Syntax.ppname =
                                       (uu___159_5313.FStar_Syntax_Syntax.ppname);
                                     FStar_Syntax_Syntax.index =
                                       (uu___159_5313.FStar_Syntax_Syntax.index);
                                     FStar_Syntax_Syntax.sort = uu____5314
                                   }) bvs
                               in
                            let env' = push_bvs e0 (bv'' :: bvs1)  in
                            bind __dismiss
                              (fun uu____5320  ->
                                 let uu____5321 =
                                   let uu____5324 =
                                     let uu____5327 =
                                       let uu___160_5328 = goal  in
                                       let uu____5329 =
                                         FStar_Syntax_Subst.subst s
                                           goal.FStar_Tactics_Types.witness
                                          in
                                       let uu____5330 =
                                         FStar_Syntax_Subst.subst s
                                           goal.FStar_Tactics_Types.goal_ty
                                          in
                                       {
                                         FStar_Tactics_Types.context = env';
                                         FStar_Tactics_Types.witness =
                                           uu____5329;
                                         FStar_Tactics_Types.goal_ty =
                                           uu____5330;
                                         FStar_Tactics_Types.opts =
                                           (uu___160_5328.FStar_Tactics_Types.opts);
                                         FStar_Tactics_Types.is_guard =
                                           (uu___160_5328.FStar_Tactics_Types.is_guard)
                                       }  in
                                     [uu____5327]  in
                                   add_goals uu____5324  in
                                 bind uu____5321
                                   (fun uu____5333  ->
                                      let uu____5334 =
                                        FStar_Syntax_Util.mk_eq2
                                          (FStar_Syntax_Syntax.U_succ u) ty
                                          bv.FStar_Syntax_Syntax.sort t'
                                         in
                                      add_irrelevant_goal
                                        "binder_retype equation" e0
                                        uu____5334
                                        goal.FStar_Tactics_Types.opts))))))
  
let (norm_binder_type :
  FStar_Syntax_Embeddings.norm_step Prims.list ->
    FStar_Syntax_Syntax.binder -> Prims.unit tac)
  =
  fun s  ->
    fun b  ->
      let uu____5349 = cur_goal ()  in
      bind uu____5349
        (fun goal  ->
           let uu____5358 = b  in
           match uu____5358 with
           | (bv,uu____5362) ->
               let uu____5363 = split_env bv goal.FStar_Tactics_Types.context
                  in
               (match uu____5363 with
                | FStar_Pervasives_Native.None  ->
                    fail
                      "binder_retype: binder is not present in environment"
                | FStar_Pervasives_Native.Some (e0,bvs) ->
                    let steps =
                      let uu____5395 =
                        FStar_TypeChecker_Normalize.tr_norm_steps s  in
                      FStar_List.append
                        [FStar_TypeChecker_Normalize.Reify;
                        FStar_TypeChecker_Normalize.UnfoldTac] uu____5395
                       in
                    let sort' =
                      normalize steps e0 bv.FStar_Syntax_Syntax.sort  in
                    let bv' =
                      let uu___161_5400 = bv  in
                      {
                        FStar_Syntax_Syntax.ppname =
                          (uu___161_5400.FStar_Syntax_Syntax.ppname);
                        FStar_Syntax_Syntax.index =
                          (uu___161_5400.FStar_Syntax_Syntax.index);
                        FStar_Syntax_Syntax.sort = sort'
                      }  in
                    let env' = push_bvs e0 (bv' :: bvs)  in
                    replace_cur
                      (let uu___162_5404 = goal  in
                       {
                         FStar_Tactics_Types.context = env';
                         FStar_Tactics_Types.witness =
                           (uu___162_5404.FStar_Tactics_Types.witness);
                         FStar_Tactics_Types.goal_ty =
                           (uu___162_5404.FStar_Tactics_Types.goal_ty);
                         FStar_Tactics_Types.opts =
                           (uu___162_5404.FStar_Tactics_Types.opts);
                         FStar_Tactics_Types.is_guard =
                           (uu___162_5404.FStar_Tactics_Types.is_guard)
                       })))
  
let (revert : Prims.unit -> Prims.unit tac) =
  fun uu____5409  ->
    let uu____5412 = cur_goal ()  in
    bind uu____5412
      (fun goal  ->
         let uu____5418 =
           FStar_TypeChecker_Env.pop_bv goal.FStar_Tactics_Types.context  in
         match uu____5418 with
         | FStar_Pervasives_Native.None  ->
             fail "Cannot revert; empty context"
         | FStar_Pervasives_Native.Some (x,env') ->
             let typ' =
               let uu____5440 =
                 FStar_Syntax_Syntax.mk_Total
                   goal.FStar_Tactics_Types.goal_ty
                  in
               FStar_Syntax_Util.arrow [(x, FStar_Pervasives_Native.None)]
                 uu____5440
                in
             let w' =
               FStar_Syntax_Util.abs [(x, FStar_Pervasives_Native.None)]
                 goal.FStar_Tactics_Types.witness
                 FStar_Pervasives_Native.None
                in
             replace_cur
               (let uu___163_5474 = goal  in
                {
                  FStar_Tactics_Types.context = env';
                  FStar_Tactics_Types.witness = w';
                  FStar_Tactics_Types.goal_ty = typ';
                  FStar_Tactics_Types.opts =
                    (uu___163_5474.FStar_Tactics_Types.opts);
                  FStar_Tactics_Types.is_guard =
                    (uu___163_5474.FStar_Tactics_Types.is_guard)
                }))
  
let (free_in :
  FStar_Syntax_Syntax.bv -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun bv  ->
    fun t  ->
      let uu____5481 = FStar_Syntax_Free.names t  in
      FStar_Util.set_mem bv uu____5481
  
let rec (clear : FStar_Syntax_Syntax.binder -> Prims.unit tac) =
  fun b  ->
    let bv = FStar_Pervasives_Native.fst b  in
    let uu____5492 = cur_goal ()  in
    bind uu____5492
      (fun goal  ->
         mlog
           (fun uu____5500  ->
              let uu____5501 = FStar_Syntax_Print.binder_to_string b  in
              let uu____5502 =
                let uu____5503 =
                  let uu____5504 =
                    FStar_TypeChecker_Env.all_binders
                      goal.FStar_Tactics_Types.context
                     in
                  FStar_All.pipe_right uu____5504 FStar_List.length  in
                FStar_All.pipe_right uu____5503 FStar_Util.string_of_int  in
              FStar_Util.print2 "Clear of (%s), env has %s binders\n"
                uu____5501 uu____5502)
           (fun uu____5515  ->
              let uu____5516 = split_env bv goal.FStar_Tactics_Types.context
                 in
              match uu____5516 with
              | FStar_Pervasives_Native.None  ->
                  fail "Cannot clear; binder not in environment"
              | FStar_Pervasives_Native.Some (e',bvs) ->
                  let rec check1 bvs1 =
                    match bvs1 with
                    | [] -> ret ()
                    | bv'::bvs2 ->
                        let uu____5561 =
                          free_in bv bv'.FStar_Syntax_Syntax.sort  in
                        if uu____5561
                        then
                          let uu____5564 =
                            let uu____5565 =
                              FStar_Syntax_Print.bv_to_string bv'  in
                            FStar_Util.format1
                              "Cannot clear; binder present in the type of %s"
                              uu____5565
                             in
                          fail uu____5564
                        else check1 bvs2
                     in
                  let uu____5567 =
                    free_in bv goal.FStar_Tactics_Types.goal_ty  in
                  if uu____5567
                  then fail "Cannot clear; binder present in goal"
                  else
                    (let uu____5571 = check1 bvs  in
                     bind uu____5571
                       (fun uu____5577  ->
                          let env' = push_bvs e' bvs  in
                          let uu____5579 =
                            new_uvar "clear.witness" env'
                              goal.FStar_Tactics_Types.goal_ty
                             in
                          bind uu____5579
                            (fun ut  ->
                               let uu____5585 =
                                 do_unify goal.FStar_Tactics_Types.context
                                   goal.FStar_Tactics_Types.witness ut
                                  in
                               bind uu____5585
                                 (fun b1  ->
                                    if b1
                                    then
                                      replace_cur
                                        (let uu___164_5594 = goal  in
                                         {
                                           FStar_Tactics_Types.context = env';
                                           FStar_Tactics_Types.witness = ut;
                                           FStar_Tactics_Types.goal_ty =
                                             (uu___164_5594.FStar_Tactics_Types.goal_ty);
                                           FStar_Tactics_Types.opts =
                                             (uu___164_5594.FStar_Tactics_Types.opts);
                                           FStar_Tactics_Types.is_guard =
                                             (uu___164_5594.FStar_Tactics_Types.is_guard)
                                         })
                                    else
                                      fail
                                        "Cannot clear; binder appears in witness"))))))
  
let (clear_top : Prims.unit -> Prims.unit tac) =
  fun uu____5600  ->
    let uu____5603 = cur_goal ()  in
    bind uu____5603
      (fun goal  ->
         let uu____5609 =
           FStar_TypeChecker_Env.pop_bv goal.FStar_Tactics_Types.context  in
         match uu____5609 with
         | FStar_Pervasives_Native.None  ->
             fail "Cannot clear; empty context"
         | FStar_Pervasives_Native.Some (x,uu____5623) ->
             let uu____5628 = FStar_Syntax_Syntax.mk_binder x  in
             clear uu____5628)
  
let (prune : Prims.string -> Prims.unit tac) =
  fun s  ->
    let uu____5636 = cur_goal ()  in
    bind uu____5636
      (fun g  ->
         let ctx = g.FStar_Tactics_Types.context  in
         let ctx' =
           FStar_TypeChecker_Env.rem_proof_ns ctx
             (FStar_Ident.path_of_text s)
            in
         let g' =
           let uu___165_5647 = g  in
           {
             FStar_Tactics_Types.context = ctx';
             FStar_Tactics_Types.witness =
               (uu___165_5647.FStar_Tactics_Types.witness);
             FStar_Tactics_Types.goal_ty =
               (uu___165_5647.FStar_Tactics_Types.goal_ty);
             FStar_Tactics_Types.opts =
               (uu___165_5647.FStar_Tactics_Types.opts);
             FStar_Tactics_Types.is_guard =
               (uu___165_5647.FStar_Tactics_Types.is_guard)
           }  in
         bind __dismiss (fun uu____5649  -> add_goals [g']))
  
let (addns : Prims.string -> Prims.unit tac) =
  fun s  ->
    let uu____5657 = cur_goal ()  in
    bind uu____5657
      (fun g  ->
         let ctx = g.FStar_Tactics_Types.context  in
         let ctx' =
           FStar_TypeChecker_Env.add_proof_ns ctx
             (FStar_Ident.path_of_text s)
            in
         let g' =
           let uu___166_5668 = g  in
           {
             FStar_Tactics_Types.context = ctx';
             FStar_Tactics_Types.witness =
               (uu___166_5668.FStar_Tactics_Types.witness);
             FStar_Tactics_Types.goal_ty =
               (uu___166_5668.FStar_Tactics_Types.goal_ty);
             FStar_Tactics_Types.opts =
               (uu___166_5668.FStar_Tactics_Types.opts);
             FStar_Tactics_Types.is_guard =
               (uu___166_5668.FStar_Tactics_Types.is_guard)
           }  in
         bind __dismiss (fun uu____5670  -> add_goals [g']))
  
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
            let uu____5702 = FStar_Syntax_Subst.compress t  in
            uu____5702.FStar_Syntax_Syntax.n  in
          let uu____5705 =
            if d = FStar_Tactics_Types.TopDown
            then
              f env
                (let uu___170_5711 = t  in
                 {
                   FStar_Syntax_Syntax.n = tn;
                   FStar_Syntax_Syntax.pos =
                     (uu___170_5711.FStar_Syntax_Syntax.pos);
                   FStar_Syntax_Syntax.vars =
                     (uu___170_5711.FStar_Syntax_Syntax.vars)
                 })
            else ret t  in
          bind uu____5705
            (fun t1  ->
               let ff = tac_fold_env d f env  in
               let tn1 =
                 let uu____5725 =
                   let uu____5726 = FStar_Syntax_Subst.compress t1  in
                   uu____5726.FStar_Syntax_Syntax.n  in
                 match uu____5725 with
                 | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
                     let uu____5753 = ff hd1  in
                     bind uu____5753
                       (fun hd2  ->
                          let fa uu____5773 =
                            match uu____5773 with
                            | (a,q) ->
                                let uu____5786 = ff a  in
                                bind uu____5786 (fun a1  -> ret (a1, q))
                             in
                          let uu____5799 = mapM fa args  in
                          bind uu____5799
                            (fun args1  ->
                               ret (FStar_Syntax_Syntax.Tm_app (hd2, args1))))
                 | FStar_Syntax_Syntax.Tm_abs (bs,t2,k) ->
                     let uu____5859 = FStar_Syntax_Subst.open_term bs t2  in
                     (match uu____5859 with
                      | (bs1,t') ->
                          let uu____5868 =
                            let uu____5871 =
                              FStar_TypeChecker_Env.push_binders env bs1  in
                            tac_fold_env d f uu____5871 t'  in
                          bind uu____5868
                            (fun t''  ->
                               let uu____5875 =
                                 let uu____5876 =
                                   let uu____5893 =
                                     FStar_Syntax_Subst.close_binders bs1  in
                                   let uu____5894 =
                                     FStar_Syntax_Subst.close bs1 t''  in
                                   (uu____5893, uu____5894, k)  in
                                 FStar_Syntax_Syntax.Tm_abs uu____5876  in
                               ret uu____5875))
                 | FStar_Syntax_Syntax.Tm_arrow (bs,k) -> ret tn
                 | FStar_Syntax_Syntax.Tm_match (hd1,brs) ->
                     let uu____5953 = ff hd1  in
                     bind uu____5953
                       (fun hd2  ->
                          let ffb br =
                            let uu____5966 =
                              FStar_Syntax_Subst.open_branch br  in
                            match uu____5966 with
                            | (pat,w,e) ->
                                let uu____5988 = ff e  in
                                bind uu____5988
                                  (fun e1  ->
                                     let br1 =
                                       FStar_Syntax_Subst.close_branch
                                         (pat, w, e1)
                                        in
                                     ret br1)
                             in
                          let uu____6001 = mapM ffb brs  in
                          bind uu____6001
                            (fun brs1  ->
                               ret (FStar_Syntax_Syntax.Tm_match (hd2, brs1))))
                 | FStar_Syntax_Syntax.Tm_let
                     ((false
                       ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inl bv;
                          FStar_Syntax_Syntax.lbunivs = uu____6015;
                          FStar_Syntax_Syntax.lbtyp = uu____6016;
                          FStar_Syntax_Syntax.lbeff = uu____6017;
                          FStar_Syntax_Syntax.lbdef = def;
                          FStar_Syntax_Syntax.lbattrs = uu____6019;
                          FStar_Syntax_Syntax.lbpos = uu____6020;_}::[]),e)
                     ->
                     let lb =
                       let uu____6045 =
                         let uu____6046 = FStar_Syntax_Subst.compress t1  in
                         uu____6046.FStar_Syntax_Syntax.n  in
                       match uu____6045 with
                       | FStar_Syntax_Syntax.Tm_let
                           ((false ,lb::[]),uu____6050) -> lb
                       | uu____6063 -> failwith "impossible"  in
                     let fflb lb1 =
                       let uu____6070 = ff lb1.FStar_Syntax_Syntax.lbdef  in
                       bind uu____6070
                         (fun def1  ->
                            ret
                              (let uu___167_6076 = lb1  in
                               {
                                 FStar_Syntax_Syntax.lbname =
                                   (uu___167_6076.FStar_Syntax_Syntax.lbname);
                                 FStar_Syntax_Syntax.lbunivs =
                                   (uu___167_6076.FStar_Syntax_Syntax.lbunivs);
                                 FStar_Syntax_Syntax.lbtyp =
                                   (uu___167_6076.FStar_Syntax_Syntax.lbtyp);
                                 FStar_Syntax_Syntax.lbeff =
                                   (uu___167_6076.FStar_Syntax_Syntax.lbeff);
                                 FStar_Syntax_Syntax.lbdef = def1;
                                 FStar_Syntax_Syntax.lbattrs =
                                   (uu___167_6076.FStar_Syntax_Syntax.lbattrs);
                                 FStar_Syntax_Syntax.lbpos =
                                   (uu___167_6076.FStar_Syntax_Syntax.lbpos)
                               }))
                        in
                     let uu____6077 = fflb lb  in
                     bind uu____6077
                       (fun lb1  ->
                          let uu____6086 =
                            let uu____6091 =
                              let uu____6092 =
                                FStar_Syntax_Syntax.mk_binder bv  in
                              [uu____6092]  in
                            FStar_Syntax_Subst.open_term uu____6091 e  in
                          match uu____6086 with
                          | (bs,e1) ->
                              let uu____6097 = ff e1  in
                              bind uu____6097
                                (fun e2  ->
                                   let e3 = FStar_Syntax_Subst.close bs e2
                                      in
                                   ret
                                     (FStar_Syntax_Syntax.Tm_let
                                        ((false, [lb1]), e3))))
                 | FStar_Syntax_Syntax.Tm_let ((true ,lbs),e) ->
                     let fflb lb =
                       let uu____6134 = ff lb.FStar_Syntax_Syntax.lbdef  in
                       bind uu____6134
                         (fun def  ->
                            ret
                              (let uu___168_6140 = lb  in
                               {
                                 FStar_Syntax_Syntax.lbname =
                                   (uu___168_6140.FStar_Syntax_Syntax.lbname);
                                 FStar_Syntax_Syntax.lbunivs =
                                   (uu___168_6140.FStar_Syntax_Syntax.lbunivs);
                                 FStar_Syntax_Syntax.lbtyp =
                                   (uu___168_6140.FStar_Syntax_Syntax.lbtyp);
                                 FStar_Syntax_Syntax.lbeff =
                                   (uu___168_6140.FStar_Syntax_Syntax.lbeff);
                                 FStar_Syntax_Syntax.lbdef = def;
                                 FStar_Syntax_Syntax.lbattrs =
                                   (uu___168_6140.FStar_Syntax_Syntax.lbattrs);
                                 FStar_Syntax_Syntax.lbpos =
                                   (uu___168_6140.FStar_Syntax_Syntax.lbpos)
                               }))
                        in
                     let uu____6141 = FStar_Syntax_Subst.open_let_rec lbs e
                        in
                     (match uu____6141 with
                      | (lbs1,e1) ->
                          let uu____6156 = mapM fflb lbs1  in
                          bind uu____6156
                            (fun lbs2  ->
                               let uu____6168 = ff e1  in
                               bind uu____6168
                                 (fun e2  ->
                                    let uu____6176 =
                                      FStar_Syntax_Subst.close_let_rec lbs2
                                        e2
                                       in
                                    match uu____6176 with
                                    | (lbs3,e3) ->
                                        ret
                                          (FStar_Syntax_Syntax.Tm_let
                                             ((true, lbs3), e3)))))
                 | FStar_Syntax_Syntax.Tm_ascribed (t2,asc,eff) ->
                     let uu____6242 = ff t2  in
                     bind uu____6242
                       (fun t3  ->
                          ret
                            (FStar_Syntax_Syntax.Tm_ascribed (t3, asc, eff)))
                 | FStar_Syntax_Syntax.Tm_meta (t2,m) ->
                     let uu____6271 = ff t2  in
                     bind uu____6271
                       (fun t3  -> ret (FStar_Syntax_Syntax.Tm_meta (t3, m)))
                 | uu____6276 -> ret tn  in
               bind tn1
                 (fun tn2  ->
                    let t' =
                      let uu___169_6283 = t1  in
                      {
                        FStar_Syntax_Syntax.n = tn2;
                        FStar_Syntax_Syntax.pos =
                          (uu___169_6283.FStar_Syntax_Syntax.pos);
                        FStar_Syntax_Syntax.vars =
                          (uu___169_6283.FStar_Syntax_Syntax.vars)
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
            let uu____6312 = FStar_TypeChecker_TcTerm.tc_term env t  in
            match uu____6312 with
            | (t1,lcomp,g) ->
                let uu____6324 =
                  (let uu____6327 =
                     FStar_Syntax_Util.is_pure_or_ghost_lcomp lcomp  in
                   Prims.op_Negation uu____6327) ||
                    (let uu____6329 = FStar_TypeChecker_Rel.is_trivial g  in
                     Prims.op_Negation uu____6329)
                   in
                if uu____6324
                then ret t1
                else
                  (let rewrite_eq =
                     let typ = lcomp.FStar_Syntax_Syntax.res_typ  in
                     let uu____6339 = new_uvar "pointwise_rec" env typ  in
                     bind uu____6339
                       (fun ut  ->
                          log ps
                            (fun uu____6350  ->
                               let uu____6351 =
                                 FStar_Syntax_Print.term_to_string t1  in
                               let uu____6352 =
                                 FStar_Syntax_Print.term_to_string ut  in
                               FStar_Util.print2
                                 "Pointwise_rec: making equality\n\t%s ==\n\t%s\n"
                                 uu____6351 uu____6352);
                          (let uu____6353 =
                             let uu____6356 =
                               let uu____6357 =
                                 FStar_TypeChecker_TcTerm.universe_of env typ
                                  in
                               FStar_Syntax_Util.mk_eq2 uu____6357 typ t1 ut
                                in
                             add_irrelevant_goal "pointwise_rec equation" env
                               uu____6356 opts
                              in
                           bind uu____6353
                             (fun uu____6360  ->
                                let uu____6361 =
                                  bind tau
                                    (fun uu____6367  ->
                                       let ut1 =
                                         FStar_TypeChecker_Normalize.reduce_uvar_solutions
                                           env ut
                                          in
                                       log ps
                                         (fun uu____6373  ->
                                            let uu____6374 =
                                              FStar_Syntax_Print.term_to_string
                                                t1
                                               in
                                            let uu____6375 =
                                              FStar_Syntax_Print.term_to_string
                                                ut1
                                               in
                                            FStar_Util.print2
                                              "Pointwise_rec: succeeded rewriting\n\t%s to\n\t%s\n"
                                              uu____6374 uu____6375);
                                       ret ut1)
                                   in
                                focus uu____6361)))
                      in
                   let uu____6376 = trytac' rewrite_eq  in
                   bind uu____6376
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
          let uu____6524 = FStar_Syntax_Subst.compress t  in
          maybe_continue ctrl uu____6524
            (fun t1  ->
               let uu____6528 =
                 f env
                   (let uu___173_6537 = t1  in
                    {
                      FStar_Syntax_Syntax.n = (t1.FStar_Syntax_Syntax.n);
                      FStar_Syntax_Syntax.pos =
                        (uu___173_6537.FStar_Syntax_Syntax.pos);
                      FStar_Syntax_Syntax.vars =
                        (uu___173_6537.FStar_Syntax_Syntax.vars)
                    })
                  in
               bind uu____6528
                 (fun uu____6549  ->
                    match uu____6549 with
                    | (t2,ctrl1) ->
                        maybe_continue ctrl1 t2
                          (fun t3  ->
                             let uu____6568 =
                               let uu____6569 =
                                 FStar_Syntax_Subst.compress t3  in
                               uu____6569.FStar_Syntax_Syntax.n  in
                             match uu____6568 with
                             | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
                                 let uu____6602 =
                                   ctrl_tac_fold f env ctrl1 hd1  in
                                 bind uu____6602
                                   (fun uu____6627  ->
                                      match uu____6627 with
                                      | (hd2,ctrl2) ->
                                          let ctrl3 = keep_going ctrl2  in
                                          let uu____6643 =
                                            ctrl_tac_fold_args f env ctrl3
                                              args
                                             in
                                          bind uu____6643
                                            (fun uu____6670  ->
                                               match uu____6670 with
                                               | (args1,ctrl4) ->
                                                   ret
                                                     ((let uu___171_6700 = t3
                                                          in
                                                       {
                                                         FStar_Syntax_Syntax.n
                                                           =
                                                           (FStar_Syntax_Syntax.Tm_app
                                                              (hd2, args1));
                                                         FStar_Syntax_Syntax.pos
                                                           =
                                                           (uu___171_6700.FStar_Syntax_Syntax.pos);
                                                         FStar_Syntax_Syntax.vars
                                                           =
                                                           (uu___171_6700.FStar_Syntax_Syntax.vars)
                                                       }), ctrl4)))
                             | FStar_Syntax_Syntax.Tm_abs (bs,t4,k) ->
                                 let uu____6726 =
                                   FStar_Syntax_Subst.open_term bs t4  in
                                 (match uu____6726 with
                                  | (bs1,t') ->
                                      let uu____6741 =
                                        let uu____6748 =
                                          FStar_TypeChecker_Env.push_binders
                                            env bs1
                                           in
                                        ctrl_tac_fold f uu____6748 ctrl1 t'
                                         in
                                      bind uu____6741
                                        (fun uu____6766  ->
                                           match uu____6766 with
                                           | (t'',ctrl2) ->
                                               let uu____6781 =
                                                 let uu____6788 =
                                                   let uu___172_6791 = t4  in
                                                   let uu____6794 =
                                                     let uu____6795 =
                                                       let uu____6812 =
                                                         FStar_Syntax_Subst.close_binders
                                                           bs1
                                                          in
                                                       let uu____6813 =
                                                         FStar_Syntax_Subst.close
                                                           bs1 t''
                                                          in
                                                       (uu____6812,
                                                         uu____6813, k)
                                                        in
                                                     FStar_Syntax_Syntax.Tm_abs
                                                       uu____6795
                                                      in
                                                   {
                                                     FStar_Syntax_Syntax.n =
                                                       uu____6794;
                                                     FStar_Syntax_Syntax.pos
                                                       =
                                                       (uu___172_6791.FStar_Syntax_Syntax.pos);
                                                     FStar_Syntax_Syntax.vars
                                                       =
                                                       (uu___172_6791.FStar_Syntax_Syntax.vars)
                                                   }  in
                                                 (uu____6788, ctrl2)  in
                                               ret uu____6781))
                             | FStar_Syntax_Syntax.Tm_arrow (bs,k) ->
                                 ret (t3, ctrl1)
                             | uu____6846 -> ret (t3, ctrl1))))

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
              let uu____6897 = ctrl_tac_fold f env ctrl t  in
              bind uu____6897
                (fun uu____6925  ->
                   match uu____6925 with
                   | (t1,ctrl1) ->
                       let uu____6944 = ctrl_tac_fold_args f env ctrl1 ts1
                          in
                       bind uu____6944
                         (fun uu____6975  ->
                            match uu____6975 with
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
              let uu____7059 =
                let uu____7066 =
                  add_irrelevant_goal "dummy" env FStar_Syntax_Util.t_true
                    opts
                   in
                bind uu____7066
                  (fun uu____7075  ->
                     let uu____7076 = ctrl t1  in
                     bind uu____7076
                       (fun res  ->
                          let uu____7099 = trivial ()  in
                          bind uu____7099 (fun uu____7107  -> ret res)))
                 in
              bind uu____7059
                (fun uu____7123  ->
                   match uu____7123 with
                   | (should_rewrite,ctrl1) ->
                       if Prims.op_Negation should_rewrite
                       then ret (t1, ctrl1)
                       else
                         (let uu____7147 =
                            FStar_TypeChecker_TcTerm.tc_term env t1  in
                          match uu____7147 with
                          | (t2,lcomp,g) ->
                              let uu____7163 =
                                (let uu____7166 =
                                   FStar_Syntax_Util.is_pure_or_ghost_lcomp
                                     lcomp
                                    in
                                 Prims.op_Negation uu____7166) ||
                                  (let uu____7168 =
                                     FStar_TypeChecker_Rel.is_trivial g  in
                                   Prims.op_Negation uu____7168)
                                 in
                              if uu____7163
                              then ret (t2, globalStop)
                              else
                                (let typ = lcomp.FStar_Syntax_Syntax.res_typ
                                    in
                                 let uu____7183 =
                                   new_uvar "pointwise_rec" env typ  in
                                 bind uu____7183
                                   (fun ut  ->
                                      log ps
                                        (fun uu____7198  ->
                                           let uu____7199 =
                                             FStar_Syntax_Print.term_to_string
                                               t2
                                              in
                                           let uu____7200 =
                                             FStar_Syntax_Print.term_to_string
                                               ut
                                              in
                                           FStar_Util.print2
                                             "Pointwise_rec: making equality\n\t%s ==\n\t%s\n"
                                             uu____7199 uu____7200);
                                      (let uu____7201 =
                                         let uu____7204 =
                                           let uu____7205 =
                                             FStar_TypeChecker_TcTerm.universe_of
                                               env typ
                                              in
                                           FStar_Syntax_Util.mk_eq2
                                             uu____7205 typ t2 ut
                                            in
                                         add_irrelevant_goal
                                           "rewrite_rec equation" env
                                           uu____7204 opts
                                          in
                                       bind uu____7201
                                         (fun uu____7212  ->
                                            let uu____7213 =
                                              bind rewriter
                                                (fun uu____7227  ->
                                                   let ut1 =
                                                     FStar_TypeChecker_Normalize.reduce_uvar_solutions
                                                       env ut
                                                      in
                                                   log ps
                                                     (fun uu____7233  ->
                                                        let uu____7234 =
                                                          FStar_Syntax_Print.term_to_string
                                                            t2
                                                           in
                                                        let uu____7235 =
                                                          FStar_Syntax_Print.term_to_string
                                                            ut1
                                                           in
                                                        FStar_Util.print2
                                                          "rewrite_rec: succeeded rewriting\n\t%s to\n\t%s\n"
                                                          uu____7234
                                                          uu____7235);
                                                   ret (ut1, ctrl1))
                                               in
                                            focus uu____7213))))))
  
let (topdown_rewrite :
  (FStar_Syntax_Syntax.term ->
     (Prims.bool,FStar_BigInt.t) FStar_Pervasives_Native.tuple2 tac)
    -> Prims.unit tac -> Prims.unit tac)
  =
  fun ctrl  ->
    fun rewriter  ->
      bind get
        (fun ps  ->
           let uu____7279 =
             match ps.FStar_Tactics_Types.goals with
             | g::gs -> (g, gs)
             | [] -> failwith "Pointwise: no goals"  in
           match uu____7279 with
           | (g,gs) ->
               let gt1 = g.FStar_Tactics_Types.goal_ty  in
               (log ps
                  (fun uu____7316  ->
                     let uu____7317 = FStar_Syntax_Print.term_to_string gt1
                        in
                     FStar_Util.print1 "Pointwise starting with %s\n"
                       uu____7317);
                bind dismiss_all
                  (fun uu____7320  ->
                     let uu____7321 =
                       ctrl_tac_fold
                         (rewrite_rec ps ctrl rewriter
                            g.FStar_Tactics_Types.opts)
                         g.FStar_Tactics_Types.context keepGoing gt1
                        in
                     bind uu____7321
                       (fun uu____7339  ->
                          match uu____7339 with
                          | (gt',uu____7347) ->
                              (log ps
                                 (fun uu____7351  ->
                                    let uu____7352 =
                                      FStar_Syntax_Print.term_to_string gt'
                                       in
                                    FStar_Util.print1
                                      "Pointwise seems to have succeded with %s\n"
                                      uu____7352);
                               (let uu____7353 = push_goals gs  in
                                bind uu____7353
                                  (fun uu____7357  ->
                                     add_goals
                                       [(let uu___174_7359 = g  in
                                         {
                                           FStar_Tactics_Types.context =
                                             (uu___174_7359.FStar_Tactics_Types.context);
                                           FStar_Tactics_Types.witness =
                                             (uu___174_7359.FStar_Tactics_Types.witness);
                                           FStar_Tactics_Types.goal_ty = gt';
                                           FStar_Tactics_Types.opts =
                                             (uu___174_7359.FStar_Tactics_Types.opts);
                                           FStar_Tactics_Types.is_guard =
                                             (uu___174_7359.FStar_Tactics_Types.is_guard)
                                         })])))))))
  
let (pointwise :
  FStar_Tactics_Types.direction -> Prims.unit tac -> Prims.unit tac) =
  fun d  ->
    fun tau  ->
      bind get
        (fun ps  ->
           let uu____7381 =
             match ps.FStar_Tactics_Types.goals with
             | g::gs -> (g, gs)
             | [] -> failwith "Pointwise: no goals"  in
           match uu____7381 with
           | (g,gs) ->
               let gt1 = g.FStar_Tactics_Types.goal_ty  in
               (log ps
                  (fun uu____7418  ->
                     let uu____7419 = FStar_Syntax_Print.term_to_string gt1
                        in
                     FStar_Util.print1 "Pointwise starting with %s\n"
                       uu____7419);
                bind dismiss_all
                  (fun uu____7422  ->
                     let uu____7423 =
                       tac_fold_env d
                         (pointwise_rec ps tau g.FStar_Tactics_Types.opts)
                         g.FStar_Tactics_Types.context gt1
                        in
                     bind uu____7423
                       (fun gt'  ->
                          log ps
                            (fun uu____7433  ->
                               let uu____7434 =
                                 FStar_Syntax_Print.term_to_string gt'  in
                               FStar_Util.print1
                                 "Pointwise seems to have succeded with %s\n"
                                 uu____7434);
                          (let uu____7435 = push_goals gs  in
                           bind uu____7435
                             (fun uu____7439  ->
                                add_goals
                                  [(let uu___175_7441 = g  in
                                    {
                                      FStar_Tactics_Types.context =
                                        (uu___175_7441.FStar_Tactics_Types.context);
                                      FStar_Tactics_Types.witness =
                                        (uu___175_7441.FStar_Tactics_Types.witness);
                                      FStar_Tactics_Types.goal_ty = gt';
                                      FStar_Tactics_Types.opts =
                                        (uu___175_7441.FStar_Tactics_Types.opts);
                                      FStar_Tactics_Types.is_guard =
                                        (uu___175_7441.FStar_Tactics_Types.is_guard)
                                    })]))))))
  
let (trefl : Prims.unit -> Prims.unit tac) =
  fun uu____7446  ->
    let uu____7449 = cur_goal ()  in
    bind uu____7449
      (fun g  ->
         let uu____7467 =
           FStar_Syntax_Util.un_squash g.FStar_Tactics_Types.goal_ty  in
         match uu____7467 with
         | FStar_Pervasives_Native.Some t ->
             let uu____7479 = FStar_Syntax_Util.head_and_args' t  in
             (match uu____7479 with
              | (hd1,args) ->
                  let uu____7512 =
                    let uu____7525 =
                      let uu____7526 = FStar_Syntax_Util.un_uinst hd1  in
                      uu____7526.FStar_Syntax_Syntax.n  in
                    (uu____7525, args)  in
                  (match uu____7512 with
                   | (FStar_Syntax_Syntax.Tm_fvar
                      fv,uu____7540::(l,uu____7542)::(r,uu____7544)::[]) when
                       FStar_Syntax_Syntax.fv_eq_lid fv
                         FStar_Parser_Const.eq2_lid
                       ->
                       let uu____7591 =
                         do_unify g.FStar_Tactics_Types.context l r  in
                       bind uu____7591
                         (fun b  ->
                            if Prims.op_Negation b
                            then
                              let uu____7600 =
                                tts g.FStar_Tactics_Types.context l  in
                              let uu____7601 =
                                tts g.FStar_Tactics_Types.context r  in
                              fail2
                                "trefl: not a trivial equality (%s vs %s)"
                                uu____7600 uu____7601
                            else solve g FStar_Syntax_Util.exp_unit)
                   | (hd2,uu____7604) ->
                       let uu____7621 = tts g.FStar_Tactics_Types.context t
                          in
                       fail1 "trefl: not an equality (%s)" uu____7621))
         | FStar_Pervasives_Native.None  -> fail "not an irrelevant goal")
  
let (dup : Prims.unit -> Prims.unit tac) =
  fun uu____7628  ->
    let uu____7631 = cur_goal ()  in
    bind uu____7631
      (fun g  ->
         let uu____7637 =
           new_uvar "dup" g.FStar_Tactics_Types.context
             g.FStar_Tactics_Types.goal_ty
            in
         bind uu____7637
           (fun u  ->
              let g' =
                let uu___176_7644 = g  in
                {
                  FStar_Tactics_Types.context =
                    (uu___176_7644.FStar_Tactics_Types.context);
                  FStar_Tactics_Types.witness = u;
                  FStar_Tactics_Types.goal_ty =
                    (uu___176_7644.FStar_Tactics_Types.goal_ty);
                  FStar_Tactics_Types.opts =
                    (uu___176_7644.FStar_Tactics_Types.opts);
                  FStar_Tactics_Types.is_guard =
                    (uu___176_7644.FStar_Tactics_Types.is_guard)
                }  in
              bind __dismiss
                (fun uu____7647  ->
                   let uu____7648 =
                     let uu____7651 =
                       let uu____7652 =
                         FStar_TypeChecker_TcTerm.universe_of
                           g.FStar_Tactics_Types.context
                           g.FStar_Tactics_Types.goal_ty
                          in
                       FStar_Syntax_Util.mk_eq2 uu____7652
                         g.FStar_Tactics_Types.goal_ty u
                         g.FStar_Tactics_Types.witness
                        in
                     add_irrelevant_goal "dup equation"
                       g.FStar_Tactics_Types.context uu____7651
                       g.FStar_Tactics_Types.opts
                      in
                   bind uu____7648
                     (fun uu____7655  ->
                        let uu____7656 = add_goals [g']  in
                        bind uu____7656 (fun uu____7660  -> ret ())))))
  
let (flip : Prims.unit -> Prims.unit tac) =
  fun uu____7665  ->
    bind get
      (fun ps  ->
         match ps.FStar_Tactics_Types.goals with
         | g1::g2::gs ->
             set
               (let uu___177_7682 = ps  in
                {
                  FStar_Tactics_Types.main_context =
                    (uu___177_7682.FStar_Tactics_Types.main_context);
                  FStar_Tactics_Types.main_goal =
                    (uu___177_7682.FStar_Tactics_Types.main_goal);
                  FStar_Tactics_Types.all_implicits =
                    (uu___177_7682.FStar_Tactics_Types.all_implicits);
                  FStar_Tactics_Types.goals = (g2 :: g1 :: gs);
                  FStar_Tactics_Types.smt_goals =
                    (uu___177_7682.FStar_Tactics_Types.smt_goals);
                  FStar_Tactics_Types.depth =
                    (uu___177_7682.FStar_Tactics_Types.depth);
                  FStar_Tactics_Types.__dump =
                    (uu___177_7682.FStar_Tactics_Types.__dump);
                  FStar_Tactics_Types.psc =
                    (uu___177_7682.FStar_Tactics_Types.psc);
                  FStar_Tactics_Types.entry_range =
                    (uu___177_7682.FStar_Tactics_Types.entry_range);
                  FStar_Tactics_Types.guard_policy =
                    (uu___177_7682.FStar_Tactics_Types.guard_policy);
                  FStar_Tactics_Types.freshness =
                    (uu___177_7682.FStar_Tactics_Types.freshness)
                })
         | uu____7683 -> fail "flip: less than 2 goals")
  
let (later : Prims.unit -> Prims.unit tac) =
  fun uu____7690  ->
    bind get
      (fun ps  ->
         match ps.FStar_Tactics_Types.goals with
         | [] -> ret ()
         | g::gs ->
             set
               (let uu___178_7703 = ps  in
                {
                  FStar_Tactics_Types.main_context =
                    (uu___178_7703.FStar_Tactics_Types.main_context);
                  FStar_Tactics_Types.main_goal =
                    (uu___178_7703.FStar_Tactics_Types.main_goal);
                  FStar_Tactics_Types.all_implicits =
                    (uu___178_7703.FStar_Tactics_Types.all_implicits);
                  FStar_Tactics_Types.goals = (FStar_List.append gs [g]);
                  FStar_Tactics_Types.smt_goals =
                    (uu___178_7703.FStar_Tactics_Types.smt_goals);
                  FStar_Tactics_Types.depth =
                    (uu___178_7703.FStar_Tactics_Types.depth);
                  FStar_Tactics_Types.__dump =
                    (uu___178_7703.FStar_Tactics_Types.__dump);
                  FStar_Tactics_Types.psc =
                    (uu___178_7703.FStar_Tactics_Types.psc);
                  FStar_Tactics_Types.entry_range =
                    (uu___178_7703.FStar_Tactics_Types.entry_range);
                  FStar_Tactics_Types.guard_policy =
                    (uu___178_7703.FStar_Tactics_Types.guard_policy);
                  FStar_Tactics_Types.freshness =
                    (uu___178_7703.FStar_Tactics_Types.freshness)
                }))
  
let (qed : Prims.unit -> Prims.unit tac) =
  fun uu____7708  ->
    bind get
      (fun ps  ->
         match ps.FStar_Tactics_Types.goals with
         | [] -> ret ()
         | uu____7715 -> fail "Not done!")
  
let (cases :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 tac)
  =
  fun t  ->
    let uu____7733 =
      let uu____7740 = cur_goal ()  in
      bind uu____7740
        (fun g  ->
           let uu____7750 = __tc g.FStar_Tactics_Types.context t  in
           bind uu____7750
             (fun uu____7786  ->
                match uu____7786 with
                | (t1,typ,guard) ->
                    let uu____7802 = FStar_Syntax_Util.head_and_args typ  in
                    (match uu____7802 with
                     | (hd1,args) ->
                         let uu____7845 =
                           let uu____7858 =
                             let uu____7859 = FStar_Syntax_Util.un_uinst hd1
                                in
                             uu____7859.FStar_Syntax_Syntax.n  in
                           (uu____7858, args)  in
                         (match uu____7845 with
                          | (FStar_Syntax_Syntax.Tm_fvar
                             fv,(p,uu____7878)::(q,uu____7880)::[]) when
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
                                let uu___179_7918 = g  in
                                let uu____7919 =
                                  FStar_TypeChecker_Env.push_bv
                                    g.FStar_Tactics_Types.context v_p
                                   in
                                {
                                  FStar_Tactics_Types.context = uu____7919;
                                  FStar_Tactics_Types.witness =
                                    (uu___179_7918.FStar_Tactics_Types.witness);
                                  FStar_Tactics_Types.goal_ty =
                                    (uu___179_7918.FStar_Tactics_Types.goal_ty);
                                  FStar_Tactics_Types.opts =
                                    (uu___179_7918.FStar_Tactics_Types.opts);
                                  FStar_Tactics_Types.is_guard =
                                    (uu___179_7918.FStar_Tactics_Types.is_guard)
                                }  in
                              let g2 =
                                let uu___180_7921 = g  in
                                let uu____7922 =
                                  FStar_TypeChecker_Env.push_bv
                                    g.FStar_Tactics_Types.context v_q
                                   in
                                {
                                  FStar_Tactics_Types.context = uu____7922;
                                  FStar_Tactics_Types.witness =
                                    (uu___180_7921.FStar_Tactics_Types.witness);
                                  FStar_Tactics_Types.goal_ty =
                                    (uu___180_7921.FStar_Tactics_Types.goal_ty);
                                  FStar_Tactics_Types.opts =
                                    (uu___180_7921.FStar_Tactics_Types.opts);
                                  FStar_Tactics_Types.is_guard =
                                    (uu___180_7921.FStar_Tactics_Types.is_guard)
                                }  in
                              bind __dismiss
                                (fun uu____7929  ->
                                   let uu____7930 = add_goals [g1; g2]  in
                                   bind uu____7930
                                     (fun uu____7939  ->
                                        let uu____7940 =
                                          let uu____7945 =
                                            FStar_Syntax_Syntax.bv_to_name
                                              v_p
                                             in
                                          let uu____7946 =
                                            FStar_Syntax_Syntax.bv_to_name
                                              v_q
                                             in
                                          (uu____7945, uu____7946)  in
                                        ret uu____7940))
                          | uu____7951 ->
                              let uu____7964 =
                                tts g.FStar_Tactics_Types.context typ  in
                              fail1 "Not a disjunction: %s" uu____7964))))
       in
    FStar_All.pipe_left (wrap_err "cases") uu____7733
  
let (set_options : Prims.string -> Prims.unit tac) =
  fun s  ->
    let uu____7992 = cur_goal ()  in
    bind uu____7992
      (fun g  ->
         FStar_Options.push ();
         (let uu____8005 = FStar_Util.smap_copy g.FStar_Tactics_Types.opts
             in
          FStar_Options.set uu____8005);
         (let res = FStar_Options.set_options FStar_Options.Set s  in
          let opts' = FStar_Options.peek ()  in
          FStar_Options.pop ();
          (match res with
           | FStar_Getopt.Success  ->
               let g' =
                 let uu___181_8012 = g  in
                 {
                   FStar_Tactics_Types.context =
                     (uu___181_8012.FStar_Tactics_Types.context);
                   FStar_Tactics_Types.witness =
                     (uu___181_8012.FStar_Tactics_Types.witness);
                   FStar_Tactics_Types.goal_ty =
                     (uu___181_8012.FStar_Tactics_Types.goal_ty);
                   FStar_Tactics_Types.opts = opts';
                   FStar_Tactics_Types.is_guard =
                     (uu___181_8012.FStar_Tactics_Types.is_guard)
                 }  in
               replace_cur g'
           | FStar_Getopt.Error err ->
               fail2 "Setting options `%s` failed: %s" s err
           | FStar_Getopt.Help  ->
               fail1 "Setting options `%s` failed (got `Help`?)" s)))
  
let (top_env : Prims.unit -> env tac) =
  fun uu____8018  ->
    bind get
      (fun ps  -> FStar_All.pipe_left ret ps.FStar_Tactics_Types.main_context)
  
let (cur_env : Prims.unit -> env tac) =
  fun uu____8029  ->
    let uu____8032 = cur_goal ()  in
    bind uu____8032
      (fun g  -> FStar_All.pipe_left ret g.FStar_Tactics_Types.context)
  
let (cur_goal' : Prims.unit -> FStar_Syntax_Syntax.term tac) =
  fun uu____8043  ->
    let uu____8046 = cur_goal ()  in
    bind uu____8046
      (fun g  -> FStar_All.pipe_left ret g.FStar_Tactics_Types.goal_ty)
  
let (cur_witness : Prims.unit -> FStar_Syntax_Syntax.term tac) =
  fun uu____8057  ->
    let uu____8060 = cur_goal ()  in
    bind uu____8060
      (fun g  -> FStar_All.pipe_left ret g.FStar_Tactics_Types.witness)
  
let (unquote :
  FStar_Reflection_Data.typ ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term tac)
  =
  fun ty  ->
    fun tm  ->
      let uu____8077 =
        let uu____8080 = cur_goal ()  in
        bind uu____8080
          (fun goal  ->
             let env =
               FStar_TypeChecker_Env.set_expected_typ
                 goal.FStar_Tactics_Types.context ty
                in
             let uu____8088 = __tc env tm  in
             bind uu____8088
               (fun uu____8108  ->
                  match uu____8108 with
                  | (tm1,typ,guard) ->
                      let uu____8120 =
                        proc_guard "unquote" env guard
                          goal.FStar_Tactics_Types.opts
                         in
                      bind uu____8120 (fun uu____8124  -> ret tm1)))
         in
      FStar_All.pipe_left (wrap_err "unquote") uu____8077
  
let (uvar_env :
  env ->
    FStar_Reflection_Data.typ FStar_Pervasives_Native.option ->
      FStar_Syntax_Syntax.term tac)
  =
  fun env  ->
    fun ty  ->
      let uu____8143 =
        match ty with
        | FStar_Pervasives_Native.Some ty1 -> ret ty1
        | FStar_Pervasives_Native.None  ->
            let uu____8149 =
              let uu____8150 = FStar_Syntax_Util.type_u ()  in
              FStar_All.pipe_left FStar_Pervasives_Native.fst uu____8150  in
            new_uvar "uvar_env.2" env uu____8149
         in
      bind uu____8143
        (fun typ  ->
           let uu____8162 = new_uvar "uvar_env" env typ  in
           bind uu____8162 (fun t  -> ret t))
  
let (unshelve : FStar_Syntax_Syntax.term -> Prims.unit tac) =
  fun t  ->
    let uu____8174 =
      bind get
        (fun ps  ->
           let env = ps.FStar_Tactics_Types.main_context  in
           let opts =
             match ps.FStar_Tactics_Types.goals with
             | g::uu____8191 -> g.FStar_Tactics_Types.opts
             | uu____8194 -> FStar_Options.peek ()  in
           let uu____8197 = FStar_Syntax_Util.head_and_args t  in
           match uu____8197 with
           | ({
                FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                  (uu____8214,typ);
                FStar_Syntax_Syntax.pos = uu____8216;
                FStar_Syntax_Syntax.vars = uu____8217;_},uu____8218)
               ->
               let uu____8263 =
                 let uu____8266 =
                   let uu____8267 = bnorm env t  in
                   let uu____8268 = bnorm env typ  in
                   {
                     FStar_Tactics_Types.context = env;
                     FStar_Tactics_Types.witness = uu____8267;
                     FStar_Tactics_Types.goal_ty = uu____8268;
                     FStar_Tactics_Types.opts = opts;
                     FStar_Tactics_Types.is_guard = false
                   }  in
                 [uu____8266]  in
               add_goals uu____8263
           | uu____8269 -> fail "not a uvar")
       in
    FStar_All.pipe_left (wrap_err "unshelve") uu____8174
  
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
          (fun uu____8316  ->
             let uu____8317 = FStar_Options.unsafe_tactic_exec ()  in
             if uu____8317
             then
               let s =
                 FStar_Util.launch_process true "tactic_launch" prog args
                   input (fun uu____8323  -> fun uu____8324  -> false)
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
        (fun uu____8338  ->
           let uu____8339 =
             FStar_Syntax_Syntax.gen_bv nm FStar_Pervasives_Native.None t  in
           ret uu____8339)
  
let (change : FStar_Reflection_Data.typ -> Prims.unit tac) =
  fun ty  ->
    let uu____8347 =
      mlog
        (fun uu____8352  ->
           let uu____8353 = FStar_Syntax_Print.term_to_string ty  in
           FStar_Util.print1 "change: ty = %s\n" uu____8353)
        (fun uu____8356  ->
           let uu____8357 = cur_goal ()  in
           bind uu____8357
             (fun g  ->
                let uu____8363 = __tc g.FStar_Tactics_Types.context ty  in
                bind uu____8363
                  (fun uu____8383  ->
                     match uu____8383 with
                     | (ty1,uu____8393,guard) ->
                         let uu____8395 =
                           proc_guard "change" g.FStar_Tactics_Types.context
                             guard g.FStar_Tactics_Types.opts
                            in
                         bind uu____8395
                           (fun uu____8400  ->
                              let uu____8401 =
                                do_unify g.FStar_Tactics_Types.context
                                  g.FStar_Tactics_Types.goal_ty ty1
                                 in
                              bind uu____8401
                                (fun bb  ->
                                   if bb
                                   then
                                     replace_cur
                                       (let uu___182_8410 = g  in
                                        {
                                          FStar_Tactics_Types.context =
                                            (uu___182_8410.FStar_Tactics_Types.context);
                                          FStar_Tactics_Types.witness =
                                            (uu___182_8410.FStar_Tactics_Types.witness);
                                          FStar_Tactics_Types.goal_ty = ty1;
                                          FStar_Tactics_Types.opts =
                                            (uu___182_8410.FStar_Tactics_Types.opts);
                                          FStar_Tactics_Types.is_guard =
                                            (uu___182_8410.FStar_Tactics_Types.is_guard)
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
                                      let uu____8417 =
                                        do_unify
                                          g.FStar_Tactics_Types.context ng
                                          nty
                                         in
                                      bind uu____8417
                                        (fun b  ->
                                           if b
                                           then
                                             replace_cur
                                               (let uu___183_8426 = g  in
                                                {
                                                  FStar_Tactics_Types.context
                                                    =
                                                    (uu___183_8426.FStar_Tactics_Types.context);
                                                  FStar_Tactics_Types.witness
                                                    =
                                                    (uu___183_8426.FStar_Tactics_Types.witness);
                                                  FStar_Tactics_Types.goal_ty
                                                    = ty1;
                                                  FStar_Tactics_Types.opts =
                                                    (uu___183_8426.FStar_Tactics_Types.opts);
                                                  FStar_Tactics_Types.is_guard
                                                    =
                                                    (uu___183_8426.FStar_Tactics_Types.is_guard)
                                                })
                                           else fail "not convertible")))))))
       in
    FStar_All.pipe_left (wrap_err "change") uu____8347
  
let rec last : 'a . 'a Prims.list -> 'a =
  fun l  ->
    match l with
    | [] -> failwith "last: empty list"
    | x::[] -> x
    | uu____8445::xs -> last xs
  
let rec init : 'a . 'a Prims.list -> 'a Prims.list =
  fun l  ->
    match l with
    | [] -> failwith "init: empty list"
    | x::[] -> []
    | x::xs -> let uu____8470 = init xs  in x :: uu____8470
  
let rec (inspect :
  FStar_Syntax_Syntax.term -> FStar_Reflection_Data.term_view tac) =
  fun t  ->
    let t1 = FStar_Syntax_Util.unascribe t  in
    let t2 = FStar_Syntax_Util.un_uinst t1  in
    match t2.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_meta (t3,uu____8485) -> inspect t3
    | FStar_Syntax_Syntax.Tm_name bv ->
        FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_Var bv)
    | FStar_Syntax_Syntax.Tm_bvar bv ->
        FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_BVar bv)
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_FVar fv)
    | FStar_Syntax_Syntax.Tm_app (hd1,[]) ->
        failwith "inspect: empty arguments on Tm_app"
    | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
        let uu____8542 = last args  in
        (match uu____8542 with
         | (a,q) ->
             let q' = FStar_Reflection_Basic.inspect_aqual q  in
             let uu____8564 =
               let uu____8565 =
                 let uu____8570 =
                   let uu____8573 =
                     let uu____8574 = init args  in
                     FStar_Syntax_Syntax.mk_Tm_app hd1 uu____8574  in
                   uu____8573 FStar_Pervasives_Native.None
                     t2.FStar_Syntax_Syntax.pos
                    in
                 (uu____8570, (a, q'))  in
               FStar_Reflection_Data.Tv_App uu____8565  in
             FStar_All.pipe_left ret uu____8564)
    | FStar_Syntax_Syntax.Tm_abs ([],uu____8595,uu____8596) ->
        failwith "inspect: empty arguments on Tm_abs"
    | FStar_Syntax_Syntax.Tm_abs (bs,t3,k) ->
        let uu____8640 = FStar_Syntax_Subst.open_term bs t3  in
        (match uu____8640 with
         | (bs1,t4) ->
             (match bs1 with
              | [] -> failwith "impossible"
              | b::bs2 ->
                  let uu____8673 =
                    let uu____8674 =
                      let uu____8679 = FStar_Syntax_Util.abs bs2 t4 k  in
                      (b, uu____8679)  in
                    FStar_Reflection_Data.Tv_Abs uu____8674  in
                  FStar_All.pipe_left ret uu____8673))
    | FStar_Syntax_Syntax.Tm_type uu____8686 ->
        FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_Type ())
    | FStar_Syntax_Syntax.Tm_arrow ([],k) ->
        failwith "inspect: empty binders on arrow"
    | FStar_Syntax_Syntax.Tm_arrow uu____8706 ->
        let uu____8719 = FStar_Syntax_Util.arrow_one t2  in
        (match uu____8719 with
         | FStar_Pervasives_Native.Some (b,c) ->
             FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_Arrow (b, c))
         | FStar_Pervasives_Native.None  -> failwith "impossible")
    | FStar_Syntax_Syntax.Tm_refine (bv,t3) ->
        let b = FStar_Syntax_Syntax.mk_binder bv  in
        let uu____8749 = FStar_Syntax_Subst.open_term [b] t3  in
        (match uu____8749 with
         | (b',t4) ->
             let b1 =
               match b' with
               | b'1::[] -> b'1
               | uu____8780 -> failwith "impossible"  in
             FStar_All.pipe_left ret
               (FStar_Reflection_Data.Tv_Refine
                  ((FStar_Pervasives_Native.fst b1), t4)))
    | FStar_Syntax_Syntax.Tm_constant c ->
        let uu____8788 =
          let uu____8789 = FStar_Reflection_Basic.inspect_const c  in
          FStar_Reflection_Data.Tv_Const uu____8789  in
        FStar_All.pipe_left ret uu____8788
    | FStar_Syntax_Syntax.Tm_uvar (u,t3) ->
        let uu____8818 =
          let uu____8819 =
            let uu____8824 =
              let uu____8825 = FStar_Syntax_Unionfind.uvar_id u  in
              FStar_BigInt.of_int_fs uu____8825  in
            (uu____8824, t3)  in
          FStar_Reflection_Data.Tv_Uvar uu____8819  in
        FStar_All.pipe_left ret uu____8818
    | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),t21) ->
        if lb.FStar_Syntax_Syntax.lbunivs <> []
        then FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown
        else
          (match lb.FStar_Syntax_Syntax.lbname with
           | FStar_Util.Inr uu____8853 ->
               FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown
           | FStar_Util.Inl bv ->
               let b = FStar_Syntax_Syntax.mk_binder bv  in
               let uu____8858 = FStar_Syntax_Subst.open_term [b] t21  in
               (match uu____8858 with
                | (bs,t22) ->
                    let b1 =
                      match bs with
                      | b1::[] -> b1
                      | uu____8889 ->
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
           | FStar_Util.Inr uu____8921 ->
               FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown
           | FStar_Util.Inl bv ->
               let uu____8925 = FStar_Syntax_Subst.open_let_rec [lb] t21  in
               (match uu____8925 with
                | (lbs,t22) ->
                    (match lbs with
                     | lb1::[] ->
                         (match lb1.FStar_Syntax_Syntax.lbname with
                          | FStar_Util.Inr uu____8945 ->
                              ret FStar_Reflection_Data.Tv_Unknown
                          | FStar_Util.Inl bv1 ->
                              FStar_All.pipe_left ret
                                (FStar_Reflection_Data.Tv_Let
                                   (true, bv1,
                                     (lb1.FStar_Syntax_Syntax.lbdef), t22)))
                     | uu____8951 ->
                         failwith
                           "impossible: open_term returned different amount of binders")))
    | FStar_Syntax_Syntax.Tm_match (t3,brs) ->
        let rec inspect_pat p =
          match p.FStar_Syntax_Syntax.v with
          | FStar_Syntax_Syntax.Pat_constant c ->
              let uu____9003 = FStar_Reflection_Basic.inspect_const c  in
              FStar_Reflection_Data.Pat_Constant uu____9003
          | FStar_Syntax_Syntax.Pat_cons (fv,ps) ->
              let uu____9022 =
                let uu____9029 =
                  FStar_List.map
                    (fun uu____9041  ->
                       match uu____9041 with
                       | (p1,uu____9049) -> inspect_pat p1) ps
                   in
                (fv, uu____9029)  in
              FStar_Reflection_Data.Pat_Cons uu____9022
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
            (fun uu___117_9103  ->
               match uu___117_9103 with
               | (pat,uu____9125,t4) ->
                   let uu____9143 = inspect_pat pat  in (uu____9143, t4))
            brs1
           in
        FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_Match (t3, brs2))
    | FStar_Syntax_Syntax.Tm_unknown  ->
        FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown
    | uu____9160 ->
        ((let uu____9162 =
            let uu____9167 =
              let uu____9168 = FStar_Syntax_Print.tag_of_term t2  in
              let uu____9169 = FStar_Syntax_Print.term_to_string t2  in
              FStar_Util.format2
                "inspect: outside of expected syntax (%s, %s)\n" uu____9168
                uu____9169
               in
            (FStar_Errors.Warning_CantInspect, uu____9167)  in
          FStar_Errors.log_issue t2.FStar_Syntax_Syntax.pos uu____9162);
         FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown)
  
let (pack : FStar_Reflection_Data.term_view -> FStar_Syntax_Syntax.term tac)
  =
  fun tv  ->
    match tv with
    | FStar_Reflection_Data.Tv_Var bv ->
        let uu____9180 = FStar_Syntax_Syntax.bv_to_name bv  in
        FStar_All.pipe_left ret uu____9180
    | FStar_Reflection_Data.Tv_BVar bv ->
        let uu____9184 = FStar_Syntax_Syntax.bv_to_tm bv  in
        FStar_All.pipe_left ret uu____9184
    | FStar_Reflection_Data.Tv_FVar fv ->
        let uu____9188 = FStar_Syntax_Syntax.fv_to_tm fv  in
        FStar_All.pipe_left ret uu____9188
    | FStar_Reflection_Data.Tv_App (l,(r,q)) ->
        let q' = FStar_Reflection_Basic.pack_aqual q  in
        let uu____9199 = FStar_Syntax_Util.mk_app l [(r, q')]  in
        FStar_All.pipe_left ret uu____9199
    | FStar_Reflection_Data.Tv_Abs (b,t) ->
        let uu____9220 =
          FStar_Syntax_Util.abs [b] t FStar_Pervasives_Native.None  in
        FStar_All.pipe_left ret uu____9220
    | FStar_Reflection_Data.Tv_Arrow (b,c) ->
        let uu____9225 = FStar_Syntax_Util.arrow [b] c  in
        FStar_All.pipe_left ret uu____9225
    | FStar_Reflection_Data.Tv_Type () ->
        FStar_All.pipe_left ret FStar_Syntax_Util.ktype
    | FStar_Reflection_Data.Tv_Refine (bv,t) ->
        let uu____9246 = FStar_Syntax_Util.refine bv t  in
        FStar_All.pipe_left ret uu____9246
    | FStar_Reflection_Data.Tv_Const c ->
        let uu____9258 =
          let uu____9261 =
            let uu____9264 =
              let uu____9265 = FStar_Reflection_Basic.pack_const c  in
              FStar_Syntax_Syntax.Tm_constant uu____9265  in
            FStar_Syntax_Syntax.mk uu____9264  in
          uu____9261 FStar_Pervasives_Native.None FStar_Range.dummyRange  in
        FStar_All.pipe_left ret uu____9258
    | FStar_Reflection_Data.Tv_Uvar (u,t) ->
        let uu____9279 =
          let uu____9282 = FStar_BigInt.to_int_fs u  in
          FStar_Syntax_Util.uvar_from_id uu____9282 t  in
        FStar_All.pipe_left ret uu____9279
    | FStar_Reflection_Data.Tv_Let (false ,bv,t1,t2) ->
        let lb =
          FStar_Syntax_Util.mk_letbinding (FStar_Util.Inl bv) []
            bv.FStar_Syntax_Syntax.sort FStar_Parser_Const.effect_Tot_lid t1
            [] FStar_Range.dummyRange
           in
        let uu____9297 =
          let uu____9300 =
            let uu____9303 =
              let uu____9304 =
                let uu____9317 =
                  let uu____9318 =
                    let uu____9319 = FStar_Syntax_Syntax.mk_binder bv  in
                    [uu____9319]  in
                  FStar_Syntax_Subst.close uu____9318 t2  in
                ((false, [lb]), uu____9317)  in
              FStar_Syntax_Syntax.Tm_let uu____9304  in
            FStar_Syntax_Syntax.mk uu____9303  in
          uu____9300 FStar_Pervasives_Native.None FStar_Range.dummyRange  in
        FStar_All.pipe_left ret uu____9297
    | FStar_Reflection_Data.Tv_Let (true ,bv,t1,t2) ->
        let lb =
          FStar_Syntax_Util.mk_letbinding (FStar_Util.Inl bv) []
            bv.FStar_Syntax_Syntax.sort FStar_Parser_Const.effect_Tot_lid t1
            [] FStar_Range.dummyRange
           in
        let uu____9345 = FStar_Syntax_Subst.close_let_rec [lb] t2  in
        (match uu____9345 with
         | (lbs,body) ->
             let uu____9360 =
               FStar_Syntax_Syntax.mk
                 (FStar_Syntax_Syntax.Tm_let ((true, lbs), body))
                 FStar_Pervasives_Native.None FStar_Range.dummyRange
                in
             FStar_All.pipe_left ret uu____9360)
    | FStar_Reflection_Data.Tv_Match (t,brs) ->
        let wrap v1 =
          {
            FStar_Syntax_Syntax.v = v1;
            FStar_Syntax_Syntax.p = FStar_Range.dummyRange
          }  in
        let rec pack_pat p =
          match p with
          | FStar_Reflection_Data.Pat_Constant c ->
              let uu____9396 =
                let uu____9397 = FStar_Reflection_Basic.pack_const c  in
                FStar_Syntax_Syntax.Pat_constant uu____9397  in
              FStar_All.pipe_left wrap uu____9396
          | FStar_Reflection_Data.Pat_Cons (fv,ps) ->
              let uu____9406 =
                let uu____9407 =
                  let uu____9420 =
                    FStar_List.map
                      (fun p1  ->
                         let uu____9434 = pack_pat p1  in (uu____9434, false))
                      ps
                     in
                  (fv, uu____9420)  in
                FStar_Syntax_Syntax.Pat_cons uu____9407  in
              FStar_All.pipe_left wrap uu____9406
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
            (fun uu___118_9484  ->
               match uu___118_9484 with
               | (pat,t1) ->
                   let uu____9501 = pack_pat pat  in
                   (uu____9501, FStar_Pervasives_Native.None, t1)) brs
           in
        let brs2 = FStar_List.map FStar_Syntax_Subst.close_branch brs1  in
        let uu____9511 =
          FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_match (t, brs2))
            FStar_Pervasives_Native.None FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____9511
    | FStar_Reflection_Data.Tv_AscribedT (e,t,tacopt) ->
        let uu____9531 =
          FStar_Syntax_Syntax.mk
            (FStar_Syntax_Syntax.Tm_ascribed
               (e, ((FStar_Util.Inl t), tacopt),
                 FStar_Pervasives_Native.None)) FStar_Pervasives_Native.None
            FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____9531
    | FStar_Reflection_Data.Tv_AscribedC (e,c,tacopt) ->
        let uu____9573 =
          FStar_Syntax_Syntax.mk
            (FStar_Syntax_Syntax.Tm_ascribed
               (e, ((FStar_Util.Inr c), tacopt),
                 FStar_Pervasives_Native.None)) FStar_Pervasives_Native.None
            FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____9573
    | FStar_Reflection_Data.Tv_Unknown  ->
        let uu____9608 =
          FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown
            FStar_Pervasives_Native.None FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____9608
  
let (goal_of_goal_ty :
  env ->
    FStar_Reflection_Data.typ ->
      (FStar_Tactics_Types.goal,FStar_TypeChecker_Env.guard_t)
        FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun typ  ->
      let uu____9633 =
        FStar_TypeChecker_Util.new_implicit_var "proofstate_of_goal_ty"
          typ.FStar_Syntax_Syntax.pos env typ
         in
      match uu____9633 with
      | (u,uu____9651,g_u) ->
          let g =
            let uu____9666 = FStar_Options.peek ()  in
            {
              FStar_Tactics_Types.context = env;
              FStar_Tactics_Types.witness = u;
              FStar_Tactics_Types.goal_ty = typ;
              FStar_Tactics_Types.opts = uu____9666;
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
      let uu____9677 = goal_of_goal_ty env typ  in
      match uu____9677 with
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
  