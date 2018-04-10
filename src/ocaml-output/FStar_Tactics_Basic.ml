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
           let uu____177 = run t1 p  in
           match uu____177 with
           | FStar_Tactics_Result.Success (a,q) ->
               let uu____184 = t2 a  in run uu____184 q
           | FStar_Tactics_Result.Failed (msg,q) ->
               FStar_Tactics_Result.Failed (msg, q))
  
let (get : FStar_Tactics_Types.proofstate tac) =
  mk_tac (fun p  -> FStar_Tactics_Result.Success (p, p)) 
let (idtac : unit tac) = ret () 
let (goal_to_string : FStar_Tactics_Types.goal -> Prims.string) =
  fun g  ->
    let g_binders =
      let uu____203 =
        FStar_TypeChecker_Env.all_binders g.FStar_Tactics_Types.context  in
      FStar_All.pipe_right uu____203
        (FStar_Syntax_Print.binders_to_string ", ")
       in
    let w = bnorm g.FStar_Tactics_Types.context g.FStar_Tactics_Types.witness
       in
    let t = bnorm g.FStar_Tactics_Types.context g.FStar_Tactics_Types.goal_ty
       in
    let uu____206 = tts g.FStar_Tactics_Types.context w  in
    let uu____207 = tts g.FStar_Tactics_Types.context t  in
    FStar_Util.format3 "%s |- %s : %s" g_binders uu____206 uu____207
  
let (tacprint : Prims.string -> unit) =
  fun s  -> FStar_Util.print1 "TAC>> %s\n" s 
let (tacprint1 : Prims.string -> Prims.string -> unit) =
  fun s  ->
    fun x  ->
      let uu____223 = FStar_Util.format1 s x  in
      FStar_Util.print1 "TAC>> %s\n" uu____223
  
let (tacprint2 : Prims.string -> Prims.string -> Prims.string -> unit) =
  fun s  ->
    fun x  ->
      fun y  ->
        let uu____239 = FStar_Util.format2 s x y  in
        FStar_Util.print1 "TAC>> %s\n" uu____239
  
let (tacprint3 :
  Prims.string -> Prims.string -> Prims.string -> Prims.string -> unit) =
  fun s  ->
    fun x  ->
      fun y  ->
        fun z  ->
          let uu____260 = FStar_Util.format3 s x y z  in
          FStar_Util.print1 "TAC>> %s\n" uu____260
  
let (comp_to_typ : FStar_Syntax_Syntax.comp -> FStar_Reflection_Data.typ) =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Total (t,uu____267) -> t
    | FStar_Syntax_Syntax.GTotal (t,uu____277) -> t
    | FStar_Syntax_Syntax.Comp ct -> ct.FStar_Syntax_Syntax.result_typ
  
let (is_irrelevant : FStar_Tactics_Types.goal -> Prims.bool) =
  fun g  ->
    let uu____292 =
      let uu____297 =
        FStar_TypeChecker_Normalize.unfold_whnf g.FStar_Tactics_Types.context
          g.FStar_Tactics_Types.goal_ty
         in
      FStar_Syntax_Util.un_squash uu____297  in
    match uu____292 with
    | FStar_Pervasives_Native.Some t -> true
    | uu____303 -> false
  
let (print : Prims.string -> unit tac) =
  fun msg  -> let uu____317 = tacprint msg  in ret () 
let (debug : Prims.string -> unit tac) =
  fun msg  ->
    bind get
      (fun ps  ->
         let uu____330 =
           let uu____331 =
             let uu____332 =
               FStar_Ident.string_of_lid
                 (ps.FStar_Tactics_Types.main_context).FStar_TypeChecker_Env.curmodule
                in
             FStar_Options.debug_module uu____332  in
           if uu____331 then tacprint msg else ()  in
         ret ())
  
let dump_goal : 'Auu____340 . 'Auu____340 -> FStar_Tactics_Types.goal -> unit
  =
  fun ps  ->
    fun goal  ->
      let uu____351 =
        let uu____352 = goal_to_string goal  in tacprint uu____352  in
      ()
  
let (dump_cur : FStar_Tactics_Types.proofstate -> Prims.string -> unit) =
  fun ps  ->
    fun msg  ->
      match ps.FStar_Tactics_Types.goals with
      | [] -> tacprint1 "No more goals (%s)" msg
      | h::uu____364 ->
          let uu____367 = tacprint1 "Current goal (%s):" msg  in
          let uu____368 = FStar_List.hd ps.FStar_Tactics_Types.goals  in
          dump_goal ps uu____368
  
let (ps_to_string :
  (Prims.string,FStar_Tactics_Types.proofstate)
    FStar_Pervasives_Native.tuple2 -> Prims.string)
  =
  fun uu____377  ->
    match uu____377 with
    | (msg,ps) ->
        let uu____384 =
          let uu____387 =
            let uu____388 =
              FStar_Util.string_of_int ps.FStar_Tactics_Types.depth  in
            FStar_Util.format2 "State dump @ depth %s (%s):\n" uu____388 msg
             in
          let uu____389 =
            let uu____392 =
              let uu____393 =
                FStar_Range.string_of_range
                  ps.FStar_Tactics_Types.entry_range
                 in
              FStar_Util.format1 "Location: %s\n" uu____393  in
            let uu____394 =
              let uu____397 =
                let uu____398 =
                  FStar_Util.string_of_int
                    (FStar_List.length ps.FStar_Tactics_Types.goals)
                   in
                let uu____399 =
                  let uu____400 =
                    FStar_List.map goal_to_string
                      ps.FStar_Tactics_Types.goals
                     in
                  FStar_String.concat "\n" uu____400  in
                FStar_Util.format2 "ACTIVE goals (%s):\n%s\n" uu____398
                  uu____399
                 in
              let uu____403 =
                let uu____406 =
                  let uu____407 =
                    FStar_Util.string_of_int
                      (FStar_List.length ps.FStar_Tactics_Types.smt_goals)
                     in
                  let uu____408 =
                    let uu____409 =
                      FStar_List.map goal_to_string
                        ps.FStar_Tactics_Types.smt_goals
                       in
                    FStar_String.concat "\n" uu____409  in
                  FStar_Util.format2 "SMT goals (%s):\n%s\n" uu____407
                    uu____408
                   in
                [uu____406]  in
              uu____397 :: uu____403  in
            uu____392 :: uu____394  in
          uu____387 :: uu____389  in
        FStar_String.concat "" uu____384
  
let (goal_to_json : FStar_Tactics_Types.goal -> FStar_Util.json) =
  fun g  ->
    let g_binders =
      let uu____418 =
        FStar_TypeChecker_Env.all_binders g.FStar_Tactics_Types.context  in
      let uu____419 =
        let uu____424 =
          FStar_TypeChecker_Env.dsenv g.FStar_Tactics_Types.context  in
        FStar_Syntax_Print.binders_to_json uu____424  in
      FStar_All.pipe_right uu____418 uu____419  in
    let uu____425 =
      let uu____432 =
        let uu____439 =
          let uu____444 =
            let uu____445 =
              let uu____452 =
                let uu____457 =
                  let uu____458 =
                    tts g.FStar_Tactics_Types.context
                      g.FStar_Tactics_Types.witness
                     in
                  FStar_Util.JsonStr uu____458  in
                ("witness", uu____457)  in
              let uu____459 =
                let uu____466 =
                  let uu____471 =
                    let uu____472 =
                      tts g.FStar_Tactics_Types.context
                        g.FStar_Tactics_Types.goal_ty
                       in
                    FStar_Util.JsonStr uu____472  in
                  ("type", uu____471)  in
                [uu____466]  in
              uu____452 :: uu____459  in
            FStar_Util.JsonAssoc uu____445  in
          ("goal", uu____444)  in
        [uu____439]  in
      ("hyps", g_binders) :: uu____432  in
    FStar_Util.JsonAssoc uu____425
  
let (ps_to_json :
  (Prims.string,FStar_Tactics_Types.proofstate)
    FStar_Pervasives_Native.tuple2 -> FStar_Util.json)
  =
  fun uu____505  ->
    match uu____505 with
    | (msg,ps) ->
        let uu____512 =
          let uu____519 =
            let uu____526 =
              let uu____533 =
                let uu____540 =
                  let uu____545 =
                    let uu____546 =
                      FStar_List.map goal_to_json
                        ps.FStar_Tactics_Types.goals
                       in
                    FStar_Util.JsonList uu____546  in
                  ("goals", uu____545)  in
                let uu____549 =
                  let uu____556 =
                    let uu____561 =
                      let uu____562 =
                        FStar_List.map goal_to_json
                          ps.FStar_Tactics_Types.smt_goals
                         in
                      FStar_Util.JsonList uu____562  in
                    ("smt-goals", uu____561)  in
                  [uu____556]  in
                uu____540 :: uu____549  in
              ("depth", (FStar_Util.JsonInt (ps.FStar_Tactics_Types.depth)))
                :: uu____533
               in
            ("label", (FStar_Util.JsonStr msg)) :: uu____526  in
          let uu____585 =
            if ps.FStar_Tactics_Types.entry_range <> FStar_Range.dummyRange
            then
              let uu____598 =
                let uu____603 =
                  FStar_Range.json_of_def_range
                    ps.FStar_Tactics_Types.entry_range
                   in
                ("location", uu____603)  in
              [uu____598]
            else []  in
          FStar_List.append uu____519 uu____585  in
        FStar_Util.JsonAssoc uu____512
  
let (dump_proofstate :
  FStar_Tactics_Types.proofstate -> Prims.string -> unit) =
  fun ps  ->
    fun msg  ->
      FStar_Options.with_saved_options
        (fun uu____633  ->
           let uu____634 =
             FStar_Options.set_option "print_effect_args"
               (FStar_Options.Bool true)
              in
           FStar_Util.print_generic "proof-state" ps_to_string ps_to_json
             (msg, ps))
  
let (print_proof_state1 : Prims.string -> unit tac) =
  fun msg  ->
    mk_tac
      (fun ps  ->
         let psc = ps.FStar_Tactics_Types.psc  in
         let subst1 = FStar_TypeChecker_Normalize.psc_subst psc  in
         let uu____655 =
           let uu____656 = FStar_Tactics_Types.subst_proof_state subst1 ps
              in
           dump_cur uu____656 msg  in
         FStar_Tactics_Result.Success ((), ps))
  
let (print_proof_state : Prims.string -> unit tac) =
  fun msg  ->
    mk_tac
      (fun ps  ->
         let psc = ps.FStar_Tactics_Types.psc  in
         let subst1 = FStar_TypeChecker_Normalize.psc_subst psc  in
         let uu____673 =
           let uu____674 = FStar_Tactics_Types.subst_proof_state subst1 ps
              in
           dump_proofstate uu____674 msg  in
         FStar_Tactics_Result.Success ((), ps))
  
let (tac_verb_dbg : Prims.bool FStar_Pervasives_Native.option FStar_ST.ref) =
  FStar_Util.mk_ref FStar_Pervasives_Native.None 
let rec (log : FStar_Tactics_Types.proofstate -> (unit -> unit) -> unit) =
  fun ps  ->
    fun f  ->
      let uu____707 = FStar_ST.op_Bang tac_verb_dbg  in
      match uu____707 with
      | FStar_Pervasives_Native.None  ->
          let uu____737 =
            let uu____738 =
              let uu____741 =
                FStar_TypeChecker_Env.debug
                  ps.FStar_Tactics_Types.main_context
                  (FStar_Options.Other "TacVerbose")
                 in
              FStar_Pervasives_Native.Some uu____741  in
            FStar_ST.op_Colon_Equals tac_verb_dbg uu____738  in
          log ps f
      | FStar_Pervasives_Native.Some (true ) -> f ()
      | FStar_Pervasives_Native.Some (false ) -> ()
  
let mlog : 'a . (unit -> unit) -> (unit -> 'a tac) -> 'a tac =
  fun f  ->
    fun cont  -> bind get (fun ps  -> let uu____805 = log ps f  in cont ())
  
let fail : 'a . Prims.string -> 'a tac =
  fun msg  ->
    mk_tac
      (fun ps  ->
         let uu____821 =
           let uu____822 =
             FStar_TypeChecker_Env.debug ps.FStar_Tactics_Types.main_context
               (FStar_Options.Other "TacFail")
              in
           if uu____822
           then dump_proofstate ps (Prims.strcat "TACTIC FAILING: " msg)
           else ()  in
         FStar_Tactics_Result.Failed (msg, ps))
  
let fail1 : 'Auu____830 . Prims.string -> Prims.string -> 'Auu____830 tac =
  fun msg  ->
    fun x  -> let uu____843 = FStar_Util.format1 msg x  in fail uu____843
  
let fail2 :
  'Auu____852 .
    Prims.string -> Prims.string -> Prims.string -> 'Auu____852 tac
  =
  fun msg  ->
    fun x  ->
      fun y  -> let uu____870 = FStar_Util.format2 msg x y  in fail uu____870
  
let fail3 :
  'Auu____881 .
    Prims.string ->
      Prims.string -> Prims.string -> Prims.string -> 'Auu____881 tac
  =
  fun msg  ->
    fun x  ->
      fun y  ->
        fun z  ->
          let uu____904 = FStar_Util.format3 msg x y z  in fail uu____904
  
let fail4 :
  'Auu____917 .
    Prims.string ->
      Prims.string ->
        Prims.string -> Prims.string -> Prims.string -> 'Auu____917 tac
  =
  fun msg  ->
    fun x  ->
      fun y  ->
        fun z  ->
          fun w  ->
            let uu____945 = FStar_Util.format4 msg x y z w  in fail uu____945
  
let trytac' : 'a . 'a tac -> (Prims.string,'a) FStar_Util.either tac =
  fun t  ->
    mk_tac
      (fun ps  ->
         let tx = FStar_Syntax_Unionfind.new_transaction ()  in
         let uu____978 = run t ps  in
         match uu____978 with
         | FStar_Tactics_Result.Success (a,q) ->
             let uu____989 = FStar_Syntax_Unionfind.commit tx  in
             FStar_Tactics_Result.Success ((FStar_Util.Inr a), q)
         | FStar_Tactics_Result.Failed (m,q) ->
             let uu____1000 = FStar_Syntax_Unionfind.rollback tx  in
             let ps1 =
               let uu___65_1002 = ps  in
               {
                 FStar_Tactics_Types.main_context =
                   (uu___65_1002.FStar_Tactics_Types.main_context);
                 FStar_Tactics_Types.main_goal =
                   (uu___65_1002.FStar_Tactics_Types.main_goal);
                 FStar_Tactics_Types.all_implicits =
                   (uu___65_1002.FStar_Tactics_Types.all_implicits);
                 FStar_Tactics_Types.goals =
                   (uu___65_1002.FStar_Tactics_Types.goals);
                 FStar_Tactics_Types.smt_goals =
                   (uu___65_1002.FStar_Tactics_Types.smt_goals);
                 FStar_Tactics_Types.depth =
                   (uu___65_1002.FStar_Tactics_Types.depth);
                 FStar_Tactics_Types.__dump =
                   (uu___65_1002.FStar_Tactics_Types.__dump);
                 FStar_Tactics_Types.psc =
                   (uu___65_1002.FStar_Tactics_Types.psc);
                 FStar_Tactics_Types.entry_range =
                   (uu___65_1002.FStar_Tactics_Types.entry_range);
                 FStar_Tactics_Types.guard_policy =
                   (uu___65_1002.FStar_Tactics_Types.guard_policy);
                 FStar_Tactics_Types.freshness =
                   (q.FStar_Tactics_Types.freshness)
               }  in
             FStar_Tactics_Result.Success ((FStar_Util.Inl m), ps1))
  
let trytac : 'a . 'a tac -> 'a FStar_Pervasives_Native.option tac =
  fun t  ->
    let uu____1029 = trytac' t  in
    bind uu____1029
      (fun r  ->
         match r with
         | FStar_Util.Inr v1 -> ret (FStar_Pervasives_Native.Some v1)
         | FStar_Util.Inl uu____1056 -> ret FStar_Pervasives_Native.None)
  
let trytac_exn : 'a . 'a tac -> 'a FStar_Pervasives_Native.option tac =
  fun t  ->
    mk_tac
      (fun ps  ->
         try let uu____1092 = trytac t  in run uu____1092 ps
         with
         | FStar_Errors.Err (uu____1108,msg) ->
             let uu____1110 =
               log ps
                 (fun uu____1112  ->
                    FStar_Util.print1 "trytac_exn error: (%s)" msg)
                in
             FStar_Tactics_Result.Success (FStar_Pervasives_Native.None, ps)
         | FStar_Errors.Error (uu____1117,msg,uu____1119) ->
             let uu____1120 =
               log ps
                 (fun uu____1122  ->
                    FStar_Util.print1 "trytac_exn error: (%s)" msg)
                in
             FStar_Tactics_Result.Success (FStar_Pervasives_Native.None, ps))
  
let wrap_err : 'a . Prims.string -> 'a tac -> 'a tac =
  fun pref  ->
    fun t  ->
      mk_tac
        (fun ps  ->
           let uu____1155 = run t ps  in
           match uu____1155 with
           | FStar_Tactics_Result.Success (a,q) ->
               FStar_Tactics_Result.Success (a, q)
           | FStar_Tactics_Result.Failed (msg,q) ->
               FStar_Tactics_Result.Failed
                 ((Prims.strcat pref (Prims.strcat ": " msg)), q))
  
let (set : FStar_Tactics_Types.proofstate -> unit tac) =
  fun p  -> mk_tac (fun uu____1174  -> FStar_Tactics_Result.Success ((), p)) 
let (__do_unify :
  env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.bool tac)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____1194 =
          let uu____1195 =
            FStar_TypeChecker_Env.debug env (FStar_Options.Other "1346")  in
          if uu____1195
          then
            let uu____1196 = FStar_Syntax_Print.term_to_string t1  in
            let uu____1197 = FStar_Syntax_Print.term_to_string t2  in
            FStar_Util.print2 "%%%%%%%%do_unify %s =? %s\n" uu____1196
              uu____1197
          else ()  in
        try
          let res = FStar_TypeChecker_Rel.teq_nosmt env t1 t2  in
          let uu____1208 =
            let uu____1209 =
              FStar_TypeChecker_Env.debug env (FStar_Options.Other "1346")
               in
            if uu____1209
            then
              let uu____1210 = FStar_Util.string_of_bool res  in
              let uu____1211 = FStar_Syntax_Print.term_to_string t1  in
              let uu____1212 = FStar_Syntax_Print.term_to_string t2  in
              FStar_Util.print3 "%%%%%%%%do_unify (RESULT %s) %s =? %s\n"
                uu____1210 uu____1211 uu____1212
            else ()  in
          ret res
        with
        | FStar_Errors.Err (uu____1220,msg) ->
            mlog
              (fun uu____1223  ->
                 FStar_Util.print1 ">> do_unify error, (%s)\n" msg)
              (fun uu____1225  -> ret false)
        | FStar_Errors.Error (uu____1226,msg,r) ->
            mlog
              (fun uu____1231  ->
                 let uu____1232 = FStar_Range.string_of_range r  in
                 FStar_Util.print2 ">> do_unify error, (%s) at (%s)\n" msg
                   uu____1232) (fun uu____1234  -> ret false)
  
let (do_unify :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.bool tac)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        bind idtac
          (fun uu____1257  ->
             let uu____1258 =
               let uu____1259 =
                 FStar_TypeChecker_Env.debug env (FStar_Options.Other "1346")
                  in
               if uu____1259
               then
                 let uu____1260 = FStar_Options.push ()  in
                 let uu____1261 =
                   FStar_Options.set_options FStar_Options.Set
                     "--debug_level Rel --debug_level RelCheck"
                    in
                 ()
               else ()  in
             let uu____1263 =
               let uu____1266 = __do_unify env t1 t2  in
               bind uu____1266
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
             bind uu____1263
               (fun r  ->
                  let uu____1281 =
                    let uu____1282 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "1346")
                       in
                    if uu____1282 then FStar_Options.pop () else ()  in
                  ret r))
  
let (trysolve :
  FStar_Tactics_Types.goal -> FStar_Syntax_Syntax.term -> Prims.bool tac) =
  fun goal  ->
    fun solution  ->
      do_unify goal.FStar_Tactics_Types.context solution
        goal.FStar_Tactics_Types.witness
  
let (__dismiss : unit tac) =
  bind get
    (fun p  ->
       let uu____1303 =
         let uu___70_1304 = p  in
         let uu____1305 = FStar_List.tl p.FStar_Tactics_Types.goals  in
         {
           FStar_Tactics_Types.main_context =
             (uu___70_1304.FStar_Tactics_Types.main_context);
           FStar_Tactics_Types.main_goal =
             (uu___70_1304.FStar_Tactics_Types.main_goal);
           FStar_Tactics_Types.all_implicits =
             (uu___70_1304.FStar_Tactics_Types.all_implicits);
           FStar_Tactics_Types.goals = uu____1305;
           FStar_Tactics_Types.smt_goals =
             (uu___70_1304.FStar_Tactics_Types.smt_goals);
           FStar_Tactics_Types.depth =
             (uu___70_1304.FStar_Tactics_Types.depth);
           FStar_Tactics_Types.__dump =
             (uu___70_1304.FStar_Tactics_Types.__dump);
           FStar_Tactics_Types.psc = (uu___70_1304.FStar_Tactics_Types.psc);
           FStar_Tactics_Types.entry_range =
             (uu___70_1304.FStar_Tactics_Types.entry_range);
           FStar_Tactics_Types.guard_policy =
             (uu___70_1304.FStar_Tactics_Types.guard_policy);
           FStar_Tactics_Types.freshness =
             (uu___70_1304.FStar_Tactics_Types.freshness)
         }  in
       set uu____1303)
  
let (dismiss : unit -> unit tac) =
  fun uu____1314  ->
    bind get
      (fun p  ->
         match p.FStar_Tactics_Types.goals with
         | [] -> fail "dismiss: no more goals"
         | uu____1321 -> __dismiss)
  
let (solve :
  FStar_Tactics_Types.goal -> FStar_Syntax_Syntax.term -> unit tac) =
  fun goal  ->
    fun solution  ->
      let uu____1338 = trysolve goal solution  in
      bind uu____1338
        (fun b  ->
           if b
           then __dismiss
           else
             (let uu____1346 =
                let uu____1347 =
                  tts goal.FStar_Tactics_Types.context solution  in
                let uu____1348 =
                  tts goal.FStar_Tactics_Types.context
                    goal.FStar_Tactics_Types.witness
                   in
                let uu____1349 =
                  tts goal.FStar_Tactics_Types.context
                    goal.FStar_Tactics_Types.goal_ty
                   in
                FStar_Util.format3 "%s does not solve %s : %s" uu____1347
                  uu____1348 uu____1349
                 in
              fail uu____1346))
  
let (dismiss_all : unit tac) =
  bind get
    (fun p  ->
       set
         (let uu___71_1356 = p  in
          {
            FStar_Tactics_Types.main_context =
              (uu___71_1356.FStar_Tactics_Types.main_context);
            FStar_Tactics_Types.main_goal =
              (uu___71_1356.FStar_Tactics_Types.main_goal);
            FStar_Tactics_Types.all_implicits =
              (uu___71_1356.FStar_Tactics_Types.all_implicits);
            FStar_Tactics_Types.goals = [];
            FStar_Tactics_Types.smt_goals =
              (uu___71_1356.FStar_Tactics_Types.smt_goals);
            FStar_Tactics_Types.depth =
              (uu___71_1356.FStar_Tactics_Types.depth);
            FStar_Tactics_Types.__dump =
              (uu___71_1356.FStar_Tactics_Types.__dump);
            FStar_Tactics_Types.psc = (uu___71_1356.FStar_Tactics_Types.psc);
            FStar_Tactics_Types.entry_range =
              (uu___71_1356.FStar_Tactics_Types.entry_range);
            FStar_Tactics_Types.guard_policy =
              (uu___71_1356.FStar_Tactics_Types.guard_policy);
            FStar_Tactics_Types.freshness =
              (uu___71_1356.FStar_Tactics_Types.freshness)
          }))
  
let (nwarn : Prims.int FStar_ST.ref) =
  FStar_Util.mk_ref (Prims.parse_int "0") 
let (check_valid_goal : FStar_Tactics_Types.goal -> unit) =
  fun g  ->
    let uu____1375 = FStar_Options.defensive ()  in
    if uu____1375
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
        let uu____1391 = FStar_TypeChecker_Env.pop_bv e  in
        match uu____1391 with
        | FStar_Pervasives_Native.None  -> b3
        | FStar_Pervasives_Native.Some (bv,e1) ->
            let b4 =
              b3 &&
                (FStar_TypeChecker_Env.closed e1 bv.FStar_Syntax_Syntax.sort)
               in
            aux b4 e1
         in
      let uu____1409 =
        (let uu____1412 = aux b2 env  in Prims.op_Negation uu____1412) &&
          (let uu____1414 = FStar_ST.op_Bang nwarn  in
           uu____1414 < (Prims.parse_int "5"))
         in
      (if uu____1409
       then
         let uu____1438 =
           let uu____1439 =
             let uu____1444 =
               let uu____1445 = goal_to_string g  in
               FStar_Util.format1
                 "The following goal is ill-formed. Keeping calm and carrying on...\n<%s>\n\n"
                 uu____1445
                in
             (FStar_Errors.Warning_IllFormedGoal, uu____1444)  in
           FStar_Errors.log_issue
             (g.FStar_Tactics_Types.goal_ty).FStar_Syntax_Syntax.pos
             uu____1439
            in
         let uu____1446 =
           let uu____1447 = FStar_ST.op_Bang nwarn  in
           uu____1447 + (Prims.parse_int "1")  in
         FStar_ST.op_Colon_Equals nwarn uu____1446
       else ())
    else ()
  
let (add_goals : FStar_Tactics_Types.goal Prims.list -> unit tac) =
  fun gs  ->
    bind get
      (fun p  ->
         let uu____1512 = FStar_List.iter check_valid_goal gs  in
         set
           (let uu___72_1515 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___72_1515.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___72_1515.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___72_1515.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (FStar_List.append gs p.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (uu___72_1515.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___72_1515.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___72_1515.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___72_1515.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___72_1515.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___72_1515.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___72_1515.FStar_Tactics_Types.freshness)
            }))
  
let (add_smt_goals : FStar_Tactics_Types.goal Prims.list -> unit tac) =
  fun gs  ->
    bind get
      (fun p  ->
         let uu____1532 = FStar_List.iter check_valid_goal gs  in
         set
           (let uu___73_1535 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___73_1535.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___73_1535.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___73_1535.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___73_1535.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (FStar_List.append gs p.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___73_1535.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___73_1535.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___73_1535.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___73_1535.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___73_1535.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___73_1535.FStar_Tactics_Types.freshness)
            }))
  
let (push_goals : FStar_Tactics_Types.goal Prims.list -> unit tac) =
  fun gs  ->
    bind get
      (fun p  ->
         let uu____1552 = FStar_List.iter check_valid_goal gs  in
         set
           (let uu___74_1555 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___74_1555.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___74_1555.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___74_1555.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (FStar_List.append p.FStar_Tactics_Types.goals gs);
              FStar_Tactics_Types.smt_goals =
                (uu___74_1555.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___74_1555.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___74_1555.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___74_1555.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___74_1555.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___74_1555.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___74_1555.FStar_Tactics_Types.freshness)
            }))
  
let (push_smt_goals : FStar_Tactics_Types.goal Prims.list -> unit tac) =
  fun gs  ->
    bind get
      (fun p  ->
         let uu____1572 = FStar_List.iter check_valid_goal gs  in
         set
           (let uu___75_1575 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___75_1575.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___75_1575.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___75_1575.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___75_1575.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (FStar_List.append p.FStar_Tactics_Types.smt_goals gs);
              FStar_Tactics_Types.depth =
                (uu___75_1575.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___75_1575.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___75_1575.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___75_1575.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___75_1575.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___75_1575.FStar_Tactics_Types.freshness)
            }))
  
let (replace_cur : FStar_Tactics_Types.goal -> unit tac) =
  fun g  -> bind __dismiss (fun uu____1586  -> add_goals [g]) 
let (add_implicits : implicits -> unit tac) =
  fun i  ->
    bind get
      (fun p  ->
         set
           (let uu___76_1600 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___76_1600.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___76_1600.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (FStar_List.append i p.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___76_1600.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (uu___76_1600.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___76_1600.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___76_1600.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___76_1600.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___76_1600.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___76_1600.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___76_1600.FStar_Tactics_Types.freshness)
            }))
  
let (new_uvar :
  Prims.string ->
    env -> FStar_Reflection_Data.typ -> FStar_Syntax_Syntax.term tac)
  =
  fun reason  ->
    fun env  ->
      fun typ  ->
        let uu____1632 =
          FStar_TypeChecker_Util.new_implicit_var reason
            typ.FStar_Syntax_Syntax.pos env typ
           in
        match uu____1632 with
        | (u,uu____1648,g_u) ->
            let uu____1662 =
              add_implicits g_u.FStar_TypeChecker_Env.implicits  in
            bind uu____1662 (fun uu____1666  -> ret u)
  
let (is_true : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____1672 = FStar_Syntax_Util.un_squash t  in
    match uu____1672 with
    | FStar_Pervasives_Native.Some t' ->
        let uu____1682 =
          let uu____1683 = FStar_Syntax_Subst.compress t'  in
          uu____1683.FStar_Syntax_Syntax.n  in
        (match uu____1682 with
         | FStar_Syntax_Syntax.Tm_fvar fv ->
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.true_lid
         | uu____1687 -> false)
    | uu____1688 -> false
  
let (is_false : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____1698 = FStar_Syntax_Util.un_squash t  in
    match uu____1698 with
    | FStar_Pervasives_Native.Some t' ->
        let uu____1708 =
          let uu____1709 = FStar_Syntax_Subst.compress t'  in
          uu____1709.FStar_Syntax_Syntax.n  in
        (match uu____1708 with
         | FStar_Syntax_Syntax.Tm_fvar fv ->
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.false_lid
         | uu____1713 -> false)
    | uu____1714 -> false
  
let (cur_goal : unit -> FStar_Tactics_Types.goal tac) =
  fun uu____1725  ->
    bind get
      (fun p  ->
         match p.FStar_Tactics_Types.goals with
         | [] -> fail "No more goals (1)"
         | hd1::tl1 -> ret hd1)
  
let (tadmit : unit -> unit tac) =
  fun uu____1742  ->
    let uu____1745 =
      let uu____1748 = cur_goal ()  in
      bind uu____1748
        (fun g  ->
           let uu____1754 =
             let uu____1755 =
               let uu____1760 =
                 let uu____1761 = goal_to_string g  in
                 FStar_Util.format1 "Tactics admitted goal <%s>\n\n"
                   uu____1761
                  in
               (FStar_Errors.Warning_TacAdmit, uu____1760)  in
             FStar_Errors.log_issue
               (g.FStar_Tactics_Types.goal_ty).FStar_Syntax_Syntax.pos
               uu____1755
              in
           solve g FStar_Syntax_Util.exp_unit)
       in
    FStar_All.pipe_left (wrap_err "tadmit") uu____1745
  
let (fresh : unit -> FStar_BigInt.t tac) =
  fun uu____1772  ->
    bind get
      (fun ps  ->
         let n1 = ps.FStar_Tactics_Types.freshness  in
         let ps1 =
           let uu___77_1782 = ps  in
           {
             FStar_Tactics_Types.main_context =
               (uu___77_1782.FStar_Tactics_Types.main_context);
             FStar_Tactics_Types.main_goal =
               (uu___77_1782.FStar_Tactics_Types.main_goal);
             FStar_Tactics_Types.all_implicits =
               (uu___77_1782.FStar_Tactics_Types.all_implicits);
             FStar_Tactics_Types.goals =
               (uu___77_1782.FStar_Tactics_Types.goals);
             FStar_Tactics_Types.smt_goals =
               (uu___77_1782.FStar_Tactics_Types.smt_goals);
             FStar_Tactics_Types.depth =
               (uu___77_1782.FStar_Tactics_Types.depth);
             FStar_Tactics_Types.__dump =
               (uu___77_1782.FStar_Tactics_Types.__dump);
             FStar_Tactics_Types.psc = (uu___77_1782.FStar_Tactics_Types.psc);
             FStar_Tactics_Types.entry_range =
               (uu___77_1782.FStar_Tactics_Types.entry_range);
             FStar_Tactics_Types.guard_policy =
               (uu___77_1782.FStar_Tactics_Types.guard_policy);
             FStar_Tactics_Types.freshness = (n1 + (Prims.parse_int "1"))
           }  in
         let uu____1783 = set ps1  in
         bind uu____1783
           (fun uu____1788  ->
              let uu____1789 = FStar_BigInt.of_int_fs n1  in ret uu____1789))
  
let (ngoals : unit -> FStar_BigInt.t tac) =
  fun uu____1796  ->
    bind get
      (fun ps  ->
         let n1 = FStar_List.length ps.FStar_Tactics_Types.goals  in
         let uu____1804 = FStar_BigInt.of_int_fs n1  in ret uu____1804)
  
let (ngoals_smt : unit -> FStar_BigInt.t tac) =
  fun uu____1817  ->
    bind get
      (fun ps  ->
         let n1 = FStar_List.length ps.FStar_Tactics_Types.smt_goals  in
         let uu____1825 = FStar_BigInt.of_int_fs n1  in ret uu____1825)
  
let (is_guard : unit -> Prims.bool tac) =
  fun uu____1838  ->
    let uu____1841 = cur_goal ()  in
    bind uu____1841 (fun g  -> ret g.FStar_Tactics_Types.is_guard)
  
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
            let uu____1873 = env.FStar_TypeChecker_Env.universe_of env phi
               in
            FStar_Syntax_Util.mk_squash uu____1873 phi  in
          let uu____1874 = new_uvar reason env typ  in
          bind uu____1874
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
             (fun uu____1923  ->
                let uu____1924 = tts e t  in
                FStar_Util.print1 "Tac> __tc(%s)\n" uu____1924)
             (fun uu____1926  ->
                try
                  let uu____1946 =
                    (ps.FStar_Tactics_Types.main_context).FStar_TypeChecker_Env.type_of
                      e t
                     in
                  ret uu____1946
                with
                | FStar_Errors.Err (uu____1973,msg) ->
                    let uu____1975 = tts e t  in
                    let uu____1976 =
                      let uu____1977 = FStar_TypeChecker_Env.all_binders e
                         in
                      FStar_All.pipe_right uu____1977
                        (FStar_Syntax_Print.binders_to_string ", ")
                       in
                    fail3 "Cannot type %s in context (%s). Error = (%s)"
                      uu____1975 uu____1976 msg
                | FStar_Errors.Error (uu____1984,msg,uu____1986) ->
                    let uu____1987 = tts e t  in
                    let uu____1988 =
                      let uu____1989 = FStar_TypeChecker_Env.all_binders e
                         in
                      FStar_All.pipe_right uu____1989
                        (FStar_Syntax_Print.binders_to_string ", ")
                       in
                    fail3 "Cannot type %s in context (%s). Error = (%s)"
                      uu____1987 uu____1988 msg))
  
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
  
let (get_guard_policy : unit -> FStar_Tactics_Types.guard_policy tac) =
  fun uu____2016  ->
    bind get (fun ps  -> ret ps.FStar_Tactics_Types.guard_policy)
  
let (set_guard_policy : FStar_Tactics_Types.guard_policy -> unit tac) =
  fun pol  ->
    bind get
      (fun ps  ->
         set
           (let uu___80_2034 = ps  in
            {
              FStar_Tactics_Types.main_context =
                (uu___80_2034.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___80_2034.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___80_2034.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___80_2034.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (uu___80_2034.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___80_2034.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___80_2034.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___80_2034.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___80_2034.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy = pol;
              FStar_Tactics_Types.freshness =
                (uu___80_2034.FStar_Tactics_Types.freshness)
            }))
  
let with_policy : 'a . FStar_Tactics_Types.guard_policy -> 'a tac -> 'a tac =
  fun pol  ->
    fun t  ->
      let uu____2058 = get_guard_policy ()  in
      bind uu____2058
        (fun old_pol  ->
           let uu____2064 = set_guard_policy pol  in
           bind uu____2064
             (fun uu____2068  ->
                bind t
                  (fun r  ->
                     let uu____2072 = set_guard_policy old_pol  in
                     bind uu____2072 (fun uu____2076  -> ret r))))
  
let (proc_guard :
  Prims.string ->
    env ->
      FStar_TypeChecker_Env.guard_t -> FStar_Options.optionstate -> unit tac)
  =
  fun reason  ->
    fun e  ->
      fun g  ->
        fun opts  ->
          let uu____2101 =
            let uu____2102 = FStar_TypeChecker_Rel.simplify_guard e g  in
            uu____2102.FStar_TypeChecker_Env.guard_f  in
          match uu____2101 with
          | FStar_TypeChecker_Common.Trivial  -> ret ()
          | FStar_TypeChecker_Common.NonTrivial f ->
              let uu____2106 = istrivial e f  in
              if uu____2106
              then ret ()
              else
                bind get
                  (fun ps  ->
                     match ps.FStar_Tactics_Types.guard_policy with
                     | FStar_Tactics_Types.Drop  -> ret ()
                     | FStar_Tactics_Types.Goal  ->
                         let uu____2114 = mk_irrelevant_goal reason e f opts
                            in
                         bind uu____2114
                           (fun goal  ->
                              let goal1 =
                                let uu___81_2121 = goal  in
                                {
                                  FStar_Tactics_Types.context =
                                    (uu___81_2121.FStar_Tactics_Types.context);
                                  FStar_Tactics_Types.witness =
                                    (uu___81_2121.FStar_Tactics_Types.witness);
                                  FStar_Tactics_Types.goal_ty =
                                    (uu___81_2121.FStar_Tactics_Types.goal_ty);
                                  FStar_Tactics_Types.opts =
                                    (uu___81_2121.FStar_Tactics_Types.opts);
                                  FStar_Tactics_Types.is_guard = true
                                }  in
                              push_goals [goal1])
                     | FStar_Tactics_Types.SMT  ->
                         let uu____2122 = mk_irrelevant_goal reason e f opts
                            in
                         bind uu____2122
                           (fun goal  ->
                              let goal1 =
                                let uu___82_2129 = goal  in
                                {
                                  FStar_Tactics_Types.context =
                                    (uu___82_2129.FStar_Tactics_Types.context);
                                  FStar_Tactics_Types.witness =
                                    (uu___82_2129.FStar_Tactics_Types.witness);
                                  FStar_Tactics_Types.goal_ty =
                                    (uu___82_2129.FStar_Tactics_Types.goal_ty);
                                  FStar_Tactics_Types.opts =
                                    (uu___82_2129.FStar_Tactics_Types.opts);
                                  FStar_Tactics_Types.is_guard = true
                                }  in
                              push_smt_goals [goal1])
                     | FStar_Tactics_Types.Force  ->
                         (try
                            let uu____2137 =
                              let uu____2138 =
                                let uu____2139 =
                                  FStar_TypeChecker_Rel.discharge_guard_no_smt
                                    e g
                                   in
                                FStar_All.pipe_left
                                  FStar_TypeChecker_Rel.is_trivial uu____2139
                                 in
                              Prims.op_Negation uu____2138  in
                            if uu____2137
                            then
                              mlog
                                (fun uu____2144  ->
                                   let uu____2145 =
                                     FStar_TypeChecker_Rel.guard_to_string e
                                       g
                                      in
                                   FStar_Util.print1 "guard = %s\n"
                                     uu____2145)
                                (fun uu____2147  ->
                                   fail1 "Forcing the guard failed %s)"
                                     reason)
                            else ret ()
                          with
                          | uu____2154 ->
                              mlog
                                (fun uu____2157  ->
                                   let uu____2158 =
                                     FStar_TypeChecker_Rel.guard_to_string e
                                       g
                                      in
                                   FStar_Util.print1 "guard = %s\n"
                                     uu____2158)
                                (fun uu____2160  ->
                                   fail1 "Forcing the guard failed (%s)"
                                     reason)))
  
let (tc : FStar_Syntax_Syntax.term -> FStar_Reflection_Data.typ tac) =
  fun t  ->
    let uu____2170 =
      let uu____2173 = cur_goal ()  in
      bind uu____2173
        (fun goal  ->
           let uu____2179 = __tc goal.FStar_Tactics_Types.context t  in
           bind uu____2179
             (fun uu____2199  ->
                match uu____2199 with
                | (t1,typ,guard) ->
                    let uu____2211 =
                      proc_guard "tc" goal.FStar_Tactics_Types.context guard
                        goal.FStar_Tactics_Types.opts
                       in
                    bind uu____2211 (fun uu____2215  -> ret typ)))
       in
    FStar_All.pipe_left (wrap_err "tc") uu____2170
  
let (add_irrelevant_goal :
  Prims.string ->
    env -> FStar_Reflection_Data.typ -> FStar_Options.optionstate -> unit tac)
  =
  fun reason  ->
    fun env  ->
      fun phi  ->
        fun opts  ->
          let uu____2244 = mk_irrelevant_goal reason env phi opts  in
          bind uu____2244 (fun goal  -> add_goals [goal])
  
let (trivial : unit -> unit tac) =
  fun uu____2255  ->
    let uu____2258 = cur_goal ()  in
    bind uu____2258
      (fun goal  ->
         let uu____2264 =
           istrivial goal.FStar_Tactics_Types.context
             goal.FStar_Tactics_Types.goal_ty
            in
         if uu____2264
         then solve goal FStar_Syntax_Util.exp_unit
         else
           (let uu____2268 =
              tts goal.FStar_Tactics_Types.context
                goal.FStar_Tactics_Types.goal_ty
               in
            fail1 "Not a trivial goal: %s" uu____2268))
  
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
          let uu____2297 =
            let uu____2298 = FStar_TypeChecker_Rel.simplify_guard e g  in
            uu____2298.FStar_TypeChecker_Env.guard_f  in
          match uu____2297 with
          | FStar_TypeChecker_Common.Trivial  ->
              ret FStar_Pervasives_Native.None
          | FStar_TypeChecker_Common.NonTrivial f ->
              let uu____2306 = istrivial e f  in
              if uu____2306
              then ret FStar_Pervasives_Native.None
              else
                (let uu____2314 = mk_irrelevant_goal reason e f opts  in
                 bind uu____2314
                   (fun goal  ->
                      ret
                        (FStar_Pervasives_Native.Some
                           (let uu___85_2324 = goal  in
                            {
                              FStar_Tactics_Types.context =
                                (uu___85_2324.FStar_Tactics_Types.context);
                              FStar_Tactics_Types.witness =
                                (uu___85_2324.FStar_Tactics_Types.witness);
                              FStar_Tactics_Types.goal_ty =
                                (uu___85_2324.FStar_Tactics_Types.goal_ty);
                              FStar_Tactics_Types.opts =
                                (uu___85_2324.FStar_Tactics_Types.opts);
                              FStar_Tactics_Types.is_guard = true
                            }))))
  
let (smt : unit -> unit tac) =
  fun uu____2331  ->
    let uu____2334 = cur_goal ()  in
    bind uu____2334
      (fun g  ->
         let uu____2340 = is_irrelevant g  in
         if uu____2340
         then bind __dismiss (fun uu____2344  -> add_smt_goals [g])
         else
           (let uu____2346 =
              tts g.FStar_Tactics_Types.context g.FStar_Tactics_Types.goal_ty
               in
            fail1 "goal is not irrelevant: cannot dispatch to smt (%s)"
              uu____2346))
  
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
             let uu____2395 =
               try
                 let uu____2429 =
                   let uu____2438 = FStar_BigInt.to_int_fs n1  in
                   FStar_List.splitAt uu____2438 p.FStar_Tactics_Types.goals
                    in
                 ret uu____2429
               with | uu____2460 -> fail "divide: not enough goals"  in
             bind uu____2395
               (fun uu____2487  ->
                  match uu____2487 with
                  | (lgs,rgs) ->
                      let lp =
                        let uu___86_2513 = p  in
                        {
                          FStar_Tactics_Types.main_context =
                            (uu___86_2513.FStar_Tactics_Types.main_context);
                          FStar_Tactics_Types.main_goal =
                            (uu___86_2513.FStar_Tactics_Types.main_goal);
                          FStar_Tactics_Types.all_implicits =
                            (uu___86_2513.FStar_Tactics_Types.all_implicits);
                          FStar_Tactics_Types.goals = lgs;
                          FStar_Tactics_Types.smt_goals = [];
                          FStar_Tactics_Types.depth =
                            (uu___86_2513.FStar_Tactics_Types.depth);
                          FStar_Tactics_Types.__dump =
                            (uu___86_2513.FStar_Tactics_Types.__dump);
                          FStar_Tactics_Types.psc =
                            (uu___86_2513.FStar_Tactics_Types.psc);
                          FStar_Tactics_Types.entry_range =
                            (uu___86_2513.FStar_Tactics_Types.entry_range);
                          FStar_Tactics_Types.guard_policy =
                            (uu___86_2513.FStar_Tactics_Types.guard_policy);
                          FStar_Tactics_Types.freshness =
                            (uu___86_2513.FStar_Tactics_Types.freshness)
                        }  in
                      let rp =
                        let uu___87_2515 = p  in
                        {
                          FStar_Tactics_Types.main_context =
                            (uu___87_2515.FStar_Tactics_Types.main_context);
                          FStar_Tactics_Types.main_goal =
                            (uu___87_2515.FStar_Tactics_Types.main_goal);
                          FStar_Tactics_Types.all_implicits =
                            (uu___87_2515.FStar_Tactics_Types.all_implicits);
                          FStar_Tactics_Types.goals = rgs;
                          FStar_Tactics_Types.smt_goals = [];
                          FStar_Tactics_Types.depth =
                            (uu___87_2515.FStar_Tactics_Types.depth);
                          FStar_Tactics_Types.__dump =
                            (uu___87_2515.FStar_Tactics_Types.__dump);
                          FStar_Tactics_Types.psc =
                            (uu___87_2515.FStar_Tactics_Types.psc);
                          FStar_Tactics_Types.entry_range =
                            (uu___87_2515.FStar_Tactics_Types.entry_range);
                          FStar_Tactics_Types.guard_policy =
                            (uu___87_2515.FStar_Tactics_Types.guard_policy);
                          FStar_Tactics_Types.freshness =
                            (uu___87_2515.FStar_Tactics_Types.freshness)
                        }  in
                      let uu____2516 = set lp  in
                      bind uu____2516
                        (fun uu____2524  ->
                           bind l
                             (fun a  ->
                                bind get
                                  (fun lp'  ->
                                     let uu____2538 = set rp  in
                                     bind uu____2538
                                       (fun uu____2546  ->
                                          bind r
                                            (fun b  ->
                                               bind get
                                                 (fun rp'  ->
                                                    let p' =
                                                      let uu___88_2562 = p
                                                         in
                                                      {
                                                        FStar_Tactics_Types.main_context
                                                          =
                                                          (uu___88_2562.FStar_Tactics_Types.main_context);
                                                        FStar_Tactics_Types.main_goal
                                                          =
                                                          (uu___88_2562.FStar_Tactics_Types.main_goal);
                                                        FStar_Tactics_Types.all_implicits
                                                          =
                                                          (uu___88_2562.FStar_Tactics_Types.all_implicits);
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
                                                          (uu___88_2562.FStar_Tactics_Types.depth);
                                                        FStar_Tactics_Types.__dump
                                                          =
                                                          (uu___88_2562.FStar_Tactics_Types.__dump);
                                                        FStar_Tactics_Types.psc
                                                          =
                                                          (uu___88_2562.FStar_Tactics_Types.psc);
                                                        FStar_Tactics_Types.entry_range
                                                          =
                                                          (uu___88_2562.FStar_Tactics_Types.entry_range);
                                                        FStar_Tactics_Types.guard_policy
                                                          =
                                                          (uu___88_2562.FStar_Tactics_Types.guard_policy);
                                                        FStar_Tactics_Types.freshness
                                                          =
                                                          (uu___88_2562.FStar_Tactics_Types.freshness)
                                                      }  in
                                                    let uu____2563 = set p'
                                                       in
                                                    bind uu____2563
                                                      (fun uu____2571  ->
                                                         ret (a, b))))))))))
  
let focus : 'a . 'a tac -> 'a tac =
  fun f  ->
    let uu____2592 = divide FStar_BigInt.one f idtac  in
    bind uu____2592
      (fun uu____2605  -> match uu____2605 with | (a,()) -> ret a)
  
let rec map : 'a . 'a tac -> 'a Prims.list tac =
  fun tau  ->
    bind get
      (fun p  ->
         match p.FStar_Tactics_Types.goals with
         | [] -> ret []
         | uu____2642::uu____2643 ->
             let uu____2646 =
               let uu____2655 = map tau  in
               divide FStar_BigInt.one tau uu____2655  in
             bind uu____2646
               (fun uu____2673  ->
                  match uu____2673 with | (h,t) -> ret (h :: t)))
  
let (seq : unit tac -> unit tac -> unit tac) =
  fun t1  ->
    fun t2  ->
      let uu____2714 =
        bind t1
          (fun uu____2719  ->
             let uu____2720 = map t2  in
             bind uu____2720 (fun uu____2728  -> ret ()))
         in
      focus uu____2714
  
let (intro : unit -> FStar_Syntax_Syntax.binder tac) =
  fun uu____2737  ->
    let uu____2740 =
      let uu____2743 = cur_goal ()  in
      bind uu____2743
        (fun goal  ->
           let uu____2752 =
             FStar_Syntax_Util.arrow_one goal.FStar_Tactics_Types.goal_ty  in
           match uu____2752 with
           | FStar_Pervasives_Native.Some (b,c) ->
               let uu____2767 =
                 let uu____2768 = FStar_Syntax_Util.is_total_comp c  in
                 Prims.op_Negation uu____2768  in
               if uu____2767
               then fail "Codomain is effectful"
               else
                 (let env' =
                    FStar_TypeChecker_Env.push_binders
                      goal.FStar_Tactics_Types.context [b]
                     in
                  let typ' = comp_to_typ c  in
                  let uu____2774 = new_uvar "intro" env' typ'  in
                  bind uu____2774
                    (fun u  ->
                       let uu____2780 =
                         let uu____2783 =
                           FStar_Syntax_Util.abs [b] u
                             FStar_Pervasives_Native.None
                            in
                         trysolve goal uu____2783  in
                       bind uu____2780
                         (fun bb  ->
                            if bb
                            then
                              let uu____2789 =
                                let uu____2792 =
                                  let uu___91_2793 = goal  in
                                  let uu____2794 = bnorm env' u  in
                                  let uu____2795 = bnorm env' typ'  in
                                  {
                                    FStar_Tactics_Types.context = env';
                                    FStar_Tactics_Types.witness = uu____2794;
                                    FStar_Tactics_Types.goal_ty = uu____2795;
                                    FStar_Tactics_Types.opts =
                                      (uu___91_2793.FStar_Tactics_Types.opts);
                                    FStar_Tactics_Types.is_guard =
                                      (uu___91_2793.FStar_Tactics_Types.is_guard)
                                  }  in
                                replace_cur uu____2792  in
                              bind uu____2789 (fun uu____2797  -> ret b)
                            else fail "unification failed")))
           | FStar_Pervasives_Native.None  ->
               let uu____2803 =
                 tts goal.FStar_Tactics_Types.context
                   goal.FStar_Tactics_Types.goal_ty
                  in
               fail1 "goal is not an arrow (%s)" uu____2803)
       in
    FStar_All.pipe_left (wrap_err "intro") uu____2740
  
let (intro_rec :
  unit ->
    (FStar_Syntax_Syntax.binder,FStar_Syntax_Syntax.binder)
      FStar_Pervasives_Native.tuple2 tac)
  =
  fun uu____2818  ->
    let uu____2825 = cur_goal ()  in
    bind uu____2825
      (fun goal  ->
         let uu____2840 =
           FStar_Util.print_string
             "WARNING (intro_rec): calling this is known to cause normalizer loops\n"
            in
         let uu____2841 =
           FStar_Util.print_string
             "WARNING (intro_rec): proceed at your own risk...\n"
            in
         let uu____2842 =
           FStar_Syntax_Util.arrow_one goal.FStar_Tactics_Types.goal_ty  in
         match uu____2842 with
         | FStar_Pervasives_Native.Some (b,c) ->
             let uu____2861 =
               let uu____2862 = FStar_Syntax_Util.is_total_comp c  in
               Prims.op_Negation uu____2862  in
             if uu____2861
             then fail "Codomain is effectful"
             else
               (let bv =
                  FStar_Syntax_Syntax.gen_bv "__recf"
                    FStar_Pervasives_Native.None
                    goal.FStar_Tactics_Types.goal_ty
                   in
                let bs =
                  let uu____2878 = FStar_Syntax_Syntax.mk_binder bv  in
                  [uu____2878; b]  in
                let env' =
                  FStar_TypeChecker_Env.push_binders
                    goal.FStar_Tactics_Types.context bs
                   in
                let uu____2880 =
                  let uu____2883 = comp_to_typ c  in
                  new_uvar "intro_rec" env' uu____2883  in
                bind uu____2880
                  (fun u  ->
                     let lb =
                       let uu____2898 =
                         FStar_Syntax_Util.abs [b] u
                           FStar_Pervasives_Native.None
                          in
                       FStar_Syntax_Util.mk_letbinding (FStar_Util.Inl bv) []
                         goal.FStar_Tactics_Types.goal_ty
                         FStar_Parser_Const.effect_Tot_lid uu____2898 []
                         FStar_Range.dummyRange
                        in
                     let body = FStar_Syntax_Syntax.bv_to_name bv  in
                     let uu____2904 =
                       FStar_Syntax_Subst.close_let_rec [lb] body  in
                     match uu____2904 with
                     | (lbs,body1) ->
                         let tm =
                           FStar_Syntax_Syntax.mk
                             (FStar_Syntax_Syntax.Tm_let ((true, lbs), body1))
                             FStar_Pervasives_Native.None
                             (goal.FStar_Tactics_Types.witness).FStar_Syntax_Syntax.pos
                            in
                         let uu____2934 = trysolve goal tm  in
                         bind uu____2934
                           (fun bb  ->
                              if bb
                              then
                                let uu____2950 =
                                  let uu____2953 =
                                    let uu___92_2954 = goal  in
                                    let uu____2955 = bnorm env' u  in
                                    let uu____2956 =
                                      let uu____2957 = comp_to_typ c  in
                                      bnorm env' uu____2957  in
                                    {
                                      FStar_Tactics_Types.context = env';
                                      FStar_Tactics_Types.witness =
                                        uu____2955;
                                      FStar_Tactics_Types.goal_ty =
                                        uu____2956;
                                      FStar_Tactics_Types.opts =
                                        (uu___92_2954.FStar_Tactics_Types.opts);
                                      FStar_Tactics_Types.is_guard =
                                        (uu___92_2954.FStar_Tactics_Types.is_guard)
                                    }  in
                                  replace_cur uu____2953  in
                                bind uu____2950
                                  (fun uu____2964  ->
                                     let uu____2965 =
                                       let uu____2970 =
                                         FStar_Syntax_Syntax.mk_binder bv  in
                                       (uu____2970, b)  in
                                     ret uu____2965)
                              else fail "intro_rec: unification failed")))
         | FStar_Pervasives_Native.None  ->
             let uu____2984 =
               tts goal.FStar_Tactics_Types.context
                 goal.FStar_Tactics_Types.goal_ty
                in
             fail1 "intro_rec: goal is not an arrow (%s)" uu____2984)
  
let (norm : FStar_Syntax_Embeddings.norm_step Prims.list -> unit tac) =
  fun s  ->
    let uu____3002 = cur_goal ()  in
    bind uu____3002
      (fun goal  ->
         mlog
           (fun uu____3009  ->
              let uu____3010 =
                FStar_Syntax_Print.term_to_string
                  goal.FStar_Tactics_Types.witness
                 in
              FStar_Util.print1 "norm: witness = %s\n" uu____3010)
           (fun uu____3015  ->
              let steps =
                let uu____3019 = FStar_TypeChecker_Normalize.tr_norm_steps s
                   in
                FStar_List.append
                  [FStar_TypeChecker_Normalize.Reify;
                  FStar_TypeChecker_Normalize.UnfoldTac] uu____3019
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
                (let uu___93_3026 = goal  in
                 {
                   FStar_Tactics_Types.context =
                     (uu___93_3026.FStar_Tactics_Types.context);
                   FStar_Tactics_Types.witness = w;
                   FStar_Tactics_Types.goal_ty = t;
                   FStar_Tactics_Types.opts =
                     (uu___93_3026.FStar_Tactics_Types.opts);
                   FStar_Tactics_Types.is_guard =
                     (uu___93_3026.FStar_Tactics_Types.is_guard)
                 })))
  
let (norm_term_env :
  env ->
    FStar_Syntax_Embeddings.norm_step Prims.list ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term tac)
  =
  fun e  ->
    fun s  ->
      fun t  ->
        let uu____3050 =
          mlog
            (fun uu____3055  ->
               let uu____3056 = FStar_Syntax_Print.term_to_string t  in
               FStar_Util.print1 "norm_term: tm = %s\n" uu____3056)
            (fun uu____3058  ->
               bind get
                 (fun ps  ->
                    let opts =
                      match ps.FStar_Tactics_Types.goals with
                      | g::uu____3064 -> g.FStar_Tactics_Types.opts
                      | uu____3067 -> FStar_Options.peek ()  in
                    mlog
                      (fun uu____3072  ->
                         let uu____3073 =
                           tts ps.FStar_Tactics_Types.main_context t  in
                         FStar_Util.print1 "norm_term_env: t = %s\n"
                           uu____3073)
                      (fun uu____3076  ->
                         let uu____3077 = __tc e t  in
                         bind uu____3077
                           (fun uu____3098  ->
                              match uu____3098 with
                              | (t1,uu____3108,uu____3109) ->
                                  let steps =
                                    let uu____3113 =
                                      FStar_TypeChecker_Normalize.tr_norm_steps
                                        s
                                       in
                                    FStar_List.append
                                      [FStar_TypeChecker_Normalize.Reify;
                                      FStar_TypeChecker_Normalize.UnfoldTac]
                                      uu____3113
                                     in
                                  let t2 =
                                    normalize steps
                                      ps.FStar_Tactics_Types.main_context t1
                                     in
                                  ret t2))))
           in
        FStar_All.pipe_left (wrap_err "norm_term") uu____3050
  
let (refine_intro : unit -> unit tac) =
  fun uu____3127  ->
    let uu____3130 =
      let uu____3133 = cur_goal ()  in
      bind uu____3133
        (fun g  ->
           let uu____3140 =
             FStar_TypeChecker_Rel.base_and_refinement
               g.FStar_Tactics_Types.context g.FStar_Tactics_Types.goal_ty
              in
           match uu____3140 with
           | (uu____3153,FStar_Pervasives_Native.None ) ->
               fail "not a refinement"
           | (t,FStar_Pervasives_Native.Some (bv,phi)) ->
               let g1 =
                 let uu___94_3178 = g  in
                 {
                   FStar_Tactics_Types.context =
                     (uu___94_3178.FStar_Tactics_Types.context);
                   FStar_Tactics_Types.witness =
                     (uu___94_3178.FStar_Tactics_Types.witness);
                   FStar_Tactics_Types.goal_ty = t;
                   FStar_Tactics_Types.opts =
                     (uu___94_3178.FStar_Tactics_Types.opts);
                   FStar_Tactics_Types.is_guard =
                     (uu___94_3178.FStar_Tactics_Types.is_guard)
                 }  in
               let uu____3179 =
                 let uu____3184 =
                   let uu____3189 =
                     let uu____3190 = FStar_Syntax_Syntax.mk_binder bv  in
                     [uu____3190]  in
                   FStar_Syntax_Subst.open_term uu____3189 phi  in
                 match uu____3184 with
                 | (bvs,phi1) ->
                     let uu____3197 =
                       let uu____3198 = FStar_List.hd bvs  in
                       FStar_Pervasives_Native.fst uu____3198  in
                     (uu____3197, phi1)
                  in
               (match uu____3179 with
                | (bv1,phi1) ->
                    let uu____3211 =
                      let uu____3214 =
                        FStar_Syntax_Subst.subst
                          [FStar_Syntax_Syntax.NT
                             (bv1, (g.FStar_Tactics_Types.witness))] phi1
                         in
                      mk_irrelevant_goal "refine_intro refinement"
                        g.FStar_Tactics_Types.context uu____3214
                        g.FStar_Tactics_Types.opts
                       in
                    bind uu____3211
                      (fun g2  ->
                         bind __dismiss
                           (fun uu____3218  -> add_goals [g1; g2]))))
       in
    FStar_All.pipe_left (wrap_err "refine_intro") uu____3130
  
let (__exact_now : Prims.bool -> FStar_Syntax_Syntax.term -> unit tac) =
  fun set_expected_typ1  ->
    fun t  ->
      let uu____3237 = cur_goal ()  in
      bind uu____3237
        (fun goal  ->
           let env =
             if set_expected_typ1
             then
               FStar_TypeChecker_Env.set_expected_typ
                 goal.FStar_Tactics_Types.context
                 goal.FStar_Tactics_Types.goal_ty
             else goal.FStar_Tactics_Types.context  in
           let uu____3246 = __tc env t  in
           bind uu____3246
             (fun uu____3265  ->
                match uu____3265 with
                | (t1,typ,guard) ->
                    mlog
                      (fun uu____3280  ->
                         let uu____3281 =
                           tts goal.FStar_Tactics_Types.context typ  in
                         let uu____3282 =
                           FStar_TypeChecker_Rel.guard_to_string
                             goal.FStar_Tactics_Types.context guard
                            in
                         FStar_Util.print2
                           "__exact_now: got type %s\n__exact_now and guard %s\n"
                           uu____3281 uu____3282)
                      (fun uu____3285  ->
                         let uu____3286 =
                           proc_guard "__exact typing"
                             goal.FStar_Tactics_Types.context guard
                             goal.FStar_Tactics_Types.opts
                            in
                         bind uu____3286
                           (fun uu____3290  ->
                              mlog
                                (fun uu____3294  ->
                                   let uu____3295 =
                                     tts goal.FStar_Tactics_Types.context typ
                                      in
                                   let uu____3296 =
                                     tts goal.FStar_Tactics_Types.context
                                       goal.FStar_Tactics_Types.goal_ty
                                      in
                                   FStar_Util.print2
                                     "__exact_now: unifying %s and %s\n"
                                     uu____3295 uu____3296)
                                (fun uu____3299  ->
                                   let uu____3300 =
                                     do_unify
                                       goal.FStar_Tactics_Types.context typ
                                       goal.FStar_Tactics_Types.goal_ty
                                      in
                                   bind uu____3300
                                     (fun b  ->
                                        if b
                                        then solve goal t1
                                        else
                                          (let uu____3308 =
                                             tts
                                               goal.FStar_Tactics_Types.context
                                               t1
                                              in
                                           let uu____3309 =
                                             tts
                                               goal.FStar_Tactics_Types.context
                                               typ
                                              in
                                           let uu____3310 =
                                             tts
                                               goal.FStar_Tactics_Types.context
                                               goal.FStar_Tactics_Types.goal_ty
                                              in
                                           let uu____3311 =
                                             tts
                                               goal.FStar_Tactics_Types.context
                                               goal.FStar_Tactics_Types.witness
                                              in
                                           fail4
                                             "%s : %s does not exactly solve the goal %s (witness = %s)"
                                             uu____3308 uu____3309 uu____3310
                                             uu____3311)))))))
  
let (t_exact : Prims.bool -> FStar_Syntax_Syntax.term -> unit tac) =
  fun set_expected_typ1  ->
    fun tm  ->
      let uu____3326 =
        mlog
          (fun uu____3331  ->
             let uu____3332 = FStar_Syntax_Print.term_to_string tm  in
             FStar_Util.print1 "t_exact: tm = %s\n" uu____3332)
          (fun uu____3335  ->
             let uu____3336 =
               let uu____3343 = __exact_now set_expected_typ1 tm  in
               trytac' uu____3343  in
             bind uu____3336
               (fun uu___60_3352  ->
                  match uu___60_3352 with
                  | FStar_Util.Inr r -> ret ()
                  | FStar_Util.Inl e ->
                      let uu____3361 =
                        let uu____3368 =
                          let uu____3371 =
                            norm [FStar_Syntax_Embeddings.Delta]  in
                          bind uu____3371
                            (fun uu____3376  ->
                               let uu____3377 = refine_intro ()  in
                               bind uu____3377
                                 (fun uu____3381  ->
                                    __exact_now set_expected_typ1 tm))
                           in
                        trytac' uu____3368  in
                      bind uu____3361
                        (fun uu___59_3388  ->
                           match uu___59_3388 with
                           | FStar_Util.Inr r -> ret ()
                           | FStar_Util.Inl uu____3396 -> fail e)))
         in
      FStar_All.pipe_left (wrap_err "exact") uu____3326
  
let (uvar_free_in_goal :
  FStar_Syntax_Syntax.uvar -> FStar_Tactics_Types.goal -> Prims.bool) =
  fun u  ->
    fun g  ->
      if g.FStar_Tactics_Types.is_guard
      then false
      else
        (let free_uvars =
           let uu____3415 =
             let uu____3422 =
               FStar_Syntax_Free.uvars g.FStar_Tactics_Types.goal_ty  in
             FStar_Util.set_elements uu____3422  in
           FStar_List.map FStar_Pervasives_Native.fst uu____3415  in
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
          let uu____3492 = f x  in
          bind uu____3492
            (fun y  ->
               let uu____3500 = mapM f xs  in
               bind uu____3500 (fun ys  -> ret (y :: ys)))
  
exception NoUnif 
let (uu___is_NoUnif : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with | NoUnif  -> true | uu____3520 -> false
  
let rec (__apply :
  Prims.bool ->
    FStar_Syntax_Syntax.term -> FStar_Reflection_Data.typ -> unit tac)
  =
  fun uopt  ->
    fun tm  ->
      fun typ  ->
        let uu____3540 = cur_goal ()  in
        bind uu____3540
          (fun goal  ->
             mlog
               (fun uu____3547  ->
                  let uu____3548 = FStar_Syntax_Print.term_to_string tm  in
                  FStar_Util.print1 ">>> Calling __exact(%s)\n" uu____3548)
               (fun uu____3551  ->
                  let uu____3552 =
                    let uu____3557 =
                      let uu____3560 = t_exact false tm  in
                      with_policy FStar_Tactics_Types.Force uu____3560  in
                    trytac_exn uu____3557  in
                  bind uu____3552
                    (fun uu___61_3567  ->
                       match uu___61_3567 with
                       | FStar_Pervasives_Native.Some r -> ret ()
                       | FStar_Pervasives_Native.None  ->
                           mlog
                             (fun uu____3575  ->
                                let uu____3576 =
                                  FStar_Syntax_Print.term_to_string typ  in
                                FStar_Util.print1 ">>> typ = %s\n" uu____3576)
                             (fun uu____3579  ->
                                let uu____3580 =
                                  FStar_Syntax_Util.arrow_one typ  in
                                match uu____3580 with
                                | FStar_Pervasives_Native.None  ->
                                    FStar_Exn.raise NoUnif
                                | FStar_Pervasives_Native.Some ((bv,aq),c) ->
                                    mlog
                                      (fun uu____3612  ->
                                         let uu____3613 =
                                           FStar_Syntax_Print.binder_to_string
                                             (bv, aq)
                                            in
                                         FStar_Util.print1
                                           "__apply: pushing binder %s\n"
                                           uu____3613)
                                      (fun uu____3616  ->
                                         let uu____3617 =
                                           let uu____3618 =
                                             FStar_Syntax_Util.is_total_comp
                                               c
                                              in
                                           Prims.op_Negation uu____3618  in
                                         if uu____3617
                                         then
                                           fail "apply: not total codomain"
                                         else
                                           (let uu____3622 =
                                              new_uvar "apply"
                                                goal.FStar_Tactics_Types.context
                                                bv.FStar_Syntax_Syntax.sort
                                               in
                                            bind uu____3622
                                              (fun u  ->
                                                 let tm' =
                                                   FStar_Syntax_Syntax.mk_Tm_app
                                                     tm [(u, aq)]
                                                     FStar_Pervasives_Native.None
                                                     tm.FStar_Syntax_Syntax.pos
                                                    in
                                                 let typ' =
                                                   let uu____3642 =
                                                     comp_to_typ c  in
                                                   FStar_All.pipe_left
                                                     (FStar_Syntax_Subst.subst
                                                        [FStar_Syntax_Syntax.NT
                                                           (bv, u)])
                                                     uu____3642
                                                    in
                                                 let uu____3643 =
                                                   __apply uopt tm' typ'  in
                                                 bind uu____3643
                                                   (fun uu____3651  ->
                                                      let u1 =
                                                        bnorm
                                                          goal.FStar_Tactics_Types.context
                                                          u
                                                         in
                                                      let uu____3653 =
                                                        let uu____3654 =
                                                          let uu____3657 =
                                                            let uu____3658 =
                                                              FStar_Syntax_Util.head_and_args
                                                                u1
                                                               in
                                                            FStar_Pervasives_Native.fst
                                                              uu____3658
                                                             in
                                                          FStar_Syntax_Subst.compress
                                                            uu____3657
                                                           in
                                                        uu____3654.FStar_Syntax_Syntax.n
                                                         in
                                                      match uu____3653 with
                                                      | FStar_Syntax_Syntax.Tm_uvar
                                                          (uvar,uu____3686)
                                                          ->
                                                          bind get
                                                            (fun ps  ->
                                                               let uu____3714
                                                                 =
                                                                 uopt &&
                                                                   (uvar_free
                                                                    uvar ps)
                                                                  in
                                                               if uu____3714
                                                               then ret ()
                                                               else
                                                                 (let uu____3718
                                                                    =
                                                                    let uu____3721
                                                                    =
                                                                    let uu___95_3722
                                                                    = goal
                                                                     in
                                                                    let uu____3723
                                                                    =
                                                                    bnorm
                                                                    goal.FStar_Tactics_Types.context
                                                                    u1  in
                                                                    let uu____3724
                                                                    =
                                                                    bnorm
                                                                    goal.FStar_Tactics_Types.context
                                                                    bv.FStar_Syntax_Syntax.sort
                                                                     in
                                                                    {
                                                                    FStar_Tactics_Types.context
                                                                    =
                                                                    (uu___95_3722.FStar_Tactics_Types.context);
                                                                    FStar_Tactics_Types.witness
                                                                    =
                                                                    uu____3723;
                                                                    FStar_Tactics_Types.goal_ty
                                                                    =
                                                                    uu____3724;
                                                                    FStar_Tactics_Types.opts
                                                                    =
                                                                    (uu___95_3722.FStar_Tactics_Types.opts);
                                                                    FStar_Tactics_Types.is_guard
                                                                    = false
                                                                    }  in
                                                                    [uu____3721]
                                                                     in
                                                                  add_goals
                                                                    uu____3718))
                                                      | t -> ret ()))))))))
  
let try_unif : 'a . 'a tac -> 'a tac -> 'a tac =
  fun t  ->
    fun t'  -> mk_tac (fun ps  -> try run t ps with | NoUnif  -> run t' ps)
  
let (apply : Prims.bool -> FStar_Syntax_Syntax.term -> unit tac) =
  fun uopt  ->
    fun tm  ->
      let uu____3779 =
        mlog
          (fun uu____3784  ->
             let uu____3785 = FStar_Syntax_Print.term_to_string tm  in
             FStar_Util.print1 "apply: tm = %s\n" uu____3785)
          (fun uu____3788  ->
             let uu____3789 = cur_goal ()  in
             bind uu____3789
               (fun goal  ->
                  let uu____3795 = __tc goal.FStar_Tactics_Types.context tm
                     in
                  bind uu____3795
                    (fun uu____3817  ->
                       match uu____3817 with
                       | (tm1,typ,guard) ->
                           let typ1 =
                             bnorm goal.FStar_Tactics_Types.context typ  in
                           let uu____3830 =
                             let uu____3833 =
                               let uu____3836 = __apply uopt tm1 typ1  in
                               bind uu____3836
                                 (fun uu____3840  ->
                                    proc_guard "apply guard"
                                      goal.FStar_Tactics_Types.context guard
                                      goal.FStar_Tactics_Types.opts)
                                in
                             focus uu____3833  in
                           let uu____3841 =
                             let uu____3844 =
                               tts goal.FStar_Tactics_Types.context tm1  in
                             let uu____3845 =
                               tts goal.FStar_Tactics_Types.context typ1  in
                             let uu____3846 =
                               tts goal.FStar_Tactics_Types.context
                                 goal.FStar_Tactics_Types.goal_ty
                                in
                             fail3
                               "Cannot instantiate %s (of type %s) to match goal (%s)"
                               uu____3844 uu____3845 uu____3846
                              in
                           try_unif uu____3830 uu____3841)))
         in
      FStar_All.pipe_left (wrap_err "apply") uu____3779
  
let (lemma_or_sq :
  FStar_Syntax_Syntax.comp ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun c  ->
    let ct = FStar_Syntax_Util.comp_to_comp_typ_nouniv c  in
    let uu____3869 =
      FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
        FStar_Parser_Const.effect_Lemma_lid
       in
    if uu____3869
    then
      let uu____3876 =
        match ct.FStar_Syntax_Syntax.effect_args with
        | pre::post::uu____3895 ->
            ((FStar_Pervasives_Native.fst pre),
              (FStar_Pervasives_Native.fst post))
        | uu____3936 -> failwith "apply_lemma: impossible: not a lemma"  in
      match uu____3876 with
      | (pre,post) ->
          let post1 =
            let uu____3972 =
              let uu____3981 =
                FStar_Syntax_Syntax.as_arg FStar_Syntax_Util.exp_unit  in
              [uu____3981]  in
            FStar_Syntax_Util.mk_app post uu____3972  in
          FStar_Pervasives_Native.Some (pre, post1)
    else
      (let uu____3995 =
         FStar_Syntax_Util.is_pure_effect ct.FStar_Syntax_Syntax.effect_name
          in
       if uu____3995
       then
         let uu____4002 =
           FStar_Syntax_Util.un_squash ct.FStar_Syntax_Syntax.result_typ  in
         FStar_Util.map_opt uu____4002
           (fun post  -> (FStar_Syntax_Util.t_true, post))
       else FStar_Pervasives_Native.None)
  
let (apply_lemma : FStar_Syntax_Syntax.term -> unit tac) =
  fun tm  ->
    let uu____4035 =
      let uu____4038 =
        mlog
          (fun uu____4043  ->
             let uu____4044 = FStar_Syntax_Print.term_to_string tm  in
             FStar_Util.print1 "apply_lemma: tm = %s\n" uu____4044)
          (fun uu____4048  ->
             let is_unit_t t =
               let uu____4055 =
                 let uu____4056 = FStar_Syntax_Subst.compress t  in
                 uu____4056.FStar_Syntax_Syntax.n  in
               match uu____4055 with
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.unit_lid
                   -> true
               | uu____4060 -> false  in
             let uu____4061 = cur_goal ()  in
             bind uu____4061
               (fun goal  ->
                  let uu____4067 = __tc goal.FStar_Tactics_Types.context tm
                     in
                  bind uu____4067
                    (fun uu____4090  ->
                       match uu____4090 with
                       | (tm1,t,guard) ->
                           let uu____4102 =
                             FStar_Syntax_Util.arrow_formals_comp t  in
                           (match uu____4102 with
                            | (bs,comp) ->
                                let uu____4129 = lemma_or_sq comp  in
                                (match uu____4129 with
                                 | FStar_Pervasives_Native.None  ->
                                     fail "not a lemma or squashed function"
                                 | FStar_Pervasives_Native.Some (pre,post) ->
                                     let uu____4148 =
                                       FStar_List.fold_left
                                         (fun uu____4194  ->
                                            fun uu____4195  ->
                                              match (uu____4194, uu____4195)
                                              with
                                              | ((uvs,guard1,subst1),(b,aq))
                                                  ->
                                                  let b_t =
                                                    FStar_Syntax_Subst.subst
                                                      subst1
                                                      b.FStar_Syntax_Syntax.sort
                                                     in
                                                  let uu____4298 =
                                                    is_unit_t b_t  in
                                                  if uu____4298
                                                  then
                                                    (((FStar_Syntax_Util.exp_unit,
                                                        aq) :: uvs), guard1,
                                                      ((FStar_Syntax_Syntax.NT
                                                          (b,
                                                            FStar_Syntax_Util.exp_unit))
                                                      :: subst1))
                                                  else
                                                    (let uu____4336 =
                                                       FStar_TypeChecker_Util.new_implicit_var
                                                         "apply_lemma"
                                                         (goal.FStar_Tactics_Types.goal_ty).FStar_Syntax_Syntax.pos
                                                         goal.FStar_Tactics_Types.context
                                                         b_t
                                                        in
                                                     match uu____4336 with
                                                     | (u,uu____4366,g_u) ->
                                                         let uu____4380 =
                                                           FStar_TypeChecker_Rel.conj_guard
                                                             guard1 g_u
                                                            in
                                                         (((u, aq) :: uvs),
                                                           uu____4380,
                                                           ((FStar_Syntax_Syntax.NT
                                                               (b, u)) ::
                                                           subst1))))
                                         ([], guard, []) bs
                                        in
                                     (match uu____4148 with
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
                                          let uu____4451 =
                                            let uu____4454 =
                                              FStar_Syntax_Util.mk_squash
                                                FStar_Syntax_Syntax.U_zero
                                                post1
                                               in
                                            do_unify
                                              goal.FStar_Tactics_Types.context
                                              uu____4454
                                              goal.FStar_Tactics_Types.goal_ty
                                             in
                                          bind uu____4451
                                            (fun b  ->
                                               if Prims.op_Negation b
                                               then
                                                 let uu____4462 =
                                                   tts
                                                     goal.FStar_Tactics_Types.context
                                                     tm1
                                                    in
                                                 let uu____4463 =
                                                   let uu____4464 =
                                                     FStar_Syntax_Util.mk_squash
                                                       FStar_Syntax_Syntax.U_zero
                                                       post1
                                                      in
                                                   tts
                                                     goal.FStar_Tactics_Types.context
                                                     uu____4464
                                                    in
                                                 let uu____4465 =
                                                   tts
                                                     goal.FStar_Tactics_Types.context
                                                     goal.FStar_Tactics_Types.goal_ty
                                                    in
                                                 fail3
                                                   "Cannot instantiate lemma %s (with postcondition: %s) to match goal (%s)"
                                                   uu____4462 uu____4463
                                                   uu____4465
                                               else
                                                 (let uu____4467 =
                                                    add_implicits
                                                      implicits.FStar_TypeChecker_Env.implicits
                                                     in
                                                  bind uu____4467
                                                    (fun uu____4472  ->
                                                       let uu____4473 =
                                                         solve goal
                                                           FStar_Syntax_Util.exp_unit
                                                          in
                                                       bind uu____4473
                                                         (fun uu____4481  ->
                                                            let is_free_uvar
                                                              uv t1 =
                                                              let free_uvars
                                                                =
                                                                let uu____4496
                                                                  =
                                                                  let uu____4503
                                                                    =
                                                                    FStar_Syntax_Free.uvars
                                                                    t1  in
                                                                  FStar_Util.set_elements
                                                                    uu____4503
                                                                   in
                                                                FStar_List.map
                                                                  FStar_Pervasives_Native.fst
                                                                  uu____4496
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
                                                              let uu____4552
                                                                =
                                                                FStar_Syntax_Util.head_and_args
                                                                  t1
                                                                 in
                                                              match uu____4552
                                                              with
                                                              | (hd1,uu____4568)
                                                                  ->
                                                                  (match 
                                                                    hd1.FStar_Syntax_Syntax.n
                                                                   with
                                                                   | 
                                                                   FStar_Syntax_Syntax.Tm_uvar
                                                                    (uv,uu____4590)
                                                                    ->
                                                                    appears
                                                                    uv goals
                                                                   | 
                                                                   uu____4615
                                                                    -> false)
                                                               in
                                                            let uu____4616 =
                                                              FStar_All.pipe_right
                                                                implicits.FStar_TypeChecker_Env.implicits
                                                                (mapM
                                                                   (fun
                                                                    uu____4688
                                                                     ->
                                                                    match uu____4688
                                                                    with
                                                                    | 
                                                                    (_msg,env,_uvar,term,typ,uu____4716)
                                                                    ->
                                                                    let uu____4717
                                                                    =
                                                                    FStar_Syntax_Util.head_and_args
                                                                    term  in
                                                                    (match uu____4717
                                                                    with
                                                                    | 
                                                                    (hd1,uu____4743)
                                                                    ->
                                                                    let uu____4764
                                                                    =
                                                                    let uu____4765
                                                                    =
                                                                    FStar_Syntax_Subst.compress
                                                                    hd1  in
                                                                    uu____4765.FStar_Syntax_Syntax.n
                                                                     in
                                                                    (match uu____4764
                                                                    with
                                                                    | 
                                                                    FStar_Syntax_Syntax.Tm_uvar
                                                                    uu____4778
                                                                    ->
                                                                    let uu____4795
                                                                    =
                                                                    let uu____4804
                                                                    =
                                                                    let uu____4807
                                                                    =
                                                                    let uu___98_4808
                                                                    = goal
                                                                     in
                                                                    let uu____4809
                                                                    =
                                                                    bnorm
                                                                    goal.FStar_Tactics_Types.context
                                                                    term  in
                                                                    let uu____4810
                                                                    =
                                                                    bnorm
                                                                    goal.FStar_Tactics_Types.context
                                                                    typ  in
                                                                    {
                                                                    FStar_Tactics_Types.context
                                                                    =
                                                                    (uu___98_4808.FStar_Tactics_Types.context);
                                                                    FStar_Tactics_Types.witness
                                                                    =
                                                                    uu____4809;
                                                                    FStar_Tactics_Types.goal_ty
                                                                    =
                                                                    uu____4810;
                                                                    FStar_Tactics_Types.opts
                                                                    =
                                                                    (uu___98_4808.FStar_Tactics_Types.opts);
                                                                    FStar_Tactics_Types.is_guard
                                                                    =
                                                                    (uu___98_4808.FStar_Tactics_Types.is_guard)
                                                                    }  in
                                                                    [uu____4807]
                                                                     in
                                                                    (uu____4804,
                                                                    [])  in
                                                                    ret
                                                                    uu____4795
                                                                    | 
                                                                    uu____4823
                                                                    ->
                                                                    let g_typ
                                                                    =
                                                                    let uu____4825
                                                                    =
                                                                    FStar_Options.__temp_fast_implicits
                                                                    ()  in
                                                                    if
                                                                    uu____4825
                                                                    then
                                                                    FStar_TypeChecker_TcTerm.check_type_of_well_typed_term
                                                                    false env
                                                                    term typ
                                                                    else
                                                                    (let term1
                                                                    =
                                                                    bnorm env
                                                                    term  in
                                                                    let uu____4828
                                                                    =
                                                                    let uu____4835
                                                                    =
                                                                    FStar_TypeChecker_Env.set_expected_typ
                                                                    env typ
                                                                     in
                                                                    env.FStar_TypeChecker_Env.type_of
                                                                    uu____4835
                                                                    term1  in
                                                                    match uu____4828
                                                                    with
                                                                    | 
                                                                    (uu____4836,uu____4837,g_typ)
                                                                    -> g_typ)
                                                                     in
                                                                    let uu____4839
                                                                    =
                                                                    goal_from_guard
                                                                    "apply_lemma solved arg"
                                                                    goal.FStar_Tactics_Types.context
                                                                    g_typ
                                                                    goal.FStar_Tactics_Types.opts
                                                                     in
                                                                    bind
                                                                    uu____4839
                                                                    (fun
                                                                    uu___62_4855
                                                                     ->
                                                                    match uu___62_4855
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
                                                            bind uu____4616
                                                              (fun goals_  ->
                                                                 let sub_goals
                                                                   =
                                                                   let uu____4923
                                                                    =
                                                                    FStar_List.map
                                                                    FStar_Pervasives_Native.fst
                                                                    goals_
                                                                     in
                                                                   FStar_List.flatten
                                                                    uu____4923
                                                                    in
                                                                 let smt_goals
                                                                   =
                                                                   let uu____4945
                                                                    =
                                                                    FStar_List.map
                                                                    FStar_Pervasives_Native.snd
                                                                    goals_
                                                                     in
                                                                   FStar_List.flatten
                                                                    uu____4945
                                                                    in
                                                                 let rec filter'
                                                                   f xs =
                                                                   match xs
                                                                   with
                                                                   | 
                                                                   [] -> []
                                                                   | 
                                                                   x::xs1 ->
                                                                    let uu____5006
                                                                    = f x xs1
                                                                     in
                                                                    if
                                                                    uu____5006
                                                                    then
                                                                    let uu____5009
                                                                    =
                                                                    filter' f
                                                                    xs1  in x
                                                                    ::
                                                                    uu____5009
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
                                                                    let uu____5023
                                                                    =
                                                                    checkone
                                                                    g.FStar_Tactics_Types.witness
                                                                    goals  in
                                                                    Prims.op_Negation
                                                                    uu____5023)
                                                                    sub_goals
                                                                    in
                                                                 let uu____5024
                                                                   =
                                                                   proc_guard
                                                                    "apply_lemma guard"
                                                                    goal.FStar_Tactics_Types.context
                                                                    guard
                                                                    goal.FStar_Tactics_Types.opts
                                                                    in
                                                                 bind
                                                                   uu____5024
                                                                   (fun
                                                                    uu____5029
                                                                     ->
                                                                    let uu____5030
                                                                    =
                                                                    let uu____5033
                                                                    =
                                                                    let uu____5034
                                                                    =
                                                                    let uu____5035
                                                                    =
                                                                    FStar_Syntax_Util.mk_squash
                                                                    FStar_Syntax_Syntax.U_zero
                                                                    pre1  in
                                                                    istrivial
                                                                    goal.FStar_Tactics_Types.context
                                                                    uu____5035
                                                                     in
                                                                    Prims.op_Negation
                                                                    uu____5034
                                                                     in
                                                                    if
                                                                    uu____5033
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
                                                                    uu____5030
                                                                    (fun
                                                                    uu____5041
                                                                     ->
                                                                    let uu____5042
                                                                    =
                                                                    add_smt_goals
                                                                    smt_goals
                                                                     in
                                                                    bind
                                                                    uu____5042
                                                                    (fun
                                                                    uu____5046
                                                                     ->
                                                                    add_goals
                                                                    sub_goals1))))))))))))))
         in
      focus uu____4038  in
    FStar_All.pipe_left (wrap_err "apply_lemma") uu____4035
  
let (destruct_eq' :
  FStar_Reflection_Data.typ ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun typ  ->
    let uu____5068 = FStar_Syntax_Util.destruct_typ_as_formula typ  in
    match uu____5068 with
    | FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn
        (l,uu____5078::(e1,uu____5080)::(e2,uu____5082)::[])) when
        FStar_Ident.lid_equals l FStar_Parser_Const.eq2_lid ->
        FStar_Pervasives_Native.Some (e1, e2)
    | uu____5141 -> FStar_Pervasives_Native.None
  
let (destruct_eq :
  FStar_Reflection_Data.typ ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun typ  ->
    let uu____5165 = destruct_eq' typ  in
    match uu____5165 with
    | FStar_Pervasives_Native.Some t -> FStar_Pervasives_Native.Some t
    | FStar_Pervasives_Native.None  ->
        let uu____5195 = FStar_Syntax_Util.un_squash typ  in
        (match uu____5195 with
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
        let uu____5257 = FStar_TypeChecker_Env.pop_bv e1  in
        match uu____5257 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (bv',e') ->
            if FStar_Syntax_Syntax.bv_eq bvar bv'
            then FStar_Pervasives_Native.Some (e', [])
            else
              (let uu____5305 = aux e'  in
               FStar_Util.map_opt uu____5305
                 (fun uu____5329  ->
                    match uu____5329 with | (e'',bvs) -> (e'', (bv' :: bvs))))
         in
      let uu____5350 = aux e  in
      FStar_Util.map_opt uu____5350
        (fun uu____5374  ->
           match uu____5374 with | (e',bvs) -> (e', (FStar_List.rev bvs)))
  
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
          let uu____5441 = split_env b1 g.FStar_Tactics_Types.context  in
          FStar_Util.map_opt uu____5441
            (fun uu____5465  ->
               match uu____5465 with
               | (e0,bvs) ->
                   let s1 bv =
                     let uu___99_5484 = bv  in
                     let uu____5485 =
                       FStar_Syntax_Subst.subst s bv.FStar_Syntax_Syntax.sort
                        in
                     {
                       FStar_Syntax_Syntax.ppname =
                         (uu___99_5484.FStar_Syntax_Syntax.ppname);
                       FStar_Syntax_Syntax.index =
                         (uu___99_5484.FStar_Syntax_Syntax.index);
                       FStar_Syntax_Syntax.sort = uu____5485
                     }  in
                   let bvs1 = FStar_List.map s1 bvs  in
                   let c = push_bvs e0 (b2 :: bvs1)  in
                   let w =
                     FStar_Syntax_Subst.subst s g.FStar_Tactics_Types.witness
                      in
                   let t =
                     FStar_Syntax_Subst.subst s g.FStar_Tactics_Types.goal_ty
                      in
                   let uu___100_5494 = g  in
                   {
                     FStar_Tactics_Types.context = c;
                     FStar_Tactics_Types.witness = w;
                     FStar_Tactics_Types.goal_ty = t;
                     FStar_Tactics_Types.opts =
                       (uu___100_5494.FStar_Tactics_Types.opts);
                     FStar_Tactics_Types.is_guard =
                       (uu___100_5494.FStar_Tactics_Types.is_guard)
                   })
  
let (rewrite : FStar_Syntax_Syntax.binder -> unit tac) =
  fun h  ->
    let uu____5504 = cur_goal ()  in
    bind uu____5504
      (fun goal  ->
         let uu____5512 = h  in
         match uu____5512 with
         | (bv,uu____5516) ->
             mlog
               (fun uu____5520  ->
                  let uu____5521 = FStar_Syntax_Print.bv_to_string bv  in
                  let uu____5522 =
                    tts goal.FStar_Tactics_Types.context
                      bv.FStar_Syntax_Syntax.sort
                     in
                  FStar_Util.print2 "+++Rewrite %s : %s\n" uu____5521
                    uu____5522)
               (fun uu____5525  ->
                  let uu____5526 =
                    split_env bv goal.FStar_Tactics_Types.context  in
                  match uu____5526 with
                  | FStar_Pervasives_Native.None  ->
                      fail "rewrite: binder not found in environment"
                  | FStar_Pervasives_Native.Some (e0,bvs) ->
                      let uu____5555 =
                        destruct_eq bv.FStar_Syntax_Syntax.sort  in
                      (match uu____5555 with
                       | FStar_Pervasives_Native.Some (x,e) ->
                           let uu____5570 =
                             let uu____5571 = FStar_Syntax_Subst.compress x
                                in
                             uu____5571.FStar_Syntax_Syntax.n  in
                           (match uu____5570 with
                            | FStar_Syntax_Syntax.Tm_name x1 ->
                                let s = [FStar_Syntax_Syntax.NT (x1, e)]  in
                                let s1 bv1 =
                                  let uu___101_5586 = bv1  in
                                  let uu____5587 =
                                    FStar_Syntax_Subst.subst s
                                      bv1.FStar_Syntax_Syntax.sort
                                     in
                                  {
                                    FStar_Syntax_Syntax.ppname =
                                      (uu___101_5586.FStar_Syntax_Syntax.ppname);
                                    FStar_Syntax_Syntax.index =
                                      (uu___101_5586.FStar_Syntax_Syntax.index);
                                    FStar_Syntax_Syntax.sort = uu____5587
                                  }  in
                                let bvs1 = FStar_List.map s1 bvs  in
                                let uu____5593 =
                                  let uu___102_5594 = goal  in
                                  let uu____5595 = push_bvs e0 (bv :: bvs1)
                                     in
                                  let uu____5596 =
                                    FStar_Syntax_Subst.subst s
                                      goal.FStar_Tactics_Types.witness
                                     in
                                  let uu____5597 =
                                    FStar_Syntax_Subst.subst s
                                      goal.FStar_Tactics_Types.goal_ty
                                     in
                                  {
                                    FStar_Tactics_Types.context = uu____5595;
                                    FStar_Tactics_Types.witness = uu____5596;
                                    FStar_Tactics_Types.goal_ty = uu____5597;
                                    FStar_Tactics_Types.opts =
                                      (uu___102_5594.FStar_Tactics_Types.opts);
                                    FStar_Tactics_Types.is_guard =
                                      (uu___102_5594.FStar_Tactics_Types.is_guard)
                                  }  in
                                replace_cur uu____5593
                            | uu____5598 ->
                                fail
                                  "rewrite: Not an equality hypothesis with a variable on the LHS")
                       | uu____5599 ->
                           fail "rewrite: Not an equality hypothesis")))
  
let (rename_to : FStar_Syntax_Syntax.binder -> Prims.string -> unit tac) =
  fun b  ->
    fun s  ->
      let uu____5620 = cur_goal ()  in
      bind uu____5620
        (fun goal  ->
           let uu____5631 = b  in
           match uu____5631 with
           | (bv,uu____5635) ->
               let bv' =
                 let uu____5637 =
                   let uu___103_5638 = bv  in
                   let uu____5639 =
                     FStar_Ident.mk_ident
                       (s,
                         ((bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange))
                      in
                   {
                     FStar_Syntax_Syntax.ppname = uu____5639;
                     FStar_Syntax_Syntax.index =
                       (uu___103_5638.FStar_Syntax_Syntax.index);
                     FStar_Syntax_Syntax.sort =
                       (uu___103_5638.FStar_Syntax_Syntax.sort)
                   }  in
                 FStar_Syntax_Syntax.freshen_bv uu____5637  in
               let s1 =
                 let uu____5643 =
                   let uu____5644 =
                     let uu____5651 = FStar_Syntax_Syntax.bv_to_name bv'  in
                     (bv, uu____5651)  in
                   FStar_Syntax_Syntax.NT uu____5644  in
                 [uu____5643]  in
               let uu____5652 = subst_goal bv bv' s1 goal  in
               (match uu____5652 with
                | FStar_Pervasives_Native.None  ->
                    fail "rename_to: binder not found in environment"
                | FStar_Pervasives_Native.Some goal1 -> replace_cur goal1))
  
let (binder_retype : FStar_Syntax_Syntax.binder -> unit tac) =
  fun b  ->
    let uu____5667 = cur_goal ()  in
    bind uu____5667
      (fun goal  ->
         let uu____5676 = b  in
         match uu____5676 with
         | (bv,uu____5680) ->
             let uu____5681 = split_env bv goal.FStar_Tactics_Types.context
                in
             (match uu____5681 with
              | FStar_Pervasives_Native.None  ->
                  fail "binder_retype: binder is not present in environment"
              | FStar_Pervasives_Native.Some (e0,bvs) ->
                  let uu____5710 = FStar_Syntax_Util.type_u ()  in
                  (match uu____5710 with
                   | (ty,u) ->
                       let uu____5719 = new_uvar "binder_retype" e0 ty  in
                       bind uu____5719
                         (fun t'  ->
                            let bv'' =
                              let uu___104_5729 = bv  in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___104_5729.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___104_5729.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = t'
                              }  in
                            let s =
                              let uu____5733 =
                                let uu____5734 =
                                  let uu____5741 =
                                    FStar_Syntax_Syntax.bv_to_name bv''  in
                                  (bv, uu____5741)  in
                                FStar_Syntax_Syntax.NT uu____5734  in
                              [uu____5733]  in
                            let bvs1 =
                              FStar_List.map
                                (fun b1  ->
                                   let uu___105_5749 = b1  in
                                   let uu____5750 =
                                     FStar_Syntax_Subst.subst s
                                       b1.FStar_Syntax_Syntax.sort
                                      in
                                   {
                                     FStar_Syntax_Syntax.ppname =
                                       (uu___105_5749.FStar_Syntax_Syntax.ppname);
                                     FStar_Syntax_Syntax.index =
                                       (uu___105_5749.FStar_Syntax_Syntax.index);
                                     FStar_Syntax_Syntax.sort = uu____5750
                                   }) bvs
                               in
                            let env' = push_bvs e0 (bv'' :: bvs1)  in
                            bind __dismiss
                              (fun uu____5756  ->
                                 let uu____5757 =
                                   let uu____5760 =
                                     let uu____5763 =
                                       let uu___106_5764 = goal  in
                                       let uu____5765 =
                                         FStar_Syntax_Subst.subst s
                                           goal.FStar_Tactics_Types.witness
                                          in
                                       let uu____5766 =
                                         FStar_Syntax_Subst.subst s
                                           goal.FStar_Tactics_Types.goal_ty
                                          in
                                       {
                                         FStar_Tactics_Types.context = env';
                                         FStar_Tactics_Types.witness =
                                           uu____5765;
                                         FStar_Tactics_Types.goal_ty =
                                           uu____5766;
                                         FStar_Tactics_Types.opts =
                                           (uu___106_5764.FStar_Tactics_Types.opts);
                                         FStar_Tactics_Types.is_guard =
                                           (uu___106_5764.FStar_Tactics_Types.is_guard)
                                       }  in
                                     [uu____5763]  in
                                   add_goals uu____5760  in
                                 bind uu____5757
                                   (fun uu____5769  ->
                                      let uu____5770 =
                                        FStar_Syntax_Util.mk_eq2
                                          (FStar_Syntax_Syntax.U_succ u) ty
                                          bv.FStar_Syntax_Syntax.sort t'
                                         in
                                      add_irrelevant_goal
                                        "binder_retype equation" e0
                                        uu____5770
                                        goal.FStar_Tactics_Types.opts))))))
  
let (norm_binder_type :
  FStar_Syntax_Embeddings.norm_step Prims.list ->
    FStar_Syntax_Syntax.binder -> unit tac)
  =
  fun s  ->
    fun b  ->
      let uu____5789 = cur_goal ()  in
      bind uu____5789
        (fun goal  ->
           let uu____5798 = b  in
           match uu____5798 with
           | (bv,uu____5802) ->
               let uu____5803 = split_env bv goal.FStar_Tactics_Types.context
                  in
               (match uu____5803 with
                | FStar_Pervasives_Native.None  ->
                    fail
                      "binder_retype: binder is not present in environment"
                | FStar_Pervasives_Native.Some (e0,bvs) ->
                    let steps =
                      let uu____5835 =
                        FStar_TypeChecker_Normalize.tr_norm_steps s  in
                      FStar_List.append
                        [FStar_TypeChecker_Normalize.Reify;
                        FStar_TypeChecker_Normalize.UnfoldTac] uu____5835
                       in
                    let sort' =
                      normalize steps e0 bv.FStar_Syntax_Syntax.sort  in
                    let bv' =
                      let uu___107_5840 = bv  in
                      {
                        FStar_Syntax_Syntax.ppname =
                          (uu___107_5840.FStar_Syntax_Syntax.ppname);
                        FStar_Syntax_Syntax.index =
                          (uu___107_5840.FStar_Syntax_Syntax.index);
                        FStar_Syntax_Syntax.sort = sort'
                      }  in
                    let env' = push_bvs e0 (bv' :: bvs)  in
                    replace_cur
                      (let uu___108_5844 = goal  in
                       {
                         FStar_Tactics_Types.context = env';
                         FStar_Tactics_Types.witness =
                           (uu___108_5844.FStar_Tactics_Types.witness);
                         FStar_Tactics_Types.goal_ty =
                           (uu___108_5844.FStar_Tactics_Types.goal_ty);
                         FStar_Tactics_Types.opts =
                           (uu___108_5844.FStar_Tactics_Types.opts);
                         FStar_Tactics_Types.is_guard =
                           (uu___108_5844.FStar_Tactics_Types.is_guard)
                       })))
  
let (revert : unit -> unit tac) =
  fun uu____5851  ->
    let uu____5854 = cur_goal ()  in
    bind uu____5854
      (fun goal  ->
         let uu____5860 =
           FStar_TypeChecker_Env.pop_bv goal.FStar_Tactics_Types.context  in
         match uu____5860 with
         | FStar_Pervasives_Native.None  ->
             fail "Cannot revert; empty context"
         | FStar_Pervasives_Native.Some (x,env') ->
             let typ' =
               let uu____5882 =
                 FStar_Syntax_Syntax.mk_Total
                   goal.FStar_Tactics_Types.goal_ty
                  in
               FStar_Syntax_Util.arrow [(x, FStar_Pervasives_Native.None)]
                 uu____5882
                in
             let w' =
               FStar_Syntax_Util.abs [(x, FStar_Pervasives_Native.None)]
                 goal.FStar_Tactics_Types.witness
                 FStar_Pervasives_Native.None
                in
             replace_cur
               (let uu___109_5916 = goal  in
                {
                  FStar_Tactics_Types.context = env';
                  FStar_Tactics_Types.witness = w';
                  FStar_Tactics_Types.goal_ty = typ';
                  FStar_Tactics_Types.opts =
                    (uu___109_5916.FStar_Tactics_Types.opts);
                  FStar_Tactics_Types.is_guard =
                    (uu___109_5916.FStar_Tactics_Types.is_guard)
                }))
  
let (free_in :
  FStar_Syntax_Syntax.bv -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun bv  ->
    fun t  ->
      let uu____5927 = FStar_Syntax_Free.names t  in
      FStar_Util.set_mem bv uu____5927
  
let rec (clear : FStar_Syntax_Syntax.binder -> unit tac) =
  fun b  ->
    let bv = FStar_Pervasives_Native.fst b  in
    let uu____5940 = cur_goal ()  in
    bind uu____5940
      (fun goal  ->
         mlog
           (fun uu____5948  ->
              let uu____5949 = FStar_Syntax_Print.binder_to_string b  in
              let uu____5950 =
                let uu____5951 =
                  let uu____5952 =
                    FStar_TypeChecker_Env.all_binders
                      goal.FStar_Tactics_Types.context
                     in
                  FStar_All.pipe_right uu____5952 FStar_List.length  in
                FStar_All.pipe_right uu____5951 FStar_Util.string_of_int  in
              FStar_Util.print2 "Clear of (%s), env has %s binders\n"
                uu____5949 uu____5950)
           (fun uu____5963  ->
              let uu____5964 = split_env bv goal.FStar_Tactics_Types.context
                 in
              match uu____5964 with
              | FStar_Pervasives_Native.None  ->
                  fail "Cannot clear; binder not in environment"
              | FStar_Pervasives_Native.Some (e',bvs) ->
                  let rec check1 bvs1 =
                    match bvs1 with
                    | [] -> ret ()
                    | bv'::bvs2 ->
                        let uu____6011 =
                          free_in bv bv'.FStar_Syntax_Syntax.sort  in
                        if uu____6011
                        then
                          let uu____6014 =
                            let uu____6015 =
                              FStar_Syntax_Print.bv_to_string bv'  in
                            FStar_Util.format1
                              "Cannot clear; binder present in the type of %s"
                              uu____6015
                             in
                          fail uu____6014
                        else check1 bvs2
                     in
                  let uu____6017 =
                    free_in bv goal.FStar_Tactics_Types.goal_ty  in
                  if uu____6017
                  then fail "Cannot clear; binder present in goal"
                  else
                    (let uu____6021 = check1 bvs  in
                     bind uu____6021
                       (fun uu____6027  ->
                          let env' = push_bvs e' bvs  in
                          let uu____6029 =
                            new_uvar "clear.witness" env'
                              goal.FStar_Tactics_Types.goal_ty
                             in
                          bind uu____6029
                            (fun ut  ->
                               let uu____6035 =
                                 do_unify goal.FStar_Tactics_Types.context
                                   goal.FStar_Tactics_Types.witness ut
                                  in
                               bind uu____6035
                                 (fun b1  ->
                                    if b1
                                    then
                                      replace_cur
                                        (let uu___110_6044 = goal  in
                                         {
                                           FStar_Tactics_Types.context = env';
                                           FStar_Tactics_Types.witness = ut;
                                           FStar_Tactics_Types.goal_ty =
                                             (uu___110_6044.FStar_Tactics_Types.goal_ty);
                                           FStar_Tactics_Types.opts =
                                             (uu___110_6044.FStar_Tactics_Types.opts);
                                           FStar_Tactics_Types.is_guard =
                                             (uu___110_6044.FStar_Tactics_Types.is_guard)
                                         })
                                    else
                                      fail
                                        "Cannot clear; binder appears in witness"))))))
  
let (clear_top : unit -> unit tac) =
  fun uu____6052  ->
    let uu____6055 = cur_goal ()  in
    bind uu____6055
      (fun goal  ->
         let uu____6061 =
           FStar_TypeChecker_Env.pop_bv goal.FStar_Tactics_Types.context  in
         match uu____6061 with
         | FStar_Pervasives_Native.None  ->
             fail "Cannot clear; empty context"
         | FStar_Pervasives_Native.Some (x,uu____6075) ->
             let uu____6080 = FStar_Syntax_Syntax.mk_binder x  in
             clear uu____6080)
  
let (prune : Prims.string -> unit tac) =
  fun s  ->
    let uu____6090 = cur_goal ()  in
    bind uu____6090
      (fun g  ->
         let ctx = g.FStar_Tactics_Types.context  in
         let ctx' =
           let uu____6100 = FStar_Ident.path_of_text s  in
           FStar_TypeChecker_Env.rem_proof_ns ctx uu____6100  in
         let g' =
           let uu___111_6102 = g  in
           {
             FStar_Tactics_Types.context = ctx';
             FStar_Tactics_Types.witness =
               (uu___111_6102.FStar_Tactics_Types.witness);
             FStar_Tactics_Types.goal_ty =
               (uu___111_6102.FStar_Tactics_Types.goal_ty);
             FStar_Tactics_Types.opts =
               (uu___111_6102.FStar_Tactics_Types.opts);
             FStar_Tactics_Types.is_guard =
               (uu___111_6102.FStar_Tactics_Types.is_guard)
           }  in
         bind __dismiss (fun uu____6104  -> add_goals [g']))
  
let (addns : Prims.string -> unit tac) =
  fun s  ->
    let uu____6114 = cur_goal ()  in
    bind uu____6114
      (fun g  ->
         let ctx = g.FStar_Tactics_Types.context  in
         let ctx' =
           let uu____6124 = FStar_Ident.path_of_text s  in
           FStar_TypeChecker_Env.add_proof_ns ctx uu____6124  in
         let g' =
           let uu___112_6126 = g  in
           {
             FStar_Tactics_Types.context = ctx';
             FStar_Tactics_Types.witness =
               (uu___112_6126.FStar_Tactics_Types.witness);
             FStar_Tactics_Types.goal_ty =
               (uu___112_6126.FStar_Tactics_Types.goal_ty);
             FStar_Tactics_Types.opts =
               (uu___112_6126.FStar_Tactics_Types.opts);
             FStar_Tactics_Types.is_guard =
               (uu___112_6126.FStar_Tactics_Types.is_guard)
           }  in
         bind __dismiss (fun uu____6128  -> add_goals [g']))
  
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
            let uu____6168 = FStar_Syntax_Subst.compress t  in
            uu____6168.FStar_Syntax_Syntax.n  in
          let uu____6171 =
            if d = FStar_Tactics_Types.TopDown
            then
              f env
                (let uu___116_6177 = t  in
                 {
                   FStar_Syntax_Syntax.n = tn;
                   FStar_Syntax_Syntax.pos =
                     (uu___116_6177.FStar_Syntax_Syntax.pos);
                   FStar_Syntax_Syntax.vars =
                     (uu___116_6177.FStar_Syntax_Syntax.vars)
                 })
            else ret t  in
          bind uu____6171
            (fun t1  ->
               let ff = tac_fold_env d f env  in
               let tn1 =
                 let uu____6193 =
                   let uu____6194 = FStar_Syntax_Subst.compress t1  in
                   uu____6194.FStar_Syntax_Syntax.n  in
                 match uu____6193 with
                 | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
                     let uu____6221 = ff hd1  in
                     bind uu____6221
                       (fun hd2  ->
                          let fa uu____6243 =
                            match uu____6243 with
                            | (a,q) ->
                                let uu____6256 = ff a  in
                                bind uu____6256 (fun a1  -> ret (a1, q))
                             in
                          let uu____6269 = mapM fa args  in
                          bind uu____6269
                            (fun args1  ->
                               ret (FStar_Syntax_Syntax.Tm_app (hd2, args1))))
                 | FStar_Syntax_Syntax.Tm_abs (bs,t2,k) ->
                     let uu____6329 = FStar_Syntax_Subst.open_term bs t2  in
                     (match uu____6329 with
                      | (bs1,t') ->
                          let uu____6338 =
                            let uu____6341 =
                              FStar_TypeChecker_Env.push_binders env bs1  in
                            tac_fold_env d f uu____6341 t'  in
                          bind uu____6338
                            (fun t''  ->
                               let uu____6345 =
                                 let uu____6346 =
                                   let uu____6363 =
                                     FStar_Syntax_Subst.close_binders bs1  in
                                   let uu____6364 =
                                     FStar_Syntax_Subst.close bs1 t''  in
                                   (uu____6363, uu____6364, k)  in
                                 FStar_Syntax_Syntax.Tm_abs uu____6346  in
                               ret uu____6345))
                 | FStar_Syntax_Syntax.Tm_arrow (bs,k) -> ret tn
                 | FStar_Syntax_Syntax.Tm_match (hd1,brs) ->
                     let uu____6423 = ff hd1  in
                     bind uu____6423
                       (fun hd2  ->
                          let ffb br =
                            let uu____6438 =
                              FStar_Syntax_Subst.open_branch br  in
                            match uu____6438 with
                            | (pat,w,e) ->
                                let bvs = FStar_Syntax_Syntax.pat_bvs pat  in
                                let ff1 =
                                  let uu____6470 =
                                    FStar_TypeChecker_Env.push_bvs env bvs
                                     in
                                  tac_fold_env d f uu____6470  in
                                let uu____6471 = ff1 e  in
                                bind uu____6471
                                  (fun e1  ->
                                     let br1 =
                                       FStar_Syntax_Subst.close_branch
                                         (pat, w, e1)
                                        in
                                     ret br1)
                             in
                          let uu____6484 = mapM ffb brs  in
                          bind uu____6484
                            (fun brs1  ->
                               ret (FStar_Syntax_Syntax.Tm_match (hd2, brs1))))
                 | FStar_Syntax_Syntax.Tm_let
                     ((false
                       ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inl bv;
                          FStar_Syntax_Syntax.lbunivs = uu____6498;
                          FStar_Syntax_Syntax.lbtyp = uu____6499;
                          FStar_Syntax_Syntax.lbeff = uu____6500;
                          FStar_Syntax_Syntax.lbdef = def;
                          FStar_Syntax_Syntax.lbattrs = uu____6502;
                          FStar_Syntax_Syntax.lbpos = uu____6503;_}::[]),e)
                     ->
                     let lb =
                       let uu____6528 =
                         let uu____6529 = FStar_Syntax_Subst.compress t1  in
                         uu____6529.FStar_Syntax_Syntax.n  in
                       match uu____6528 with
                       | FStar_Syntax_Syntax.Tm_let
                           ((false ,lb::[]),uu____6533) -> lb
                       | uu____6546 -> failwith "impossible"  in
                     let fflb lb1 =
                       let uu____6555 = ff lb1.FStar_Syntax_Syntax.lbdef  in
                       bind uu____6555
                         (fun def1  ->
                            ret
                              (let uu___113_6561 = lb1  in
                               {
                                 FStar_Syntax_Syntax.lbname =
                                   (uu___113_6561.FStar_Syntax_Syntax.lbname);
                                 FStar_Syntax_Syntax.lbunivs =
                                   (uu___113_6561.FStar_Syntax_Syntax.lbunivs);
                                 FStar_Syntax_Syntax.lbtyp =
                                   (uu___113_6561.FStar_Syntax_Syntax.lbtyp);
                                 FStar_Syntax_Syntax.lbeff =
                                   (uu___113_6561.FStar_Syntax_Syntax.lbeff);
                                 FStar_Syntax_Syntax.lbdef = def1;
                                 FStar_Syntax_Syntax.lbattrs =
                                   (uu___113_6561.FStar_Syntax_Syntax.lbattrs);
                                 FStar_Syntax_Syntax.lbpos =
                                   (uu___113_6561.FStar_Syntax_Syntax.lbpos)
                               }))
                        in
                     let uu____6562 = fflb lb  in
                     bind uu____6562
                       (fun lb1  ->
                          let uu____6572 =
                            let uu____6577 =
                              let uu____6578 =
                                FStar_Syntax_Syntax.mk_binder bv  in
                              [uu____6578]  in
                            FStar_Syntax_Subst.open_term uu____6577 e  in
                          match uu____6572 with
                          | (bs,e1) ->
                              let ff1 =
                                let uu____6590 =
                                  FStar_TypeChecker_Env.push_binders env bs
                                   in
                                tac_fold_env d f uu____6590  in
                              let uu____6591 = ff1 e1  in
                              bind uu____6591
                                (fun e2  ->
                                   let e3 = FStar_Syntax_Subst.close bs e2
                                      in
                                   ret
                                     (FStar_Syntax_Syntax.Tm_let
                                        ((false, [lb1]), e3))))
                 | FStar_Syntax_Syntax.Tm_let ((true ,lbs),e) ->
                     let fflb lb =
                       let uu____6630 = ff lb.FStar_Syntax_Syntax.lbdef  in
                       bind uu____6630
                         (fun def  ->
                            ret
                              (let uu___114_6636 = lb  in
                               {
                                 FStar_Syntax_Syntax.lbname =
                                   (uu___114_6636.FStar_Syntax_Syntax.lbname);
                                 FStar_Syntax_Syntax.lbunivs =
                                   (uu___114_6636.FStar_Syntax_Syntax.lbunivs);
                                 FStar_Syntax_Syntax.lbtyp =
                                   (uu___114_6636.FStar_Syntax_Syntax.lbtyp);
                                 FStar_Syntax_Syntax.lbeff =
                                   (uu___114_6636.FStar_Syntax_Syntax.lbeff);
                                 FStar_Syntax_Syntax.lbdef = def;
                                 FStar_Syntax_Syntax.lbattrs =
                                   (uu___114_6636.FStar_Syntax_Syntax.lbattrs);
                                 FStar_Syntax_Syntax.lbpos =
                                   (uu___114_6636.FStar_Syntax_Syntax.lbpos)
                               }))
                        in
                     let uu____6637 = FStar_Syntax_Subst.open_let_rec lbs e
                        in
                     (match uu____6637 with
                      | (lbs1,e1) ->
                          let uu____6652 = mapM fflb lbs1  in
                          bind uu____6652
                            (fun lbs2  ->
                               let uu____6664 = ff e1  in
                               bind uu____6664
                                 (fun e2  ->
                                    let uu____6672 =
                                      FStar_Syntax_Subst.close_let_rec lbs2
                                        e2
                                       in
                                    match uu____6672 with
                                    | (lbs3,e3) ->
                                        ret
                                          (FStar_Syntax_Syntax.Tm_let
                                             ((true, lbs3), e3)))))
                 | FStar_Syntax_Syntax.Tm_ascribed (t2,asc,eff) ->
                     let uu____6738 = ff t2  in
                     bind uu____6738
                       (fun t3  ->
                          ret
                            (FStar_Syntax_Syntax.Tm_ascribed (t3, asc, eff)))
                 | FStar_Syntax_Syntax.Tm_meta (t2,m) ->
                     let uu____6767 = ff t2  in
                     bind uu____6767
                       (fun t3  -> ret (FStar_Syntax_Syntax.Tm_meta (t3, m)))
                 | uu____6772 -> ret tn  in
               bind tn1
                 (fun tn2  ->
                    let t' =
                      let uu___115_6779 = t1  in
                      {
                        FStar_Syntax_Syntax.n = tn2;
                        FStar_Syntax_Syntax.pos =
                          (uu___115_6779.FStar_Syntax_Syntax.pos);
                        FStar_Syntax_Syntax.vars =
                          (uu___115_6779.FStar_Syntax_Syntax.vars)
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
            let uu____6818 = FStar_TypeChecker_TcTerm.tc_term env t  in
            match uu____6818 with
            | (t1,lcomp,g) ->
                let uu____6830 =
                  (let uu____6833 =
                     FStar_Syntax_Util.is_pure_or_ghost_lcomp lcomp  in
                   Prims.op_Negation uu____6833) ||
                    (let uu____6835 = FStar_TypeChecker_Rel.is_trivial g  in
                     Prims.op_Negation uu____6835)
                   in
                if uu____6830
                then ret t1
                else
                  (let rewrite_eq =
                     let typ = lcomp.FStar_Syntax_Syntax.res_typ  in
                     let uu____6845 = new_uvar "pointwise_rec" env typ  in
                     bind uu____6845
                       (fun ut  ->
                          let uu____6852 =
                            log ps
                              (fun uu____6856  ->
                                 let uu____6857 =
                                   FStar_Syntax_Print.term_to_string t1  in
                                 let uu____6858 =
                                   FStar_Syntax_Print.term_to_string ut  in
                                 FStar_Util.print2
                                   "Pointwise_rec: making equality\n\t%s ==\n\t%s\n"
                                   uu____6857 uu____6858)
                             in
                          let uu____6859 =
                            let uu____6862 =
                              let uu____6863 =
                                FStar_TypeChecker_TcTerm.universe_of env typ
                                 in
                              FStar_Syntax_Util.mk_eq2 uu____6863 typ t1 ut
                               in
                            add_irrelevant_goal "pointwise_rec equation" env
                              uu____6862 opts
                             in
                          bind uu____6859
                            (fun uu____6866  ->
                               let uu____6867 =
                                 bind tau
                                   (fun uu____6873  ->
                                      let ut1 =
                                        FStar_TypeChecker_Normalize.reduce_uvar_solutions
                                          env ut
                                         in
                                      let uu____6875 =
                                        log ps
                                          (fun uu____6879  ->
                                             let uu____6880 =
                                               FStar_Syntax_Print.term_to_string
                                                 t1
                                                in
                                             let uu____6881 =
                                               FStar_Syntax_Print.term_to_string
                                                 ut1
                                                in
                                             FStar_Util.print2
                                               "Pointwise_rec: succeeded rewriting\n\t%s to\n\t%s\n"
                                               uu____6880 uu____6881)
                                         in
                                      ret ut1)
                                  in
                               focus uu____6867))
                      in
                   let uu____6882 = trytac' rewrite_eq  in
                   bind uu____6882
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
          let uu____7054 = FStar_Syntax_Subst.compress t  in
          maybe_continue ctrl uu____7054
            (fun t1  ->
               let uu____7058 =
                 f env
                   (let uu___119_7067 = t1  in
                    {
                      FStar_Syntax_Syntax.n = (t1.FStar_Syntax_Syntax.n);
                      FStar_Syntax_Syntax.pos =
                        (uu___119_7067.FStar_Syntax_Syntax.pos);
                      FStar_Syntax_Syntax.vars =
                        (uu___119_7067.FStar_Syntax_Syntax.vars)
                    })
                  in
               bind uu____7058
                 (fun uu____7079  ->
                    match uu____7079 with
                    | (t2,ctrl1) ->
                        maybe_continue ctrl1 t2
                          (fun t3  ->
                             let uu____7098 =
                               let uu____7099 =
                                 FStar_Syntax_Subst.compress t3  in
                               uu____7099.FStar_Syntax_Syntax.n  in
                             match uu____7098 with
                             | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
                                 let uu____7132 =
                                   ctrl_tac_fold f env ctrl1 hd1  in
                                 bind uu____7132
                                   (fun uu____7157  ->
                                      match uu____7157 with
                                      | (hd2,ctrl2) ->
                                          let ctrl3 = keep_going ctrl2  in
                                          let uu____7173 =
                                            ctrl_tac_fold_args f env ctrl3
                                              args
                                             in
                                          bind uu____7173
                                            (fun uu____7200  ->
                                               match uu____7200 with
                                               | (args1,ctrl4) ->
                                                   ret
                                                     ((let uu___117_7230 = t3
                                                          in
                                                       {
                                                         FStar_Syntax_Syntax.n
                                                           =
                                                           (FStar_Syntax_Syntax.Tm_app
                                                              (hd2, args1));
                                                         FStar_Syntax_Syntax.pos
                                                           =
                                                           (uu___117_7230.FStar_Syntax_Syntax.pos);
                                                         FStar_Syntax_Syntax.vars
                                                           =
                                                           (uu___117_7230.FStar_Syntax_Syntax.vars)
                                                       }), ctrl4)))
                             | FStar_Syntax_Syntax.Tm_abs (bs,t4,k) ->
                                 let uu____7256 =
                                   FStar_Syntax_Subst.open_term bs t4  in
                                 (match uu____7256 with
                                  | (bs1,t') ->
                                      let uu____7271 =
                                        let uu____7278 =
                                          FStar_TypeChecker_Env.push_binders
                                            env bs1
                                           in
                                        ctrl_tac_fold f uu____7278 ctrl1 t'
                                         in
                                      bind uu____7271
                                        (fun uu____7296  ->
                                           match uu____7296 with
                                           | (t'',ctrl2) ->
                                               let uu____7311 =
                                                 let uu____7318 =
                                                   let uu___118_7321 = t4  in
                                                   let uu____7324 =
                                                     let uu____7325 =
                                                       let uu____7342 =
                                                         FStar_Syntax_Subst.close_binders
                                                           bs1
                                                          in
                                                       let uu____7343 =
                                                         FStar_Syntax_Subst.close
                                                           bs1 t''
                                                          in
                                                       (uu____7342,
                                                         uu____7343, k)
                                                        in
                                                     FStar_Syntax_Syntax.Tm_abs
                                                       uu____7325
                                                      in
                                                   {
                                                     FStar_Syntax_Syntax.n =
                                                       uu____7324;
                                                     FStar_Syntax_Syntax.pos
                                                       =
                                                       (uu___118_7321.FStar_Syntax_Syntax.pos);
                                                     FStar_Syntax_Syntax.vars
                                                       =
                                                       (uu___118_7321.FStar_Syntax_Syntax.vars)
                                                   }  in
                                                 (uu____7318, ctrl2)  in
                                               ret uu____7311))
                             | FStar_Syntax_Syntax.Tm_arrow (bs,k) ->
                                 ret (t3, ctrl1)
                             | uu____7376 -> ret (t3, ctrl1))))

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
              let uu____7427 = ctrl_tac_fold f env ctrl t  in
              bind uu____7427
                (fun uu____7455  ->
                   match uu____7455 with
                   | (t1,ctrl1) ->
                       let uu____7474 = ctrl_tac_fold_args f env ctrl1 ts1
                          in
                       bind uu____7474
                         (fun uu____7505  ->
                            match uu____7505 with
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
              let uu____7601 =
                let uu____7608 =
                  add_irrelevant_goal "dummy" env FStar_Syntax_Util.t_true
                    opts
                   in
                bind uu____7608
                  (fun uu____7617  ->
                     let uu____7618 = ctrl t1  in
                     bind uu____7618
                       (fun res  ->
                          let uu____7641 = trivial ()  in
                          bind uu____7641 (fun uu____7649  -> ret res)))
                 in
              bind uu____7601
                (fun uu____7665  ->
                   match uu____7665 with
                   | (should_rewrite,ctrl1) ->
                       if Prims.op_Negation should_rewrite
                       then ret (t1, ctrl1)
                       else
                         (let uu____7689 =
                            FStar_TypeChecker_TcTerm.tc_term env t1  in
                          match uu____7689 with
                          | (t2,lcomp,g) ->
                              let uu____7705 =
                                (let uu____7708 =
                                   FStar_Syntax_Util.is_pure_or_ghost_lcomp
                                     lcomp
                                    in
                                 Prims.op_Negation uu____7708) ||
                                  (let uu____7710 =
                                     FStar_TypeChecker_Rel.is_trivial g  in
                                   Prims.op_Negation uu____7710)
                                 in
                              if uu____7705
                              then ret (t2, globalStop)
                              else
                                (let typ = lcomp.FStar_Syntax_Syntax.res_typ
                                    in
                                 let uu____7725 =
                                   new_uvar "pointwise_rec" env typ  in
                                 bind uu____7725
                                   (fun ut  ->
                                      let uu____7736 =
                                        log ps
                                          (fun uu____7740  ->
                                             let uu____7741 =
                                               FStar_Syntax_Print.term_to_string
                                                 t2
                                                in
                                             let uu____7742 =
                                               FStar_Syntax_Print.term_to_string
                                                 ut
                                                in
                                             FStar_Util.print2
                                               "Pointwise_rec: making equality\n\t%s ==\n\t%s\n"
                                               uu____7741 uu____7742)
                                         in
                                      let uu____7743 =
                                        let uu____7746 =
                                          let uu____7747 =
                                            FStar_TypeChecker_TcTerm.universe_of
                                              env typ
                                             in
                                          FStar_Syntax_Util.mk_eq2 uu____7747
                                            typ t2 ut
                                           in
                                        add_irrelevant_goal
                                          "rewrite_rec equation" env
                                          uu____7746 opts
                                         in
                                      bind uu____7743
                                        (fun uu____7754  ->
                                           let uu____7755 =
                                             bind rewriter
                                               (fun uu____7769  ->
                                                  let ut1 =
                                                    FStar_TypeChecker_Normalize.reduce_uvar_solutions
                                                      env ut
                                                     in
                                                  let uu____7771 =
                                                    log ps
                                                      (fun uu____7775  ->
                                                         let uu____7776 =
                                                           FStar_Syntax_Print.term_to_string
                                                             t2
                                                            in
                                                         let uu____7777 =
                                                           FStar_Syntax_Print.term_to_string
                                                             ut1
                                                            in
                                                         FStar_Util.print2
                                                           "rewrite_rec: succeeded rewriting\n\t%s to\n\t%s\n"
                                                           uu____7776
                                                           uu____7777)
                                                     in
                                                  ret (ut1, ctrl1))
                                              in
                                           focus uu____7755)))))
  
let (topdown_rewrite :
  (FStar_Syntax_Syntax.term ->
     (Prims.bool,FStar_BigInt.t) FStar_Pervasives_Native.tuple2 tac)
    -> unit tac -> unit tac)
  =
  fun ctrl  ->
    fun rewriter  ->
      bind get
        (fun ps  ->
           let uu____7825 =
             match ps.FStar_Tactics_Types.goals with
             | g::gs -> (g, gs)
             | [] -> failwith "Pointwise: no goals"  in
           match uu____7825 with
           | (g,gs) ->
               let gt1 = g.FStar_Tactics_Types.goal_ty  in
               let uu____7859 =
                 log ps
                   (fun uu____7862  ->
                      let uu____7863 = FStar_Syntax_Print.term_to_string gt1
                         in
                      FStar_Util.print1 "Topdown_rewrite starting with %s\n"
                        uu____7863)
                  in
               bind dismiss_all
                 (fun uu____7866  ->
                    let uu____7867 =
                      ctrl_tac_fold
                        (rewrite_rec ps ctrl rewriter
                           g.FStar_Tactics_Types.opts)
                        g.FStar_Tactics_Types.context keepGoing gt1
                       in
                    bind uu____7867
                      (fun uu____7885  ->
                         match uu____7885 with
                         | (gt',uu____7893) ->
                             let uu____7894 =
                               log ps
                                 (fun uu____7897  ->
                                    let uu____7898 =
                                      FStar_Syntax_Print.term_to_string gt'
                                       in
                                    FStar_Util.print1
                                      "Topdown_rewrite seems to have succeded with %s\n"
                                      uu____7898)
                                in
                             let uu____7899 = push_goals gs  in
                             bind uu____7899
                               (fun uu____7903  ->
                                  add_goals
                                    [(let uu___120_7905 = g  in
                                      {
                                        FStar_Tactics_Types.context =
                                          (uu___120_7905.FStar_Tactics_Types.context);
                                        FStar_Tactics_Types.witness =
                                          (uu___120_7905.FStar_Tactics_Types.witness);
                                        FStar_Tactics_Types.goal_ty = gt';
                                        FStar_Tactics_Types.opts =
                                          (uu___120_7905.FStar_Tactics_Types.opts);
                                        FStar_Tactics_Types.is_guard =
                                          (uu___120_7905.FStar_Tactics_Types.is_guard)
                                      })]))))
  
let (pointwise : FStar_Tactics_Types.direction -> unit tac -> unit tac) =
  fun d  ->
    fun tau  ->
      bind get
        (fun ps  ->
           let uu____7931 =
             match ps.FStar_Tactics_Types.goals with
             | g::gs -> (g, gs)
             | [] -> failwith "Pointwise: no goals"  in
           match uu____7931 with
           | (g,gs) ->
               let gt1 = g.FStar_Tactics_Types.goal_ty  in
               let uu____7965 =
                 log ps
                   (fun uu____7968  ->
                      let uu____7969 = FStar_Syntax_Print.term_to_string gt1
                         in
                      FStar_Util.print1 "Pointwise starting with %s\n"
                        uu____7969)
                  in
               bind dismiss_all
                 (fun uu____7972  ->
                    let uu____7973 =
                      tac_fold_env d
                        (pointwise_rec ps tau g.FStar_Tactics_Types.opts)
                        g.FStar_Tactics_Types.context gt1
                       in
                    bind uu____7973
                      (fun gt'  ->
                         let uu____7980 =
                           log ps
                             (fun uu____7983  ->
                                let uu____7984 =
                                  FStar_Syntax_Print.term_to_string gt'  in
                                FStar_Util.print1
                                  "Pointwise seems to have succeded with %s\n"
                                  uu____7984)
                            in
                         let uu____7985 = push_goals gs  in
                         bind uu____7985
                           (fun uu____7989  ->
                              add_goals
                                [(let uu___121_7991 = g  in
                                  {
                                    FStar_Tactics_Types.context =
                                      (uu___121_7991.FStar_Tactics_Types.context);
                                    FStar_Tactics_Types.witness =
                                      (uu___121_7991.FStar_Tactics_Types.witness);
                                    FStar_Tactics_Types.goal_ty = gt';
                                    FStar_Tactics_Types.opts =
                                      (uu___121_7991.FStar_Tactics_Types.opts);
                                    FStar_Tactics_Types.is_guard =
                                      (uu___121_7991.FStar_Tactics_Types.is_guard)
                                  })]))))
  
let (trefl : unit -> unit tac) =
  fun uu____7998  ->
    let uu____8001 = cur_goal ()  in
    bind uu____8001
      (fun g  ->
         let uu____8019 =
           FStar_Syntax_Util.un_squash g.FStar_Tactics_Types.goal_ty  in
         match uu____8019 with
         | FStar_Pervasives_Native.Some t ->
             let uu____8031 = FStar_Syntax_Util.head_and_args' t  in
             (match uu____8031 with
              | (hd1,args) ->
                  let uu____8064 =
                    let uu____8077 =
                      let uu____8078 = FStar_Syntax_Util.un_uinst hd1  in
                      uu____8078.FStar_Syntax_Syntax.n  in
                    (uu____8077, args)  in
                  (match uu____8064 with
                   | (FStar_Syntax_Syntax.Tm_fvar
                      fv,uu____8092::(l,uu____8094)::(r,uu____8096)::[]) when
                       FStar_Syntax_Syntax.fv_eq_lid fv
                         FStar_Parser_Const.eq2_lid
                       ->
                       let uu____8143 =
                         do_unify g.FStar_Tactics_Types.context l r  in
                       bind uu____8143
                         (fun b  ->
                            if Prims.op_Negation b
                            then
                              let uu____8152 =
                                tts g.FStar_Tactics_Types.context l  in
                              let uu____8153 =
                                tts g.FStar_Tactics_Types.context r  in
                              fail2
                                "trefl: not a trivial equality (%s vs %s)"
                                uu____8152 uu____8153
                            else solve g FStar_Syntax_Util.exp_unit)
                   | (hd2,uu____8156) ->
                       let uu____8173 = tts g.FStar_Tactics_Types.context t
                          in
                       fail1 "trefl: not an equality (%s)" uu____8173))
         | FStar_Pervasives_Native.None  -> fail "not an irrelevant goal")
  
let (dup : unit -> unit tac) =
  fun uu____8182  ->
    let uu____8185 = cur_goal ()  in
    bind uu____8185
      (fun g  ->
         let uu____8191 =
           new_uvar "dup" g.FStar_Tactics_Types.context
             g.FStar_Tactics_Types.goal_ty
            in
         bind uu____8191
           (fun u  ->
              let g' =
                let uu___122_8198 = g  in
                {
                  FStar_Tactics_Types.context =
                    (uu___122_8198.FStar_Tactics_Types.context);
                  FStar_Tactics_Types.witness = u;
                  FStar_Tactics_Types.goal_ty =
                    (uu___122_8198.FStar_Tactics_Types.goal_ty);
                  FStar_Tactics_Types.opts =
                    (uu___122_8198.FStar_Tactics_Types.opts);
                  FStar_Tactics_Types.is_guard =
                    (uu___122_8198.FStar_Tactics_Types.is_guard)
                }  in
              bind __dismiss
                (fun uu____8201  ->
                   let uu____8202 =
                     let uu____8205 =
                       let uu____8206 =
                         FStar_TypeChecker_TcTerm.universe_of
                           g.FStar_Tactics_Types.context
                           g.FStar_Tactics_Types.goal_ty
                          in
                       FStar_Syntax_Util.mk_eq2 uu____8206
                         g.FStar_Tactics_Types.goal_ty u
                         g.FStar_Tactics_Types.witness
                        in
                     add_irrelevant_goal "dup equation"
                       g.FStar_Tactics_Types.context uu____8205
                       g.FStar_Tactics_Types.opts
                      in
                   bind uu____8202
                     (fun uu____8209  ->
                        let uu____8210 = add_goals [g']  in
                        bind uu____8210 (fun uu____8214  -> ret ())))))
  
let (flip : unit -> unit tac) =
  fun uu____8221  ->
    bind get
      (fun ps  ->
         match ps.FStar_Tactics_Types.goals with
         | g1::g2::gs ->
             set
               (let uu___123_8238 = ps  in
                {
                  FStar_Tactics_Types.main_context =
                    (uu___123_8238.FStar_Tactics_Types.main_context);
                  FStar_Tactics_Types.main_goal =
                    (uu___123_8238.FStar_Tactics_Types.main_goal);
                  FStar_Tactics_Types.all_implicits =
                    (uu___123_8238.FStar_Tactics_Types.all_implicits);
                  FStar_Tactics_Types.goals = (g2 :: g1 :: gs);
                  FStar_Tactics_Types.smt_goals =
                    (uu___123_8238.FStar_Tactics_Types.smt_goals);
                  FStar_Tactics_Types.depth =
                    (uu___123_8238.FStar_Tactics_Types.depth);
                  FStar_Tactics_Types.__dump =
                    (uu___123_8238.FStar_Tactics_Types.__dump);
                  FStar_Tactics_Types.psc =
                    (uu___123_8238.FStar_Tactics_Types.psc);
                  FStar_Tactics_Types.entry_range =
                    (uu___123_8238.FStar_Tactics_Types.entry_range);
                  FStar_Tactics_Types.guard_policy =
                    (uu___123_8238.FStar_Tactics_Types.guard_policy);
                  FStar_Tactics_Types.freshness =
                    (uu___123_8238.FStar_Tactics_Types.freshness)
                })
         | uu____8239 -> fail "flip: less than 2 goals")
  
let (later : unit -> unit tac) =
  fun uu____8248  ->
    bind get
      (fun ps  ->
         match ps.FStar_Tactics_Types.goals with
         | [] -> ret ()
         | g::gs ->
             set
               (let uu___124_8261 = ps  in
                {
                  FStar_Tactics_Types.main_context =
                    (uu___124_8261.FStar_Tactics_Types.main_context);
                  FStar_Tactics_Types.main_goal =
                    (uu___124_8261.FStar_Tactics_Types.main_goal);
                  FStar_Tactics_Types.all_implicits =
                    (uu___124_8261.FStar_Tactics_Types.all_implicits);
                  FStar_Tactics_Types.goals = (FStar_List.append gs [g]);
                  FStar_Tactics_Types.smt_goals =
                    (uu___124_8261.FStar_Tactics_Types.smt_goals);
                  FStar_Tactics_Types.depth =
                    (uu___124_8261.FStar_Tactics_Types.depth);
                  FStar_Tactics_Types.__dump =
                    (uu___124_8261.FStar_Tactics_Types.__dump);
                  FStar_Tactics_Types.psc =
                    (uu___124_8261.FStar_Tactics_Types.psc);
                  FStar_Tactics_Types.entry_range =
                    (uu___124_8261.FStar_Tactics_Types.entry_range);
                  FStar_Tactics_Types.guard_policy =
                    (uu___124_8261.FStar_Tactics_Types.guard_policy);
                  FStar_Tactics_Types.freshness =
                    (uu___124_8261.FStar_Tactics_Types.freshness)
                }))
  
let (qed : unit -> unit tac) =
  fun uu____8268  ->
    bind get
      (fun ps  ->
         match ps.FStar_Tactics_Types.goals with
         | [] -> ret ()
         | uu____8275 -> fail "Not done!")
  
let (cases :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 tac)
  =
  fun t  ->
    let uu____8295 =
      let uu____8302 = cur_goal ()  in
      bind uu____8302
        (fun g  ->
           let uu____8312 = __tc g.FStar_Tactics_Types.context t  in
           bind uu____8312
             (fun uu____8348  ->
                match uu____8348 with
                | (t1,typ,guard) ->
                    let uu____8364 = FStar_Syntax_Util.head_and_args typ  in
                    (match uu____8364 with
                     | (hd1,args) ->
                         let uu____8407 =
                           let uu____8420 =
                             let uu____8421 = FStar_Syntax_Util.un_uinst hd1
                                in
                             uu____8421.FStar_Syntax_Syntax.n  in
                           (uu____8420, args)  in
                         (match uu____8407 with
                          | (FStar_Syntax_Syntax.Tm_fvar
                             fv,(p,uu____8440)::(q,uu____8442)::[]) when
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
                                let uu___125_8480 = g  in
                                let uu____8481 =
                                  FStar_TypeChecker_Env.push_bv
                                    g.FStar_Tactics_Types.context v_p
                                   in
                                {
                                  FStar_Tactics_Types.context = uu____8481;
                                  FStar_Tactics_Types.witness =
                                    (uu___125_8480.FStar_Tactics_Types.witness);
                                  FStar_Tactics_Types.goal_ty =
                                    (uu___125_8480.FStar_Tactics_Types.goal_ty);
                                  FStar_Tactics_Types.opts =
                                    (uu___125_8480.FStar_Tactics_Types.opts);
                                  FStar_Tactics_Types.is_guard =
                                    (uu___125_8480.FStar_Tactics_Types.is_guard)
                                }  in
                              let g2 =
                                let uu___126_8483 = g  in
                                let uu____8484 =
                                  FStar_TypeChecker_Env.push_bv
                                    g.FStar_Tactics_Types.context v_q
                                   in
                                {
                                  FStar_Tactics_Types.context = uu____8484;
                                  FStar_Tactics_Types.witness =
                                    (uu___126_8483.FStar_Tactics_Types.witness);
                                  FStar_Tactics_Types.goal_ty =
                                    (uu___126_8483.FStar_Tactics_Types.goal_ty);
                                  FStar_Tactics_Types.opts =
                                    (uu___126_8483.FStar_Tactics_Types.opts);
                                  FStar_Tactics_Types.is_guard =
                                    (uu___126_8483.FStar_Tactics_Types.is_guard)
                                }  in
                              bind __dismiss
                                (fun uu____8491  ->
                                   let uu____8492 = add_goals [g1; g2]  in
                                   bind uu____8492
                                     (fun uu____8501  ->
                                        let uu____8502 =
                                          let uu____8507 =
                                            FStar_Syntax_Syntax.bv_to_name
                                              v_p
                                             in
                                          let uu____8508 =
                                            FStar_Syntax_Syntax.bv_to_name
                                              v_q
                                             in
                                          (uu____8507, uu____8508)  in
                                        ret uu____8502))
                          | uu____8513 ->
                              let uu____8526 =
                                tts g.FStar_Tactics_Types.context typ  in
                              fail1 "Not a disjunction: %s" uu____8526))))
       in
    FStar_All.pipe_left (wrap_err "cases") uu____8295
  
let (set_options : Prims.string -> unit tac) =
  fun s  ->
    let uu____8556 = cur_goal ()  in
    bind uu____8556
      (fun g  ->
         let uu____8567 = FStar_Options.push ()  in
         let uu____8568 =
           let uu____8569 = FStar_Util.smap_copy g.FStar_Tactics_Types.opts
              in
           FStar_Options.set uu____8569  in
         let res = FStar_Options.set_options FStar_Options.Set s  in
         let opts' = FStar_Options.peek ()  in
         let uu____8572 = FStar_Options.pop ()  in
         match res with
         | FStar_Getopt.Success  ->
             let g' =
               let uu___127_8576 = g  in
               {
                 FStar_Tactics_Types.context =
                   (uu___127_8576.FStar_Tactics_Types.context);
                 FStar_Tactics_Types.witness =
                   (uu___127_8576.FStar_Tactics_Types.witness);
                 FStar_Tactics_Types.goal_ty =
                   (uu___127_8576.FStar_Tactics_Types.goal_ty);
                 FStar_Tactics_Types.opts = opts';
                 FStar_Tactics_Types.is_guard =
                   (uu___127_8576.FStar_Tactics_Types.is_guard)
               }  in
             replace_cur g'
         | FStar_Getopt.Error err ->
             fail2 "Setting options `%s` failed: %s" s err
         | FStar_Getopt.Help  ->
             fail1 "Setting options `%s` failed (got `Help`?)" s)
  
let (top_env : unit -> env tac) =
  fun uu____8584  ->
    bind get
      (fun ps  -> FStar_All.pipe_left ret ps.FStar_Tactics_Types.main_context)
  
let (cur_env : unit -> env tac) =
  fun uu____8597  ->
    let uu____8600 = cur_goal ()  in
    bind uu____8600
      (fun g  -> FStar_All.pipe_left ret g.FStar_Tactics_Types.context)
  
let (cur_goal' : unit -> FStar_Syntax_Syntax.term tac) =
  fun uu____8613  ->
    let uu____8616 = cur_goal ()  in
    bind uu____8616
      (fun g  -> FStar_All.pipe_left ret g.FStar_Tactics_Types.goal_ty)
  
let (cur_witness : unit -> FStar_Syntax_Syntax.term tac) =
  fun uu____8629  ->
    let uu____8632 = cur_goal ()  in
    bind uu____8632
      (fun g  -> FStar_All.pipe_left ret g.FStar_Tactics_Types.witness)
  
let (unquote :
  FStar_Reflection_Data.typ ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term tac)
  =
  fun ty  ->
    fun tm  ->
      let uu____8653 =
        let uu____8656 = cur_goal ()  in
        bind uu____8656
          (fun goal  ->
             let env =
               FStar_TypeChecker_Env.set_expected_typ
                 goal.FStar_Tactics_Types.context ty
                in
             let uu____8664 = __tc env tm  in
             bind uu____8664
               (fun uu____8684  ->
                  match uu____8684 with
                  | (tm1,typ,guard) ->
                      let uu____8696 =
                        proc_guard "unquote" env guard
                          goal.FStar_Tactics_Types.opts
                         in
                      bind uu____8696 (fun uu____8700  -> ret tm1)))
         in
      FStar_All.pipe_left (wrap_err "unquote") uu____8653
  
let (uvar_env :
  env ->
    FStar_Reflection_Data.typ FStar_Pervasives_Native.option ->
      FStar_Syntax_Syntax.term tac)
  =
  fun env  ->
    fun ty  ->
      let uu____8723 =
        match ty with
        | FStar_Pervasives_Native.Some ty1 -> ret ty1
        | FStar_Pervasives_Native.None  ->
            let uu____8729 =
              let uu____8730 = FStar_Syntax_Util.type_u ()  in
              FStar_All.pipe_left FStar_Pervasives_Native.fst uu____8730  in
            new_uvar "uvar_env.2" env uu____8729
         in
      bind uu____8723
        (fun typ  ->
           let uu____8742 = new_uvar "uvar_env" env typ  in
           bind uu____8742 (fun t  -> ret t))
  
let (unshelve : FStar_Syntax_Syntax.term -> unit tac) =
  fun t  ->
    let uu____8756 =
      bind get
        (fun ps  ->
           let env = ps.FStar_Tactics_Types.main_context  in
           let opts =
             match ps.FStar_Tactics_Types.goals with
             | g::uu____8773 -> g.FStar_Tactics_Types.opts
             | uu____8776 -> FStar_Options.peek ()  in
           let uu____8779 = FStar_Syntax_Util.head_and_args t  in
           match uu____8779 with
           | ({
                FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                  (uu____8796,typ);
                FStar_Syntax_Syntax.pos = uu____8798;
                FStar_Syntax_Syntax.vars = uu____8799;_},uu____8800)
               ->
               let uu____8845 =
                 let uu____8848 =
                   let uu____8849 = bnorm env t  in
                   let uu____8850 = bnorm env typ  in
                   {
                     FStar_Tactics_Types.context = env;
                     FStar_Tactics_Types.witness = uu____8849;
                     FStar_Tactics_Types.goal_ty = uu____8850;
                     FStar_Tactics_Types.opts = opts;
                     FStar_Tactics_Types.is_guard = false
                   }  in
                 [uu____8848]  in
               add_goals uu____8845
           | uu____8851 -> fail "not a uvar")
       in
    FStar_All.pipe_left (wrap_err "unshelve") uu____8756
  
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
          (fun uu____8908  ->
             let uu____8909 = FStar_Options.unsafe_tactic_exec ()  in
             if uu____8909
             then
               let s =
                 FStar_Util.launch_process true "tactic_launch" prog args
                   input (fun uu____8915  -> fun uu____8916  -> false)
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
        (fun uu____8934  ->
           let uu____8935 =
             FStar_Syntax_Syntax.gen_bv nm FStar_Pervasives_Native.None t  in
           ret uu____8935)
  
let (change : FStar_Reflection_Data.typ -> unit tac) =
  fun ty  ->
    let uu____8945 =
      mlog
        (fun uu____8950  ->
           let uu____8951 = FStar_Syntax_Print.term_to_string ty  in
           FStar_Util.print1 "change: ty = %s\n" uu____8951)
        (fun uu____8954  ->
           let uu____8955 = cur_goal ()  in
           bind uu____8955
             (fun g  ->
                let uu____8961 = __tc g.FStar_Tactics_Types.context ty  in
                bind uu____8961
                  (fun uu____8981  ->
                     match uu____8981 with
                     | (ty1,uu____8991,guard) ->
                         let uu____8993 =
                           proc_guard "change" g.FStar_Tactics_Types.context
                             guard g.FStar_Tactics_Types.opts
                            in
                         bind uu____8993
                           (fun uu____8998  ->
                              let uu____8999 =
                                do_unify g.FStar_Tactics_Types.context
                                  g.FStar_Tactics_Types.goal_ty ty1
                                 in
                              bind uu____8999
                                (fun bb  ->
                                   if bb
                                   then
                                     replace_cur
                                       (let uu___128_9008 = g  in
                                        {
                                          FStar_Tactics_Types.context =
                                            (uu___128_9008.FStar_Tactics_Types.context);
                                          FStar_Tactics_Types.witness =
                                            (uu___128_9008.FStar_Tactics_Types.witness);
                                          FStar_Tactics_Types.goal_ty = ty1;
                                          FStar_Tactics_Types.opts =
                                            (uu___128_9008.FStar_Tactics_Types.opts);
                                          FStar_Tactics_Types.is_guard =
                                            (uu___128_9008.FStar_Tactics_Types.is_guard)
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
                                      let uu____9015 =
                                        do_unify
                                          g.FStar_Tactics_Types.context ng
                                          nty
                                         in
                                      bind uu____9015
                                        (fun b  ->
                                           if b
                                           then
                                             replace_cur
                                               (let uu___129_9024 = g  in
                                                {
                                                  FStar_Tactics_Types.context
                                                    =
                                                    (uu___129_9024.FStar_Tactics_Types.context);
                                                  FStar_Tactics_Types.witness
                                                    =
                                                    (uu___129_9024.FStar_Tactics_Types.witness);
                                                  FStar_Tactics_Types.goal_ty
                                                    = ty1;
                                                  FStar_Tactics_Types.opts =
                                                    (uu___129_9024.FStar_Tactics_Types.opts);
                                                  FStar_Tactics_Types.is_guard
                                                    =
                                                    (uu___129_9024.FStar_Tactics_Types.is_guard)
                                                })
                                           else fail "not convertible")))))))
       in
    FStar_All.pipe_left (wrap_err "change") uu____8945
  
let rec last : 'a . 'a Prims.list -> 'a =
  fun l  ->
    match l with
    | [] -> failwith "last: empty list"
    | x::[] -> x
    | uu____9046::xs -> last xs
  
let rec init : 'a . 'a Prims.list -> 'a Prims.list =
  fun l  ->
    match l with
    | [] -> failwith "init: empty list"
    | x::[] -> []
    | x::xs -> let uu____9074 = init xs  in x :: uu____9074
  
let rec (inspect :
  FStar_Syntax_Syntax.term -> FStar_Reflection_Data.term_view tac) =
  fun t  ->
    let t1 = FStar_Syntax_Util.unascribe t  in
    let t2 = FStar_Syntax_Util.un_uinst t1  in
    match t2.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_meta (t3,uu____9091) -> inspect t3
    | FStar_Syntax_Syntax.Tm_name bv ->
        FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_Var bv)
    | FStar_Syntax_Syntax.Tm_bvar bv ->
        FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_BVar bv)
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_FVar fv)
    | FStar_Syntax_Syntax.Tm_app (hd1,[]) ->
        failwith "inspect: empty arguments on Tm_app"
    | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
        let uu____9148 = last args  in
        (match uu____9148 with
         | (a,q) ->
             let q' = FStar_Reflection_Basic.inspect_aqual q  in
             let uu____9170 =
               let uu____9171 =
                 let uu____9176 =
                   let uu____9179 =
                     let uu____9184 = init args  in
                     FStar_Syntax_Syntax.mk_Tm_app hd1 uu____9184  in
                   uu____9179 FStar_Pervasives_Native.None
                     t2.FStar_Syntax_Syntax.pos
                    in
                 (uu____9176, (a, q'))  in
               FStar_Reflection_Data.Tv_App uu____9171  in
             FStar_All.pipe_left ret uu____9170)
    | FStar_Syntax_Syntax.Tm_abs ([],uu____9205,uu____9206) ->
        failwith "inspect: empty arguments on Tm_abs"
    | FStar_Syntax_Syntax.Tm_abs (bs,t3,k) ->
        let uu____9250 = FStar_Syntax_Subst.open_term bs t3  in
        (match uu____9250 with
         | (bs1,t4) ->
             (match bs1 with
              | [] -> failwith "impossible"
              | b::bs2 ->
                  let uu____9283 =
                    let uu____9284 =
                      let uu____9289 = FStar_Syntax_Util.abs bs2 t4 k  in
                      (b, uu____9289)  in
                    FStar_Reflection_Data.Tv_Abs uu____9284  in
                  FStar_All.pipe_left ret uu____9283))
    | FStar_Syntax_Syntax.Tm_type uu____9296 ->
        FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_Type ())
    | FStar_Syntax_Syntax.Tm_arrow ([],k) ->
        failwith "inspect: empty binders on arrow"
    | FStar_Syntax_Syntax.Tm_arrow uu____9316 ->
        let uu____9329 = FStar_Syntax_Util.arrow_one t2  in
        (match uu____9329 with
         | FStar_Pervasives_Native.Some (b,c) ->
             FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_Arrow (b, c))
         | FStar_Pervasives_Native.None  -> failwith "impossible")
    | FStar_Syntax_Syntax.Tm_refine (bv,t3) ->
        let b = FStar_Syntax_Syntax.mk_binder bv  in
        let uu____9359 = FStar_Syntax_Subst.open_term [b] t3  in
        (match uu____9359 with
         | (b',t4) ->
             let b1 =
               match b' with
               | b'1::[] -> b'1
               | uu____9390 -> failwith "impossible"  in
             FStar_All.pipe_left ret
               (FStar_Reflection_Data.Tv_Refine
                  ((FStar_Pervasives_Native.fst b1), t4)))
    | FStar_Syntax_Syntax.Tm_constant c ->
        let uu____9398 =
          let uu____9399 = FStar_Reflection_Basic.inspect_const c  in
          FStar_Reflection_Data.Tv_Const uu____9399  in
        FStar_All.pipe_left ret uu____9398
    | FStar_Syntax_Syntax.Tm_uvar (u,t3) ->
        let uu____9428 =
          let uu____9429 =
            let uu____9434 =
              let uu____9435 = FStar_Syntax_Unionfind.uvar_id u  in
              FStar_BigInt.of_int_fs uu____9435  in
            (uu____9434, t3)  in
          FStar_Reflection_Data.Tv_Uvar uu____9429  in
        FStar_All.pipe_left ret uu____9428
    | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),t21) ->
        if lb.FStar_Syntax_Syntax.lbunivs <> []
        then FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown
        else
          (match lb.FStar_Syntax_Syntax.lbname with
           | FStar_Util.Inr uu____9463 ->
               FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown
           | FStar_Util.Inl bv ->
               let b = FStar_Syntax_Syntax.mk_binder bv  in
               let uu____9468 = FStar_Syntax_Subst.open_term [b] t21  in
               (match uu____9468 with
                | (bs,t22) ->
                    let b1 =
                      match bs with
                      | b1::[] -> b1
                      | uu____9499 ->
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
           | FStar_Util.Inr uu____9531 ->
               FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown
           | FStar_Util.Inl bv ->
               let uu____9535 = FStar_Syntax_Subst.open_let_rec [lb] t21  in
               (match uu____9535 with
                | (lbs,t22) ->
                    (match lbs with
                     | lb1::[] ->
                         (match lb1.FStar_Syntax_Syntax.lbname with
                          | FStar_Util.Inr uu____9555 ->
                              ret FStar_Reflection_Data.Tv_Unknown
                          | FStar_Util.Inl bv1 ->
                              FStar_All.pipe_left ret
                                (FStar_Reflection_Data.Tv_Let
                                   (true, bv1,
                                     (lb1.FStar_Syntax_Syntax.lbdef), t22)))
                     | uu____9561 ->
                         failwith
                           "impossible: open_term returned different amount of binders")))
    | FStar_Syntax_Syntax.Tm_match (t3,brs) ->
        let rec inspect_pat p =
          match p.FStar_Syntax_Syntax.v with
          | FStar_Syntax_Syntax.Pat_constant c ->
              let uu____9615 = FStar_Reflection_Basic.inspect_const c  in
              FStar_Reflection_Data.Pat_Constant uu____9615
          | FStar_Syntax_Syntax.Pat_cons (fv,ps) ->
              let uu____9634 =
                let uu____9641 =
                  FStar_List.map
                    (fun uu____9653  ->
                       match uu____9653 with
                       | (p1,uu____9661) -> inspect_pat p1) ps
                   in
                (fv, uu____9641)  in
              FStar_Reflection_Data.Pat_Cons uu____9634
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
            (fun uu___63_9715  ->
               match uu___63_9715 with
               | (pat,uu____9737,t4) ->
                   let uu____9755 = inspect_pat pat  in (uu____9755, t4))
            brs1
           in
        FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_Match (t3, brs2))
    | FStar_Syntax_Syntax.Tm_unknown  ->
        FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown
    | uu____9772 ->
        let uu____9773 =
          let uu____9774 =
            let uu____9779 =
              let uu____9780 = FStar_Syntax_Print.tag_of_term t2  in
              let uu____9781 = FStar_Syntax_Print.term_to_string t2  in
              FStar_Util.format2
                "inspect: outside of expected syntax (%s, %s)\n" uu____9780
                uu____9781
               in
            (FStar_Errors.Warning_CantInspect, uu____9779)  in
          FStar_Errors.log_issue t2.FStar_Syntax_Syntax.pos uu____9774  in
        FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown
  
let (pack : FStar_Reflection_Data.term_view -> FStar_Syntax_Syntax.term tac)
  =
  fun tv  ->
    match tv with
    | FStar_Reflection_Data.Tv_Var bv ->
        let uu____9794 = FStar_Syntax_Syntax.bv_to_name bv  in
        FStar_All.pipe_left ret uu____9794
    | FStar_Reflection_Data.Tv_BVar bv ->
        let uu____9798 = FStar_Syntax_Syntax.bv_to_tm bv  in
        FStar_All.pipe_left ret uu____9798
    | FStar_Reflection_Data.Tv_FVar fv ->
        let uu____9802 = FStar_Syntax_Syntax.fv_to_tm fv  in
        FStar_All.pipe_left ret uu____9802
    | FStar_Reflection_Data.Tv_App (l,(r,q)) ->
        let q' = FStar_Reflection_Basic.pack_aqual q  in
        let uu____9813 = FStar_Syntax_Util.mk_app l [(r, q')]  in
        FStar_All.pipe_left ret uu____9813
    | FStar_Reflection_Data.Tv_Abs (b,t) ->
        let uu____9834 =
          FStar_Syntax_Util.abs [b] t FStar_Pervasives_Native.None  in
        FStar_All.pipe_left ret uu____9834
    | FStar_Reflection_Data.Tv_Arrow (b,c) ->
        let uu____9839 = FStar_Syntax_Util.arrow [b] c  in
        FStar_All.pipe_left ret uu____9839
    | FStar_Reflection_Data.Tv_Type () ->
        FStar_All.pipe_left ret FStar_Syntax_Util.ktype
    | FStar_Reflection_Data.Tv_Refine (bv,t) ->
        let uu____9860 = FStar_Syntax_Util.refine bv t  in
        FStar_All.pipe_left ret uu____9860
    | FStar_Reflection_Data.Tv_Const c ->
        let uu____9872 =
          let uu____9875 =
            let uu____9882 =
              let uu____9883 = FStar_Reflection_Basic.pack_const c  in
              FStar_Syntax_Syntax.Tm_constant uu____9883  in
            FStar_Syntax_Syntax.mk uu____9882  in
          uu____9875 FStar_Pervasives_Native.None FStar_Range.dummyRange  in
        FStar_All.pipe_left ret uu____9872
    | FStar_Reflection_Data.Tv_Uvar (u,t) ->
        let uu____9897 =
          let uu____9900 = FStar_BigInt.to_int_fs u  in
          FStar_Syntax_Util.uvar_from_id uu____9900 t  in
        FStar_All.pipe_left ret uu____9897
    | FStar_Reflection_Data.Tv_Let (false ,bv,t1,t2) ->
        let lb =
          FStar_Syntax_Util.mk_letbinding (FStar_Util.Inl bv) []
            bv.FStar_Syntax_Syntax.sort FStar_Parser_Const.effect_Tot_lid t1
            [] FStar_Range.dummyRange
           in
        let uu____9915 =
          let uu____9918 =
            let uu____9925 =
              let uu____9926 =
                let uu____9939 =
                  let uu____9940 =
                    let uu____9941 = FStar_Syntax_Syntax.mk_binder bv  in
                    [uu____9941]  in
                  FStar_Syntax_Subst.close uu____9940 t2  in
                ((false, [lb]), uu____9939)  in
              FStar_Syntax_Syntax.Tm_let uu____9926  in
            FStar_Syntax_Syntax.mk uu____9925  in
          uu____9918 FStar_Pervasives_Native.None FStar_Range.dummyRange  in
        FStar_All.pipe_left ret uu____9915
    | FStar_Reflection_Data.Tv_Let (true ,bv,t1,t2) ->
        let lb =
          FStar_Syntax_Util.mk_letbinding (FStar_Util.Inl bv) []
            bv.FStar_Syntax_Syntax.sort FStar_Parser_Const.effect_Tot_lid t1
            [] FStar_Range.dummyRange
           in
        let uu____9967 = FStar_Syntax_Subst.close_let_rec [lb] t2  in
        (match uu____9967 with
         | (lbs,body) ->
             let uu____9982 =
               FStar_Syntax_Syntax.mk
                 (FStar_Syntax_Syntax.Tm_let ((true, lbs), body))
                 FStar_Pervasives_Native.None FStar_Range.dummyRange
                in
             FStar_All.pipe_left ret uu____9982)
    | FStar_Reflection_Data.Tv_Match (t,brs) ->
        let wrap v1 =
          {
            FStar_Syntax_Syntax.v = v1;
            FStar_Syntax_Syntax.p = FStar_Range.dummyRange
          }  in
        let rec pack_pat p =
          match p with
          | FStar_Reflection_Data.Pat_Constant c ->
              let uu____10022 =
                let uu____10023 = FStar_Reflection_Basic.pack_const c  in
                FStar_Syntax_Syntax.Pat_constant uu____10023  in
              FStar_All.pipe_left wrap uu____10022
          | FStar_Reflection_Data.Pat_Cons (fv,ps) ->
              let uu____10032 =
                let uu____10033 =
                  let uu____10046 =
                    FStar_List.map
                      (fun p1  ->
                         let uu____10060 = pack_pat p1  in
                         (uu____10060, false)) ps
                     in
                  (fv, uu____10046)  in
                FStar_Syntax_Syntax.Pat_cons uu____10033  in
              FStar_All.pipe_left wrap uu____10032
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
            (fun uu___64_10110  ->
               match uu___64_10110 with
               | (pat,t1) ->
                   let uu____10127 = pack_pat pat  in
                   (uu____10127, FStar_Pervasives_Native.None, t1)) brs
           in
        let brs2 = FStar_List.map FStar_Syntax_Subst.close_branch brs1  in
        let uu____10137 =
          FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_match (t, brs2))
            FStar_Pervasives_Native.None FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____10137
    | FStar_Reflection_Data.Tv_AscribedT (e,t,tacopt) ->
        let uu____10157 =
          FStar_Syntax_Syntax.mk
            (FStar_Syntax_Syntax.Tm_ascribed
               (e, ((FStar_Util.Inl t), tacopt),
                 FStar_Pervasives_Native.None)) FStar_Pervasives_Native.None
            FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____10157
    | FStar_Reflection_Data.Tv_AscribedC (e,c,tacopt) ->
        let uu____10199 =
          FStar_Syntax_Syntax.mk
            (FStar_Syntax_Syntax.Tm_ascribed
               (e, ((FStar_Util.Inr c), tacopt),
                 FStar_Pervasives_Native.None)) FStar_Pervasives_Native.None
            FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____10199
    | FStar_Reflection_Data.Tv_Unknown  ->
        let uu____10234 =
          FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown
            FStar_Pervasives_Native.None FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____10234
  
let (goal_of_goal_ty :
  env ->
    FStar_Reflection_Data.typ ->
      (FStar_Tactics_Types.goal,FStar_TypeChecker_Env.guard_t)
        FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun typ  ->
      let uu____10263 =
        FStar_TypeChecker_Util.new_implicit_var "proofstate_of_goal_ty"
          typ.FStar_Syntax_Syntax.pos env typ
         in
      match uu____10263 with
      | (u,uu____10281,g_u) ->
          let g =
            let uu____10296 = FStar_Options.peek ()  in
            {
              FStar_Tactics_Types.context = env;
              FStar_Tactics_Types.witness = u;
              FStar_Tactics_Types.goal_ty = typ;
              FStar_Tactics_Types.opts = uu____10296;
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
      let uu____10311 = goal_of_goal_ty env typ  in
      match uu____10311 with
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
  