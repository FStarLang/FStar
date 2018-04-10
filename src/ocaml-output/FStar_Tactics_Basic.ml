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
        let uu____423 =
          FStar_TypeChecker_Env.dsenv g.FStar_Tactics_Types.context  in
        FStar_Syntax_Print.binders_to_json uu____423  in
      FStar_All.pipe_right uu____418 uu____419  in
    let uu____424 =
      let uu____431 =
        let uu____438 =
          let uu____443 =
            let uu____444 =
              let uu____451 =
                let uu____456 =
                  let uu____457 =
                    tts g.FStar_Tactics_Types.context
                      g.FStar_Tactics_Types.witness
                     in
                  FStar_Util.JsonStr uu____457  in
                ("witness", uu____456)  in
              let uu____458 =
                let uu____465 =
                  let uu____470 =
                    let uu____471 =
                      tts g.FStar_Tactics_Types.context
                        g.FStar_Tactics_Types.goal_ty
                       in
                    FStar_Util.JsonStr uu____471  in
                  ("type", uu____470)  in
                [uu____465]  in
              uu____451 :: uu____458  in
            FStar_Util.JsonAssoc uu____444  in
          ("goal", uu____443)  in
        [uu____438]  in
      ("hyps", g_binders) :: uu____431  in
    FStar_Util.JsonAssoc uu____424
  
let (ps_to_json :
  (Prims.string,FStar_Tactics_Types.proofstate)
    FStar_Pervasives_Native.tuple2 -> FStar_Util.json)
  =
  fun uu____504  ->
    match uu____504 with
    | (msg,ps) ->
        let uu____511 =
          let uu____518 =
            let uu____525 =
              let uu____532 =
                let uu____539 =
                  let uu____544 =
                    let uu____545 =
                      FStar_List.map goal_to_json
                        ps.FStar_Tactics_Types.goals
                       in
                    FStar_Util.JsonList uu____545  in
                  ("goals", uu____544)  in
                let uu____548 =
                  let uu____555 =
                    let uu____560 =
                      let uu____561 =
                        FStar_List.map goal_to_json
                          ps.FStar_Tactics_Types.smt_goals
                         in
                      FStar_Util.JsonList uu____561  in
                    ("smt-goals", uu____560)  in
                  [uu____555]  in
                uu____539 :: uu____548  in
              ("depth", (FStar_Util.JsonInt (ps.FStar_Tactics_Types.depth)))
                :: uu____532
               in
            ("label", (FStar_Util.JsonStr msg)) :: uu____525  in
          let uu____584 =
            if ps.FStar_Tactics_Types.entry_range <> FStar_Range.dummyRange
            then
              let uu____597 =
                let uu____602 =
                  FStar_Range.json_of_def_range
                    ps.FStar_Tactics_Types.entry_range
                   in
                ("location", uu____602)  in
              [uu____597]
            else []  in
          FStar_List.append uu____518 uu____584  in
        FStar_Util.JsonAssoc uu____511
  
let (dump_proofstate :
  FStar_Tactics_Types.proofstate -> Prims.string -> unit) =
  fun ps  ->
    fun msg  ->
      FStar_Options.with_saved_options
        (fun uu____632  ->
           let uu____633 =
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
         let uu____654 =
           let uu____655 = FStar_Tactics_Types.subst_proof_state subst1 ps
              in
           dump_cur uu____655 msg  in
         FStar_Tactics_Result.Success ((), ps))
  
let (print_proof_state : Prims.string -> unit tac) =
  fun msg  ->
    mk_tac
      (fun ps  ->
         let psc = ps.FStar_Tactics_Types.psc  in
         let subst1 = FStar_TypeChecker_Normalize.psc_subst psc  in
         let uu____672 =
           let uu____673 = FStar_Tactics_Types.subst_proof_state subst1 ps
              in
           dump_proofstate uu____673 msg  in
         FStar_Tactics_Result.Success ((), ps))
  
let (tac_verb_dbg : Prims.bool FStar_Pervasives_Native.option FStar_ST.ref) =
  FStar_Util.mk_ref FStar_Pervasives_Native.None 
let rec (log : FStar_Tactics_Types.proofstate -> (unit -> unit) -> unit) =
  fun ps  ->
    fun f  ->
      let uu____706 = FStar_ST.op_Bang tac_verb_dbg  in
      match uu____706 with
      | FStar_Pervasives_Native.None  ->
          let uu____736 =
            let uu____737 =
              let uu____740 =
                FStar_TypeChecker_Env.debug
                  ps.FStar_Tactics_Types.main_context
                  (FStar_Options.Other "TacVerbose")
                 in
              FStar_Pervasives_Native.Some uu____740  in
            FStar_ST.op_Colon_Equals tac_verb_dbg uu____737  in
          log ps f
      | FStar_Pervasives_Native.Some (true ) -> f ()
      | FStar_Pervasives_Native.Some (false ) -> ()
  
let mlog : 'a . (unit -> unit) -> (unit -> 'a tac) -> 'a tac =
  fun f  ->
    fun cont  -> bind get (fun ps  -> let uu____804 = log ps f  in cont ())
  
let fail : 'a . Prims.string -> 'a tac =
  fun msg  ->
    mk_tac
      (fun ps  ->
         let uu____820 =
           let uu____821 =
             FStar_TypeChecker_Env.debug ps.FStar_Tactics_Types.main_context
               (FStar_Options.Other "TacFail")
              in
           if uu____821
           then dump_proofstate ps (Prims.strcat "TACTIC FAILING: " msg)
           else ()  in
         FStar_Tactics_Result.Failed (msg, ps))
  
let fail1 : 'Auu____829 . Prims.string -> Prims.string -> 'Auu____829 tac =
  fun msg  ->
    fun x  -> let uu____842 = FStar_Util.format1 msg x  in fail uu____842
  
let fail2 :
  'Auu____851 .
    Prims.string -> Prims.string -> Prims.string -> 'Auu____851 tac
  =
  fun msg  ->
    fun x  ->
      fun y  -> let uu____869 = FStar_Util.format2 msg x y  in fail uu____869
  
let fail3 :
  'Auu____880 .
    Prims.string ->
      Prims.string -> Prims.string -> Prims.string -> 'Auu____880 tac
  =
  fun msg  ->
    fun x  ->
      fun y  ->
        fun z  ->
          let uu____903 = FStar_Util.format3 msg x y z  in fail uu____903
  
let fail4 :
  'Auu____916 .
    Prims.string ->
      Prims.string ->
        Prims.string -> Prims.string -> Prims.string -> 'Auu____916 tac
  =
  fun msg  ->
    fun x  ->
      fun y  ->
        fun z  ->
          fun w  ->
            let uu____944 = FStar_Util.format4 msg x y z w  in fail uu____944
  
let trytac' : 'a . 'a tac -> (Prims.string,'a) FStar_Util.either tac =
  fun t  ->
    mk_tac
      (fun ps  ->
         let tx = FStar_Syntax_Unionfind.new_transaction ()  in
         let uu____977 = run t ps  in
         match uu____977 with
         | FStar_Tactics_Result.Success (a,q) ->
             let uu____988 = FStar_Syntax_Unionfind.commit tx  in
             FStar_Tactics_Result.Success ((FStar_Util.Inr a), q)
         | FStar_Tactics_Result.Failed (m,q) ->
             let uu____999 = FStar_Syntax_Unionfind.rollback tx  in
             let ps1 =
               let uu___65_1001 = ps  in
               {
                 FStar_Tactics_Types.main_context =
                   (uu___65_1001.FStar_Tactics_Types.main_context);
                 FStar_Tactics_Types.main_goal =
                   (uu___65_1001.FStar_Tactics_Types.main_goal);
                 FStar_Tactics_Types.all_implicits =
                   (uu___65_1001.FStar_Tactics_Types.all_implicits);
                 FStar_Tactics_Types.goals =
                   (uu___65_1001.FStar_Tactics_Types.goals);
                 FStar_Tactics_Types.smt_goals =
                   (uu___65_1001.FStar_Tactics_Types.smt_goals);
                 FStar_Tactics_Types.depth =
                   (uu___65_1001.FStar_Tactics_Types.depth);
                 FStar_Tactics_Types.__dump =
                   (uu___65_1001.FStar_Tactics_Types.__dump);
                 FStar_Tactics_Types.psc =
                   (uu___65_1001.FStar_Tactics_Types.psc);
                 FStar_Tactics_Types.entry_range =
                   (uu___65_1001.FStar_Tactics_Types.entry_range);
                 FStar_Tactics_Types.guard_policy =
                   (uu___65_1001.FStar_Tactics_Types.guard_policy);
                 FStar_Tactics_Types.freshness =
                   (q.FStar_Tactics_Types.freshness)
               }  in
             FStar_Tactics_Result.Success ((FStar_Util.Inl m), ps1))
  
let trytac : 'a . 'a tac -> 'a FStar_Pervasives_Native.option tac =
  fun t  ->
    let uu____1028 = trytac' t  in
    bind uu____1028
      (fun r  ->
         match r with
         | FStar_Util.Inr v1 -> ret (FStar_Pervasives_Native.Some v1)
         | FStar_Util.Inl uu____1055 -> ret FStar_Pervasives_Native.None)
  
let trytac_exn : 'a . 'a tac -> 'a FStar_Pervasives_Native.option tac =
  fun t  ->
    mk_tac
      (fun ps  ->
         try let uu____1091 = trytac t  in run uu____1091 ps
         with
         | FStar_Errors.Err (uu____1107,msg) ->
             let uu____1109 =
               log ps
                 (fun uu____1111  ->
                    FStar_Util.print1 "trytac_exn error: (%s)" msg)
                in
             FStar_Tactics_Result.Success (FStar_Pervasives_Native.None, ps)
         | FStar_Errors.Error (uu____1116,msg,uu____1118) ->
             let uu____1119 =
               log ps
                 (fun uu____1121  ->
                    FStar_Util.print1 "trytac_exn error: (%s)" msg)
                in
             FStar_Tactics_Result.Success (FStar_Pervasives_Native.None, ps))
  
let wrap_err : 'a . Prims.string -> 'a tac -> 'a tac =
  fun pref  ->
    fun t  ->
      mk_tac
        (fun ps  ->
           let uu____1154 = run t ps  in
           match uu____1154 with
           | FStar_Tactics_Result.Success (a,q) ->
               FStar_Tactics_Result.Success (a, q)
           | FStar_Tactics_Result.Failed (msg,q) ->
               FStar_Tactics_Result.Failed
                 ((Prims.strcat pref (Prims.strcat ": " msg)), q))
  
let (set : FStar_Tactics_Types.proofstate -> unit tac) =
  fun p  -> mk_tac (fun uu____1173  -> FStar_Tactics_Result.Success ((), p)) 
let (__do_unify :
  env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.bool tac)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____1193 =
          let uu____1194 =
            FStar_TypeChecker_Env.debug env (FStar_Options.Other "1346")  in
          if uu____1194
          then
            let uu____1195 = FStar_Syntax_Print.term_to_string t1  in
            let uu____1196 = FStar_Syntax_Print.term_to_string t2  in
            FStar_Util.print2 "%%%%%%%%do_unify %s =? %s\n" uu____1195
              uu____1196
          else ()  in
        try
          let res = FStar_TypeChecker_Rel.teq_nosmt env t1 t2  in
          let uu____1207 =
            let uu____1208 =
              FStar_TypeChecker_Env.debug env (FStar_Options.Other "1346")
               in
            if uu____1208
            then
              let uu____1209 = FStar_Util.string_of_bool res  in
              let uu____1210 = FStar_Syntax_Print.term_to_string t1  in
              let uu____1211 = FStar_Syntax_Print.term_to_string t2  in
              FStar_Util.print3 "%%%%%%%%do_unify (RESULT %s) %s =? %s\n"
                uu____1209 uu____1210 uu____1211
            else ()  in
          ret res
        with
        | FStar_Errors.Err (uu____1219,msg) ->
            mlog
              (fun uu____1222  ->
                 FStar_Util.print1 ">> do_unify error, (%s)\n" msg)
              (fun uu____1224  -> ret false)
        | FStar_Errors.Error (uu____1225,msg,r) ->
            mlog
              (fun uu____1230  ->
                 let uu____1231 = FStar_Range.string_of_range r  in
                 FStar_Util.print2 ">> do_unify error, (%s) at (%s)\n" msg
                   uu____1231) (fun uu____1233  -> ret false)
  
let (do_unify :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.bool tac)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        bind idtac
          (fun uu____1256  ->
             let uu____1257 =
               let uu____1258 =
                 FStar_TypeChecker_Env.debug env (FStar_Options.Other "1346")
                  in
               if uu____1258
               then
                 let uu____1259 = FStar_Options.push ()  in
                 let uu____1260 =
                   FStar_Options.set_options FStar_Options.Set
                     "--debug_level Rel --debug_level RelCheck"
                    in
                 ()
               else ()  in
             let uu____1262 =
               let uu____1265 = __do_unify env t1 t2  in
               bind uu____1265
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
             bind uu____1262
               (fun r  ->
                  let uu____1280 =
                    let uu____1281 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "1346")
                       in
                    if uu____1281 then FStar_Options.pop () else ()  in
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
       let uu____1302 =
         let uu___70_1303 = p  in
         let uu____1304 = FStar_List.tl p.FStar_Tactics_Types.goals  in
         {
           FStar_Tactics_Types.main_context =
             (uu___70_1303.FStar_Tactics_Types.main_context);
           FStar_Tactics_Types.main_goal =
             (uu___70_1303.FStar_Tactics_Types.main_goal);
           FStar_Tactics_Types.all_implicits =
             (uu___70_1303.FStar_Tactics_Types.all_implicits);
           FStar_Tactics_Types.goals = uu____1304;
           FStar_Tactics_Types.smt_goals =
             (uu___70_1303.FStar_Tactics_Types.smt_goals);
           FStar_Tactics_Types.depth =
             (uu___70_1303.FStar_Tactics_Types.depth);
           FStar_Tactics_Types.__dump =
             (uu___70_1303.FStar_Tactics_Types.__dump);
           FStar_Tactics_Types.psc = (uu___70_1303.FStar_Tactics_Types.psc);
           FStar_Tactics_Types.entry_range =
             (uu___70_1303.FStar_Tactics_Types.entry_range);
           FStar_Tactics_Types.guard_policy =
             (uu___70_1303.FStar_Tactics_Types.guard_policy);
           FStar_Tactics_Types.freshness =
             (uu___70_1303.FStar_Tactics_Types.freshness)
         }  in
       set uu____1302)
  
let (dismiss : unit -> unit tac) =
  fun uu____1313  ->
    bind get
      (fun p  ->
         match p.FStar_Tactics_Types.goals with
         | [] -> fail "dismiss: no more goals"
         | uu____1320 -> __dismiss)
  
let (solve :
  FStar_Tactics_Types.goal -> FStar_Syntax_Syntax.term -> unit tac) =
  fun goal  ->
    fun solution  ->
      let uu____1337 = trysolve goal solution  in
      bind uu____1337
        (fun b  ->
           if b
           then __dismiss
           else
             (let uu____1345 =
                let uu____1346 =
                  tts goal.FStar_Tactics_Types.context solution  in
                let uu____1347 =
                  tts goal.FStar_Tactics_Types.context
                    goal.FStar_Tactics_Types.witness
                   in
                let uu____1348 =
                  tts goal.FStar_Tactics_Types.context
                    goal.FStar_Tactics_Types.goal_ty
                   in
                FStar_Util.format3 "%s does not solve %s : %s" uu____1346
                  uu____1347 uu____1348
                 in
              fail uu____1345))
  
let (dismiss_all : unit tac) =
  bind get
    (fun p  ->
       set
         (let uu___71_1355 = p  in
          {
            FStar_Tactics_Types.main_context =
              (uu___71_1355.FStar_Tactics_Types.main_context);
            FStar_Tactics_Types.main_goal =
              (uu___71_1355.FStar_Tactics_Types.main_goal);
            FStar_Tactics_Types.all_implicits =
              (uu___71_1355.FStar_Tactics_Types.all_implicits);
            FStar_Tactics_Types.goals = [];
            FStar_Tactics_Types.smt_goals =
              (uu___71_1355.FStar_Tactics_Types.smt_goals);
            FStar_Tactics_Types.depth =
              (uu___71_1355.FStar_Tactics_Types.depth);
            FStar_Tactics_Types.__dump =
              (uu___71_1355.FStar_Tactics_Types.__dump);
            FStar_Tactics_Types.psc = (uu___71_1355.FStar_Tactics_Types.psc);
            FStar_Tactics_Types.entry_range =
              (uu___71_1355.FStar_Tactics_Types.entry_range);
            FStar_Tactics_Types.guard_policy =
              (uu___71_1355.FStar_Tactics_Types.guard_policy);
            FStar_Tactics_Types.freshness =
              (uu___71_1355.FStar_Tactics_Types.freshness)
          }))
  
let (nwarn : Prims.int FStar_ST.ref) =
  FStar_Util.mk_ref (Prims.parse_int "0") 
let (check_valid_goal : FStar_Tactics_Types.goal -> unit) =
  fun g  ->
    let uu____1374 = FStar_Options.defensive ()  in
    if uu____1374
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
        let uu____1388 = FStar_TypeChecker_Env.pop_bv e  in
        match uu____1388 with
        | FStar_Pervasives_Native.None  -> b3
        | FStar_Pervasives_Native.Some (bv,e1) ->
            let b4 =
              b3 &&
                (FStar_TypeChecker_Env.closed e1 bv.FStar_Syntax_Syntax.sort)
               in
            aux b4 e1
         in
      let uu____1406 =
        (let uu____1409 = aux b2 env  in Prims.op_Negation uu____1409) &&
          (let uu____1411 = FStar_ST.op_Bang nwarn  in
           uu____1411 < (Prims.parse_int "5"))
         in
      (if uu____1406
       then
         let uu____1435 =
           let uu____1436 =
             let uu____1441 =
               let uu____1442 = goal_to_string g  in
               FStar_Util.format1
                 "The following goal is ill-formed. Keeping calm and carrying on...\n<%s>\n\n"
                 uu____1442
                in
             (FStar_Errors.Warning_IllFormedGoal, uu____1441)  in
           FStar_Errors.log_issue
             (g.FStar_Tactics_Types.goal_ty).FStar_Syntax_Syntax.pos
             uu____1436
            in
         let uu____1443 =
           let uu____1444 = FStar_ST.op_Bang nwarn  in
           uu____1444 + (Prims.parse_int "1")  in
         FStar_ST.op_Colon_Equals nwarn uu____1443
       else ())
    else ()
  
let (add_goals : FStar_Tactics_Types.goal Prims.list -> unit tac) =
  fun gs  ->
    bind get
      (fun p  ->
         let uu____1509 = FStar_List.iter check_valid_goal gs  in
         set
           (let uu___72_1512 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___72_1512.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___72_1512.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___72_1512.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (FStar_List.append gs p.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (uu___72_1512.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___72_1512.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___72_1512.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___72_1512.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___72_1512.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___72_1512.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___72_1512.FStar_Tactics_Types.freshness)
            }))
  
let (add_smt_goals : FStar_Tactics_Types.goal Prims.list -> unit tac) =
  fun gs  ->
    bind get
      (fun p  ->
         let uu____1529 = FStar_List.iter check_valid_goal gs  in
         set
           (let uu___73_1532 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___73_1532.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___73_1532.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___73_1532.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___73_1532.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (FStar_List.append gs p.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___73_1532.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___73_1532.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___73_1532.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___73_1532.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___73_1532.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___73_1532.FStar_Tactics_Types.freshness)
            }))
  
let (push_goals : FStar_Tactics_Types.goal Prims.list -> unit tac) =
  fun gs  ->
    bind get
      (fun p  ->
         let uu____1549 = FStar_List.iter check_valid_goal gs  in
         set
           (let uu___74_1552 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___74_1552.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___74_1552.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___74_1552.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (FStar_List.append p.FStar_Tactics_Types.goals gs);
              FStar_Tactics_Types.smt_goals =
                (uu___74_1552.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___74_1552.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___74_1552.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___74_1552.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___74_1552.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___74_1552.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___74_1552.FStar_Tactics_Types.freshness)
            }))
  
let (push_smt_goals : FStar_Tactics_Types.goal Prims.list -> unit tac) =
  fun gs  ->
    bind get
      (fun p  ->
         let uu____1569 = FStar_List.iter check_valid_goal gs  in
         set
           (let uu___75_1572 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___75_1572.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___75_1572.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___75_1572.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___75_1572.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (FStar_List.append p.FStar_Tactics_Types.smt_goals gs);
              FStar_Tactics_Types.depth =
                (uu___75_1572.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___75_1572.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___75_1572.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___75_1572.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___75_1572.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___75_1572.FStar_Tactics_Types.freshness)
            }))
  
let (replace_cur : FStar_Tactics_Types.goal -> unit tac) =
  fun g  -> bind __dismiss (fun uu____1583  -> add_goals [g]) 
let (add_implicits : implicits -> unit tac) =
  fun i  ->
    bind get
      (fun p  ->
         set
           (let uu___76_1597 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___76_1597.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___76_1597.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (FStar_List.append i p.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___76_1597.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (uu___76_1597.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___76_1597.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___76_1597.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___76_1597.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___76_1597.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___76_1597.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___76_1597.FStar_Tactics_Types.freshness)
            }))
  
let (new_uvar :
  Prims.string ->
    env -> FStar_Reflection_Data.typ -> FStar_Syntax_Syntax.term tac)
  =
  fun reason  ->
    fun env  ->
      fun typ  ->
        let uu____1629 =
          FStar_TypeChecker_Util.new_implicit_var reason
            typ.FStar_Syntax_Syntax.pos env typ
           in
        match uu____1629 with
        | (u,uu____1645,g_u) ->
            let uu____1659 =
              add_implicits g_u.FStar_TypeChecker_Env.implicits  in
            bind uu____1659 (fun uu____1663  -> ret u)
  
let (is_true : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____1669 = FStar_Syntax_Util.un_squash t  in
    match uu____1669 with
    | FStar_Pervasives_Native.Some t' ->
        let uu____1679 =
          let uu____1680 = FStar_Syntax_Subst.compress t'  in
          uu____1680.FStar_Syntax_Syntax.n  in
        (match uu____1679 with
         | FStar_Syntax_Syntax.Tm_fvar fv ->
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.true_lid
         | uu____1684 -> false)
    | uu____1685 -> false
  
let (is_false : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____1695 = FStar_Syntax_Util.un_squash t  in
    match uu____1695 with
    | FStar_Pervasives_Native.Some t' ->
        let uu____1705 =
          let uu____1706 = FStar_Syntax_Subst.compress t'  in
          uu____1706.FStar_Syntax_Syntax.n  in
        (match uu____1705 with
         | FStar_Syntax_Syntax.Tm_fvar fv ->
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.false_lid
         | uu____1710 -> false)
    | uu____1711 -> false
  
let (cur_goal : unit -> FStar_Tactics_Types.goal tac) =
  fun uu____1722  ->
    bind get
      (fun p  ->
         match p.FStar_Tactics_Types.goals with
         | [] -> fail "No more goals (1)"
         | hd1::tl1 -> ret hd1)
  
let (tadmit : unit -> unit tac) =
  fun uu____1739  ->
    let uu____1742 =
      let uu____1745 = cur_goal ()  in
      bind uu____1745
        (fun g  ->
           let uu____1751 =
             let uu____1752 =
               let uu____1757 =
                 let uu____1758 = goal_to_string g  in
                 FStar_Util.format1 "Tactics admitted goal <%s>\n\n"
                   uu____1758
                  in
               (FStar_Errors.Warning_TacAdmit, uu____1757)  in
             FStar_Errors.log_issue
               (g.FStar_Tactics_Types.goal_ty).FStar_Syntax_Syntax.pos
               uu____1752
              in
           solve g FStar_Syntax_Util.exp_unit)
       in
    FStar_All.pipe_left (wrap_err "tadmit") uu____1742
  
let (fresh : unit -> FStar_BigInt.t tac) =
  fun uu____1769  ->
    bind get
      (fun ps  ->
         let n1 = ps.FStar_Tactics_Types.freshness  in
         let ps1 =
           let uu___77_1779 = ps  in
           {
             FStar_Tactics_Types.main_context =
               (uu___77_1779.FStar_Tactics_Types.main_context);
             FStar_Tactics_Types.main_goal =
               (uu___77_1779.FStar_Tactics_Types.main_goal);
             FStar_Tactics_Types.all_implicits =
               (uu___77_1779.FStar_Tactics_Types.all_implicits);
             FStar_Tactics_Types.goals =
               (uu___77_1779.FStar_Tactics_Types.goals);
             FStar_Tactics_Types.smt_goals =
               (uu___77_1779.FStar_Tactics_Types.smt_goals);
             FStar_Tactics_Types.depth =
               (uu___77_1779.FStar_Tactics_Types.depth);
             FStar_Tactics_Types.__dump =
               (uu___77_1779.FStar_Tactics_Types.__dump);
             FStar_Tactics_Types.psc = (uu___77_1779.FStar_Tactics_Types.psc);
             FStar_Tactics_Types.entry_range =
               (uu___77_1779.FStar_Tactics_Types.entry_range);
             FStar_Tactics_Types.guard_policy =
               (uu___77_1779.FStar_Tactics_Types.guard_policy);
             FStar_Tactics_Types.freshness = (n1 + (Prims.parse_int "1"))
           }  in
         let uu____1780 = set ps1  in
         bind uu____1780
           (fun uu____1785  ->
              let uu____1786 = FStar_BigInt.of_int_fs n1  in ret uu____1786))
  
let (ngoals : unit -> FStar_BigInt.t tac) =
  fun uu____1793  ->
    bind get
      (fun ps  ->
         let n1 = FStar_List.length ps.FStar_Tactics_Types.goals  in
         let uu____1801 = FStar_BigInt.of_int_fs n1  in ret uu____1801)
  
let (ngoals_smt : unit -> FStar_BigInt.t tac) =
  fun uu____1814  ->
    bind get
      (fun ps  ->
         let n1 = FStar_List.length ps.FStar_Tactics_Types.smt_goals  in
         let uu____1822 = FStar_BigInt.of_int_fs n1  in ret uu____1822)
  
let (is_guard : unit -> Prims.bool tac) =
  fun uu____1835  ->
    let uu____1838 = cur_goal ()  in
    bind uu____1838 (fun g  -> ret g.FStar_Tactics_Types.is_guard)
  
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
            let uu____1870 = env.FStar_TypeChecker_Env.universe_of env phi
               in
            FStar_Syntax_Util.mk_squash uu____1870 phi  in
          let uu____1871 = new_uvar reason env typ  in
          bind uu____1871
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
             (fun uu____1920  ->
                let uu____1921 = tts e t  in
                FStar_Util.print1 "Tac> __tc(%s)\n" uu____1921)
             (fun uu____1923  ->
                try
                  let uu____1943 =
                    (ps.FStar_Tactics_Types.main_context).FStar_TypeChecker_Env.type_of
                      e t
                     in
                  ret uu____1943
                with
                | FStar_Errors.Err (uu____1970,msg) ->
                    let uu____1972 = tts e t  in
                    let uu____1973 =
                      let uu____1974 = FStar_TypeChecker_Env.all_binders e
                         in
                      FStar_All.pipe_right uu____1974
                        (FStar_Syntax_Print.binders_to_string ", ")
                       in
                    fail3 "Cannot type %s in context (%s). Error = (%s)"
                      uu____1972 uu____1973 msg
                | FStar_Errors.Error (uu____1981,msg,uu____1983) ->
                    let uu____1984 = tts e t  in
                    let uu____1985 =
                      let uu____1986 = FStar_TypeChecker_Env.all_binders e
                         in
                      FStar_All.pipe_right uu____1986
                        (FStar_Syntax_Print.binders_to_string ", ")
                       in
                    fail3 "Cannot type %s in context (%s). Error = (%s)"
                      uu____1984 uu____1985 msg))
  
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
  fun uu____2013  ->
    bind get (fun ps  -> ret ps.FStar_Tactics_Types.guard_policy)
  
let (set_guard_policy : FStar_Tactics_Types.guard_policy -> unit tac) =
  fun pol  ->
    bind get
      (fun ps  ->
         set
           (let uu___80_2031 = ps  in
            {
              FStar_Tactics_Types.main_context =
                (uu___80_2031.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___80_2031.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___80_2031.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___80_2031.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (uu___80_2031.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___80_2031.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___80_2031.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___80_2031.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___80_2031.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy = pol;
              FStar_Tactics_Types.freshness =
                (uu___80_2031.FStar_Tactics_Types.freshness)
            }))
  
let with_policy : 'a . FStar_Tactics_Types.guard_policy -> 'a tac -> 'a tac =
  fun pol  ->
    fun t  ->
      let uu____2055 = get_guard_policy ()  in
      bind uu____2055
        (fun old_pol  ->
           let uu____2061 = set_guard_policy pol  in
           bind uu____2061
             (fun uu____2065  ->
                bind t
                  (fun r  ->
                     let uu____2069 = set_guard_policy old_pol  in
                     bind uu____2069 (fun uu____2073  -> ret r))))
  
let (proc_guard :
  Prims.string ->
    env ->
      FStar_TypeChecker_Env.guard_t -> FStar_Options.optionstate -> unit tac)
  =
  fun reason  ->
    fun e  ->
      fun g  ->
        fun opts  ->
          let uu____2098 =
            let uu____2099 = FStar_TypeChecker_Rel.simplify_guard e g  in
            uu____2099.FStar_TypeChecker_Env.guard_f  in
          match uu____2098 with
          | FStar_TypeChecker_Common.Trivial  -> ret ()
          | FStar_TypeChecker_Common.NonTrivial f ->
              let uu____2103 = istrivial e f  in
              if uu____2103
              then ret ()
              else
                bind get
                  (fun ps  ->
                     match ps.FStar_Tactics_Types.guard_policy with
                     | FStar_Tactics_Types.Drop  -> ret ()
                     | FStar_Tactics_Types.Goal  ->
                         let uu____2111 = mk_irrelevant_goal reason e f opts
                            in
                         bind uu____2111
                           (fun goal  ->
                              let goal1 =
                                let uu___81_2118 = goal  in
                                {
                                  FStar_Tactics_Types.context =
                                    (uu___81_2118.FStar_Tactics_Types.context);
                                  FStar_Tactics_Types.witness =
                                    (uu___81_2118.FStar_Tactics_Types.witness);
                                  FStar_Tactics_Types.goal_ty =
                                    (uu___81_2118.FStar_Tactics_Types.goal_ty);
                                  FStar_Tactics_Types.opts =
                                    (uu___81_2118.FStar_Tactics_Types.opts);
                                  FStar_Tactics_Types.is_guard = true
                                }  in
                              push_goals [goal1])
                     | FStar_Tactics_Types.SMT  ->
                         let uu____2119 = mk_irrelevant_goal reason e f opts
                            in
                         bind uu____2119
                           (fun goal  ->
                              let goal1 =
                                let uu___82_2126 = goal  in
                                {
                                  FStar_Tactics_Types.context =
                                    (uu___82_2126.FStar_Tactics_Types.context);
                                  FStar_Tactics_Types.witness =
                                    (uu___82_2126.FStar_Tactics_Types.witness);
                                  FStar_Tactics_Types.goal_ty =
                                    (uu___82_2126.FStar_Tactics_Types.goal_ty);
                                  FStar_Tactics_Types.opts =
                                    (uu___82_2126.FStar_Tactics_Types.opts);
                                  FStar_Tactics_Types.is_guard = true
                                }  in
                              push_smt_goals [goal1])
                     | FStar_Tactics_Types.Force  ->
                         (try
                            let uu____2134 =
                              let uu____2135 =
                                let uu____2136 =
                                  FStar_TypeChecker_Rel.discharge_guard_no_smt
                                    e g
                                   in
                                FStar_All.pipe_left
                                  FStar_TypeChecker_Rel.is_trivial uu____2136
                                 in
                              Prims.op_Negation uu____2135  in
                            if uu____2134
                            then
                              mlog
                                (fun uu____2141  ->
                                   let uu____2142 =
                                     FStar_TypeChecker_Rel.guard_to_string e
                                       g
                                      in
                                   FStar_Util.print1 "guard = %s\n"
                                     uu____2142)
                                (fun uu____2144  ->
                                   fail1 "Forcing the guard failed %s)"
                                     reason)
                            else ret ()
                          with
                          | uu____2151 ->
                              mlog
                                (fun uu____2154  ->
                                   let uu____2155 =
                                     FStar_TypeChecker_Rel.guard_to_string e
                                       g
                                      in
                                   FStar_Util.print1 "guard = %s\n"
                                     uu____2155)
                                (fun uu____2157  ->
                                   fail1 "Forcing the guard failed (%s)"
                                     reason)))
  
let (tc : FStar_Syntax_Syntax.term -> FStar_Reflection_Data.typ tac) =
  fun t  ->
    let uu____2167 =
      let uu____2170 = cur_goal ()  in
      bind uu____2170
        (fun goal  ->
           let uu____2176 = __tc goal.FStar_Tactics_Types.context t  in
           bind uu____2176
             (fun uu____2196  ->
                match uu____2196 with
                | (t1,typ,guard) ->
                    let uu____2208 =
                      proc_guard "tc" goal.FStar_Tactics_Types.context guard
                        goal.FStar_Tactics_Types.opts
                       in
                    bind uu____2208 (fun uu____2212  -> ret typ)))
       in
    FStar_All.pipe_left (wrap_err "tc") uu____2167
  
let (add_irrelevant_goal :
  Prims.string ->
    env -> FStar_Reflection_Data.typ -> FStar_Options.optionstate -> unit tac)
  =
  fun reason  ->
    fun env  ->
      fun phi  ->
        fun opts  ->
          let uu____2241 = mk_irrelevant_goal reason env phi opts  in
          bind uu____2241 (fun goal  -> add_goals [goal])
  
let (trivial : unit -> unit tac) =
  fun uu____2252  ->
    let uu____2255 = cur_goal ()  in
    bind uu____2255
      (fun goal  ->
         let uu____2261 =
           istrivial goal.FStar_Tactics_Types.context
             goal.FStar_Tactics_Types.goal_ty
            in
         if uu____2261
         then solve goal FStar_Syntax_Util.exp_unit
         else
           (let uu____2265 =
              tts goal.FStar_Tactics_Types.context
                goal.FStar_Tactics_Types.goal_ty
               in
            fail1 "Not a trivial goal: %s" uu____2265))
  
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
          let uu____2294 =
            let uu____2295 = FStar_TypeChecker_Rel.simplify_guard e g  in
            uu____2295.FStar_TypeChecker_Env.guard_f  in
          match uu____2294 with
          | FStar_TypeChecker_Common.Trivial  ->
              ret FStar_Pervasives_Native.None
          | FStar_TypeChecker_Common.NonTrivial f ->
              let uu____2303 = istrivial e f  in
              if uu____2303
              then ret FStar_Pervasives_Native.None
              else
                (let uu____2311 = mk_irrelevant_goal reason e f opts  in
                 bind uu____2311
                   (fun goal  ->
                      ret
                        (FStar_Pervasives_Native.Some
                           (let uu___85_2321 = goal  in
                            {
                              FStar_Tactics_Types.context =
                                (uu___85_2321.FStar_Tactics_Types.context);
                              FStar_Tactics_Types.witness =
                                (uu___85_2321.FStar_Tactics_Types.witness);
                              FStar_Tactics_Types.goal_ty =
                                (uu___85_2321.FStar_Tactics_Types.goal_ty);
                              FStar_Tactics_Types.opts =
                                (uu___85_2321.FStar_Tactics_Types.opts);
                              FStar_Tactics_Types.is_guard = true
                            }))))
  
let (smt : unit -> unit tac) =
  fun uu____2328  ->
    let uu____2331 = cur_goal ()  in
    bind uu____2331
      (fun g  ->
         let uu____2337 = is_irrelevant g  in
         if uu____2337
         then bind __dismiss (fun uu____2341  -> add_smt_goals [g])
         else
           (let uu____2343 =
              tts g.FStar_Tactics_Types.context g.FStar_Tactics_Types.goal_ty
               in
            fail1 "goal is not irrelevant: cannot dispatch to smt (%s)"
              uu____2343))
  
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
             let uu____2392 =
               try
                 let uu____2426 =
                   let uu____2435 = FStar_BigInt.to_int_fs n1  in
                   FStar_List.splitAt uu____2435 p.FStar_Tactics_Types.goals
                    in
                 ret uu____2426
               with | uu____2457 -> fail "divide: not enough goals"  in
             bind uu____2392
               (fun uu____2484  ->
                  match uu____2484 with
                  | (lgs,rgs) ->
                      let lp =
                        let uu___86_2510 = p  in
                        {
                          FStar_Tactics_Types.main_context =
                            (uu___86_2510.FStar_Tactics_Types.main_context);
                          FStar_Tactics_Types.main_goal =
                            (uu___86_2510.FStar_Tactics_Types.main_goal);
                          FStar_Tactics_Types.all_implicits =
                            (uu___86_2510.FStar_Tactics_Types.all_implicits);
                          FStar_Tactics_Types.goals = lgs;
                          FStar_Tactics_Types.smt_goals = [];
                          FStar_Tactics_Types.depth =
                            (uu___86_2510.FStar_Tactics_Types.depth);
                          FStar_Tactics_Types.__dump =
                            (uu___86_2510.FStar_Tactics_Types.__dump);
                          FStar_Tactics_Types.psc =
                            (uu___86_2510.FStar_Tactics_Types.psc);
                          FStar_Tactics_Types.entry_range =
                            (uu___86_2510.FStar_Tactics_Types.entry_range);
                          FStar_Tactics_Types.guard_policy =
                            (uu___86_2510.FStar_Tactics_Types.guard_policy);
                          FStar_Tactics_Types.freshness =
                            (uu___86_2510.FStar_Tactics_Types.freshness)
                        }  in
                      let rp =
                        let uu___87_2512 = p  in
                        {
                          FStar_Tactics_Types.main_context =
                            (uu___87_2512.FStar_Tactics_Types.main_context);
                          FStar_Tactics_Types.main_goal =
                            (uu___87_2512.FStar_Tactics_Types.main_goal);
                          FStar_Tactics_Types.all_implicits =
                            (uu___87_2512.FStar_Tactics_Types.all_implicits);
                          FStar_Tactics_Types.goals = rgs;
                          FStar_Tactics_Types.smt_goals = [];
                          FStar_Tactics_Types.depth =
                            (uu___87_2512.FStar_Tactics_Types.depth);
                          FStar_Tactics_Types.__dump =
                            (uu___87_2512.FStar_Tactics_Types.__dump);
                          FStar_Tactics_Types.psc =
                            (uu___87_2512.FStar_Tactics_Types.psc);
                          FStar_Tactics_Types.entry_range =
                            (uu___87_2512.FStar_Tactics_Types.entry_range);
                          FStar_Tactics_Types.guard_policy =
                            (uu___87_2512.FStar_Tactics_Types.guard_policy);
                          FStar_Tactics_Types.freshness =
                            (uu___87_2512.FStar_Tactics_Types.freshness)
                        }  in
                      let uu____2513 = set lp  in
                      bind uu____2513
                        (fun uu____2521  ->
                           bind l
                             (fun a  ->
                                bind get
                                  (fun lp'  ->
                                     let uu____2535 = set rp  in
                                     bind uu____2535
                                       (fun uu____2543  ->
                                          bind r
                                            (fun b  ->
                                               bind get
                                                 (fun rp'  ->
                                                    let p' =
                                                      let uu___88_2559 = p
                                                         in
                                                      {
                                                        FStar_Tactics_Types.main_context
                                                          =
                                                          (uu___88_2559.FStar_Tactics_Types.main_context);
                                                        FStar_Tactics_Types.main_goal
                                                          =
                                                          (uu___88_2559.FStar_Tactics_Types.main_goal);
                                                        FStar_Tactics_Types.all_implicits
                                                          =
                                                          (uu___88_2559.FStar_Tactics_Types.all_implicits);
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
                                                          (uu___88_2559.FStar_Tactics_Types.depth);
                                                        FStar_Tactics_Types.__dump
                                                          =
                                                          (uu___88_2559.FStar_Tactics_Types.__dump);
                                                        FStar_Tactics_Types.psc
                                                          =
                                                          (uu___88_2559.FStar_Tactics_Types.psc);
                                                        FStar_Tactics_Types.entry_range
                                                          =
                                                          (uu___88_2559.FStar_Tactics_Types.entry_range);
                                                        FStar_Tactics_Types.guard_policy
                                                          =
                                                          (uu___88_2559.FStar_Tactics_Types.guard_policy);
                                                        FStar_Tactics_Types.freshness
                                                          =
                                                          (uu___88_2559.FStar_Tactics_Types.freshness)
                                                      }  in
                                                    let uu____2560 = set p'
                                                       in
                                                    bind uu____2560
                                                      (fun uu____2568  ->
                                                         ret (a, b))))))))))
  
let focus : 'a . 'a tac -> 'a tac =
  fun f  ->
    let uu____2589 = divide FStar_BigInt.one f idtac  in
    bind uu____2589
      (fun uu____2602  -> match uu____2602 with | (a,()) -> ret a)
  
let rec map : 'a . 'a tac -> 'a Prims.list tac =
  fun tau  ->
    bind get
      (fun p  ->
         match p.FStar_Tactics_Types.goals with
         | [] -> ret []
         | uu____2639::uu____2640 ->
             let uu____2643 =
               let uu____2652 = map tau  in
               divide FStar_BigInt.one tau uu____2652  in
             bind uu____2643
               (fun uu____2670  ->
                  match uu____2670 with | (h,t) -> ret (h :: t)))
  
let (seq : unit tac -> unit tac -> unit tac) =
  fun t1  ->
    fun t2  ->
      let uu____2711 =
        bind t1
          (fun uu____2716  ->
             let uu____2717 = map t2  in
             bind uu____2717 (fun uu____2725  -> ret ()))
         in
      focus uu____2711
  
let (intro : unit -> FStar_Syntax_Syntax.binder tac) =
  fun uu____2734  ->
    let uu____2737 =
      let uu____2740 = cur_goal ()  in
      bind uu____2740
        (fun goal  ->
           let uu____2749 =
             FStar_Syntax_Util.arrow_one goal.FStar_Tactics_Types.goal_ty  in
           match uu____2749 with
           | FStar_Pervasives_Native.Some (b,c) ->
               let uu____2764 =
                 let uu____2765 = FStar_Syntax_Util.is_total_comp c  in
                 Prims.op_Negation uu____2765  in
               if uu____2764
               then fail "Codomain is effectful"
               else
                 (let env' =
                    FStar_TypeChecker_Env.push_binders
                      goal.FStar_Tactics_Types.context [b]
                     in
                  let typ' = comp_to_typ c  in
                  let uu____2771 = new_uvar "intro" env' typ'  in
                  bind uu____2771
                    (fun u  ->
                       let uu____2777 =
                         let uu____2780 =
                           FStar_Syntax_Util.abs [b] u
                             FStar_Pervasives_Native.None
                            in
                         trysolve goal uu____2780  in
                       bind uu____2777
                         (fun bb  ->
                            if bb
                            then
                              let uu____2786 =
                                let uu____2789 =
                                  let uu___91_2790 = goal  in
                                  let uu____2791 = bnorm env' u  in
                                  let uu____2792 = bnorm env' typ'  in
                                  {
                                    FStar_Tactics_Types.context = env';
                                    FStar_Tactics_Types.witness = uu____2791;
                                    FStar_Tactics_Types.goal_ty = uu____2792;
                                    FStar_Tactics_Types.opts =
                                      (uu___91_2790.FStar_Tactics_Types.opts);
                                    FStar_Tactics_Types.is_guard =
                                      (uu___91_2790.FStar_Tactics_Types.is_guard)
                                  }  in
                                replace_cur uu____2789  in
                              bind uu____2786 (fun uu____2794  -> ret b)
                            else fail "unification failed")))
           | FStar_Pervasives_Native.None  ->
               let uu____2800 =
                 tts goal.FStar_Tactics_Types.context
                   goal.FStar_Tactics_Types.goal_ty
                  in
               fail1 "goal is not an arrow (%s)" uu____2800)
       in
    FStar_All.pipe_left (wrap_err "intro") uu____2737
  
let (intro_rec :
  unit ->
    (FStar_Syntax_Syntax.binder,FStar_Syntax_Syntax.binder)
      FStar_Pervasives_Native.tuple2 tac)
  =
  fun uu____2815  ->
    let uu____2822 = cur_goal ()  in
    bind uu____2822
      (fun goal  ->
         let uu____2837 =
           FStar_Util.print_string
             "WARNING (intro_rec): calling this is known to cause normalizer loops\n"
            in
         let uu____2838 =
           FStar_Util.print_string
             "WARNING (intro_rec): proceed at your own risk...\n"
            in
         let uu____2839 =
           FStar_Syntax_Util.arrow_one goal.FStar_Tactics_Types.goal_ty  in
         match uu____2839 with
         | FStar_Pervasives_Native.Some (b,c) ->
             let uu____2858 =
               let uu____2859 = FStar_Syntax_Util.is_total_comp c  in
               Prims.op_Negation uu____2859  in
             if uu____2858
             then fail "Codomain is effectful"
             else
               (let bv =
                  FStar_Syntax_Syntax.gen_bv "__recf"
                    FStar_Pervasives_Native.None
                    goal.FStar_Tactics_Types.goal_ty
                   in
                let bs =
                  let uu____2875 = FStar_Syntax_Syntax.mk_binder bv  in
                  [uu____2875; b]  in
                let env' =
                  FStar_TypeChecker_Env.push_binders
                    goal.FStar_Tactics_Types.context bs
                   in
                let uu____2877 =
                  let uu____2880 = comp_to_typ c  in
                  new_uvar "intro_rec" env' uu____2880  in
                bind uu____2877
                  (fun u  ->
                     let lb =
                       let uu____2895 =
                         FStar_Syntax_Util.abs [b] u
                           FStar_Pervasives_Native.None
                          in
                       FStar_Syntax_Util.mk_letbinding (FStar_Util.Inl bv) []
                         goal.FStar_Tactics_Types.goal_ty
                         FStar_Parser_Const.effect_Tot_lid uu____2895 []
                         FStar_Range.dummyRange
                        in
                     let body = FStar_Syntax_Syntax.bv_to_name bv  in
                     let uu____2901 =
                       FStar_Syntax_Subst.close_let_rec [lb] body  in
                     match uu____2901 with
                     | (lbs,body1) ->
                         let tm =
                           FStar_Syntax_Syntax.mk
                             (FStar_Syntax_Syntax.Tm_let ((true, lbs), body1))
                             FStar_Pervasives_Native.None
                             (goal.FStar_Tactics_Types.witness).FStar_Syntax_Syntax.pos
                            in
                         let uu____2931 = trysolve goal tm  in
                         bind uu____2931
                           (fun bb  ->
                              if bb
                              then
                                let uu____2947 =
                                  let uu____2950 =
                                    let uu___92_2951 = goal  in
                                    let uu____2952 = bnorm env' u  in
                                    let uu____2953 =
                                      let uu____2954 = comp_to_typ c  in
                                      bnorm env' uu____2954  in
                                    {
                                      FStar_Tactics_Types.context = env';
                                      FStar_Tactics_Types.witness =
                                        uu____2952;
                                      FStar_Tactics_Types.goal_ty =
                                        uu____2953;
                                      FStar_Tactics_Types.opts =
                                        (uu___92_2951.FStar_Tactics_Types.opts);
                                      FStar_Tactics_Types.is_guard =
                                        (uu___92_2951.FStar_Tactics_Types.is_guard)
                                    }  in
                                  replace_cur uu____2950  in
                                bind uu____2947
                                  (fun uu____2961  ->
                                     let uu____2962 =
                                       let uu____2967 =
                                         FStar_Syntax_Syntax.mk_binder bv  in
                                       (uu____2967, b)  in
                                     ret uu____2962)
                              else fail "intro_rec: unification failed")))
         | FStar_Pervasives_Native.None  ->
             let uu____2981 =
               tts goal.FStar_Tactics_Types.context
                 goal.FStar_Tactics_Types.goal_ty
                in
             fail1 "intro_rec: goal is not an arrow (%s)" uu____2981)
  
let (norm : FStar_Syntax_Embeddings.norm_step Prims.list -> unit tac) =
  fun s  ->
    let uu____2999 = cur_goal ()  in
    bind uu____2999
      (fun goal  ->
         mlog
           (fun uu____3006  ->
              let uu____3007 =
                FStar_Syntax_Print.term_to_string
                  goal.FStar_Tactics_Types.witness
                 in
              FStar_Util.print1 "norm: witness = %s\n" uu____3007)
           (fun uu____3012  ->
              let steps =
                let uu____3016 = FStar_TypeChecker_Normalize.tr_norm_steps s
                   in
                FStar_List.append
                  [FStar_TypeChecker_Normalize.Reify;
                  FStar_TypeChecker_Normalize.UnfoldTac] uu____3016
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
                (let uu___93_3023 = goal  in
                 {
                   FStar_Tactics_Types.context =
                     (uu___93_3023.FStar_Tactics_Types.context);
                   FStar_Tactics_Types.witness = w;
                   FStar_Tactics_Types.goal_ty = t;
                   FStar_Tactics_Types.opts =
                     (uu___93_3023.FStar_Tactics_Types.opts);
                   FStar_Tactics_Types.is_guard =
                     (uu___93_3023.FStar_Tactics_Types.is_guard)
                 })))
  
let (norm_term_env :
  env ->
    FStar_Syntax_Embeddings.norm_step Prims.list ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term tac)
  =
  fun e  ->
    fun s  ->
      fun t  ->
        let uu____3047 =
          mlog
            (fun uu____3052  ->
               let uu____3053 = FStar_Syntax_Print.term_to_string t  in
               FStar_Util.print1 "norm_term: tm = %s\n" uu____3053)
            (fun uu____3055  ->
               bind get
                 (fun ps  ->
                    let opts =
                      match ps.FStar_Tactics_Types.goals with
                      | g::uu____3061 -> g.FStar_Tactics_Types.opts
                      | uu____3064 -> FStar_Options.peek ()  in
                    mlog
                      (fun uu____3069  ->
                         let uu____3070 =
                           tts ps.FStar_Tactics_Types.main_context t  in
                         FStar_Util.print1 "norm_term_env: t = %s\n"
                           uu____3070)
                      (fun uu____3073  ->
                         let uu____3074 = __tc e t  in
                         bind uu____3074
                           (fun uu____3095  ->
                              match uu____3095 with
                              | (t1,uu____3105,uu____3106) ->
                                  let steps =
                                    let uu____3110 =
                                      FStar_TypeChecker_Normalize.tr_norm_steps
                                        s
                                       in
                                    FStar_List.append
                                      [FStar_TypeChecker_Normalize.Reify;
                                      FStar_TypeChecker_Normalize.UnfoldTac]
                                      uu____3110
                                     in
                                  let t2 =
                                    normalize steps
                                      ps.FStar_Tactics_Types.main_context t1
                                     in
                                  ret t2))))
           in
        FStar_All.pipe_left (wrap_err "norm_term") uu____3047
  
let (refine_intro : unit -> unit tac) =
  fun uu____3124  ->
    let uu____3127 =
      let uu____3130 = cur_goal ()  in
      bind uu____3130
        (fun g  ->
           let uu____3137 =
             FStar_TypeChecker_Rel.base_and_refinement
               g.FStar_Tactics_Types.context g.FStar_Tactics_Types.goal_ty
              in
           match uu____3137 with
           | (uu____3150,FStar_Pervasives_Native.None ) ->
               fail "not a refinement"
           | (t,FStar_Pervasives_Native.Some (bv,phi)) ->
               let g1 =
                 let uu___94_3175 = g  in
                 {
                   FStar_Tactics_Types.context =
                     (uu___94_3175.FStar_Tactics_Types.context);
                   FStar_Tactics_Types.witness =
                     (uu___94_3175.FStar_Tactics_Types.witness);
                   FStar_Tactics_Types.goal_ty = t;
                   FStar_Tactics_Types.opts =
                     (uu___94_3175.FStar_Tactics_Types.opts);
                   FStar_Tactics_Types.is_guard =
                     (uu___94_3175.FStar_Tactics_Types.is_guard)
                 }  in
               let uu____3176 =
                 let uu____3181 =
                   let uu____3186 =
                     let uu____3187 = FStar_Syntax_Syntax.mk_binder bv  in
                     [uu____3187]  in
                   FStar_Syntax_Subst.open_term uu____3186 phi  in
                 match uu____3181 with
                 | (bvs,phi1) ->
                     let uu____3194 =
                       let uu____3195 = FStar_List.hd bvs  in
                       FStar_Pervasives_Native.fst uu____3195  in
                     (uu____3194, phi1)
                  in
               (match uu____3176 with
                | (bv1,phi1) ->
                    let uu____3208 =
                      let uu____3211 =
                        FStar_Syntax_Subst.subst
                          [FStar_Syntax_Syntax.NT
                             (bv1, (g.FStar_Tactics_Types.witness))] phi1
                         in
                      mk_irrelevant_goal "refine_intro refinement"
                        g.FStar_Tactics_Types.context uu____3211
                        g.FStar_Tactics_Types.opts
                       in
                    bind uu____3208
                      (fun g2  ->
                         bind __dismiss
                           (fun uu____3215  -> add_goals [g1; g2]))))
       in
    FStar_All.pipe_left (wrap_err "refine_intro") uu____3127
  
let (__exact_now : Prims.bool -> FStar_Syntax_Syntax.term -> unit tac) =
  fun set_expected_typ1  ->
    fun t  ->
      let uu____3234 = cur_goal ()  in
      bind uu____3234
        (fun goal  ->
           let env =
             if set_expected_typ1
             then
               FStar_TypeChecker_Env.set_expected_typ
                 goal.FStar_Tactics_Types.context
                 goal.FStar_Tactics_Types.goal_ty
             else goal.FStar_Tactics_Types.context  in
           let uu____3243 = __tc env t  in
           bind uu____3243
             (fun uu____3262  ->
                match uu____3262 with
                | (t1,typ,guard) ->
                    mlog
                      (fun uu____3277  ->
                         let uu____3278 =
                           tts goal.FStar_Tactics_Types.context typ  in
                         let uu____3279 =
                           FStar_TypeChecker_Rel.guard_to_string
                             goal.FStar_Tactics_Types.context guard
                            in
                         FStar_Util.print2
                           "__exact_now: got type %s\n__exact_now and guard %s\n"
                           uu____3278 uu____3279)
                      (fun uu____3282  ->
                         let uu____3283 =
                           proc_guard "__exact typing"
                             goal.FStar_Tactics_Types.context guard
                             goal.FStar_Tactics_Types.opts
                            in
                         bind uu____3283
                           (fun uu____3287  ->
                              mlog
                                (fun uu____3291  ->
                                   let uu____3292 =
                                     tts goal.FStar_Tactics_Types.context typ
                                      in
                                   let uu____3293 =
                                     tts goal.FStar_Tactics_Types.context
                                       goal.FStar_Tactics_Types.goal_ty
                                      in
                                   FStar_Util.print2
                                     "__exact_now: unifying %s and %s\n"
                                     uu____3292 uu____3293)
                                (fun uu____3296  ->
                                   let uu____3297 =
                                     do_unify
                                       goal.FStar_Tactics_Types.context typ
                                       goal.FStar_Tactics_Types.goal_ty
                                      in
                                   bind uu____3297
                                     (fun b  ->
                                        if b
                                        then solve goal t1
                                        else
                                          (let uu____3305 =
                                             tts
                                               goal.FStar_Tactics_Types.context
                                               t1
                                              in
                                           let uu____3306 =
                                             tts
                                               goal.FStar_Tactics_Types.context
                                               typ
                                              in
                                           let uu____3307 =
                                             tts
                                               goal.FStar_Tactics_Types.context
                                               goal.FStar_Tactics_Types.goal_ty
                                              in
                                           let uu____3308 =
                                             tts
                                               goal.FStar_Tactics_Types.context
                                               goal.FStar_Tactics_Types.witness
                                              in
                                           fail4
                                             "%s : %s does not exactly solve the goal %s (witness = %s)"
                                             uu____3305 uu____3306 uu____3307
                                             uu____3308)))))))
  
let (t_exact : Prims.bool -> FStar_Syntax_Syntax.term -> unit tac) =
  fun set_expected_typ1  ->
    fun tm  ->
      let uu____3323 =
        mlog
          (fun uu____3328  ->
             let uu____3329 = FStar_Syntax_Print.term_to_string tm  in
             FStar_Util.print1 "t_exact: tm = %s\n" uu____3329)
          (fun uu____3332  ->
             let uu____3333 =
               let uu____3340 = __exact_now set_expected_typ1 tm  in
               trytac' uu____3340  in
             bind uu____3333
               (fun uu___60_3349  ->
                  match uu___60_3349 with
                  | FStar_Util.Inr r -> ret ()
                  | FStar_Util.Inl e ->
                      let uu____3358 =
                        let uu____3365 =
                          let uu____3368 =
                            norm [FStar_Syntax_Embeddings.Delta]  in
                          bind uu____3368
                            (fun uu____3373  ->
                               let uu____3374 = refine_intro ()  in
                               bind uu____3374
                                 (fun uu____3378  ->
                                    __exact_now set_expected_typ1 tm))
                           in
                        trytac' uu____3365  in
                      bind uu____3358
                        (fun uu___59_3385  ->
                           match uu___59_3385 with
                           | FStar_Util.Inr r -> ret ()
                           | FStar_Util.Inl uu____3393 -> fail e)))
         in
      FStar_All.pipe_left (wrap_err "exact") uu____3323
  
let (uvar_free_in_goal :
  FStar_Syntax_Syntax.uvar -> FStar_Tactics_Types.goal -> Prims.bool) =
  fun u  ->
    fun g  ->
      if g.FStar_Tactics_Types.is_guard
      then false
      else
        (let free_uvars =
           let uu____3412 =
             let uu____3419 =
               FStar_Syntax_Free.uvars g.FStar_Tactics_Types.goal_ty  in
             FStar_Util.set_elements uu____3419  in
           FStar_List.map FStar_Pervasives_Native.fst uu____3412  in
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
          let uu____3489 = f x  in
          bind uu____3489
            (fun y  ->
               let uu____3497 = mapM f xs  in
               bind uu____3497 (fun ys  -> ret (y :: ys)))
  
exception NoUnif 
let (uu___is_NoUnif : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with | NoUnif  -> true | uu____3517 -> false
  
let rec (__apply :
  Prims.bool ->
    FStar_Syntax_Syntax.term -> FStar_Reflection_Data.typ -> unit tac)
  =
  fun uopt  ->
    fun tm  ->
      fun typ  ->
        let uu____3537 = cur_goal ()  in
        bind uu____3537
          (fun goal  ->
             mlog
               (fun uu____3544  ->
                  let uu____3545 = FStar_Syntax_Print.term_to_string tm  in
                  FStar_Util.print1 ">>> Calling __exact(%s)\n" uu____3545)
               (fun uu____3548  ->
                  let uu____3549 =
                    let uu____3554 =
                      let uu____3557 = t_exact false tm  in
                      with_policy FStar_Tactics_Types.Force uu____3557  in
                    trytac_exn uu____3554  in
                  bind uu____3549
                    (fun uu___61_3564  ->
                       match uu___61_3564 with
                       | FStar_Pervasives_Native.Some r -> ret ()
                       | FStar_Pervasives_Native.None  ->
                           mlog
                             (fun uu____3572  ->
                                let uu____3573 =
                                  FStar_Syntax_Print.term_to_string typ  in
                                FStar_Util.print1 ">>> typ = %s\n" uu____3573)
                             (fun uu____3576  ->
                                let uu____3577 =
                                  FStar_Syntax_Util.arrow_one typ  in
                                match uu____3577 with
                                | FStar_Pervasives_Native.None  ->
                                    FStar_Exn.raise NoUnif
                                | FStar_Pervasives_Native.Some ((bv,aq),c) ->
                                    mlog
                                      (fun uu____3609  ->
                                         let uu____3610 =
                                           FStar_Syntax_Print.binder_to_string
                                             (bv, aq)
                                            in
                                         FStar_Util.print1
                                           "__apply: pushing binder %s\n"
                                           uu____3610)
                                      (fun uu____3613  ->
                                         let uu____3614 =
                                           let uu____3615 =
                                             FStar_Syntax_Util.is_total_comp
                                               c
                                              in
                                           Prims.op_Negation uu____3615  in
                                         if uu____3614
                                         then
                                           fail "apply: not total codomain"
                                         else
                                           (let uu____3619 =
                                              new_uvar "apply"
                                                goal.FStar_Tactics_Types.context
                                                bv.FStar_Syntax_Syntax.sort
                                               in
                                            bind uu____3619
                                              (fun u  ->
                                                 let tm' =
                                                   FStar_Syntax_Syntax.mk_Tm_app
                                                     tm [(u, aq)]
                                                     FStar_Pervasives_Native.None
                                                     tm.FStar_Syntax_Syntax.pos
                                                    in
                                                 let typ' =
                                                   let uu____3639 =
                                                     comp_to_typ c  in
                                                   FStar_All.pipe_left
                                                     (FStar_Syntax_Subst.subst
                                                        [FStar_Syntax_Syntax.NT
                                                           (bv, u)])
                                                     uu____3639
                                                    in
                                                 let uu____3640 =
                                                   __apply uopt tm' typ'  in
                                                 bind uu____3640
                                                   (fun uu____3648  ->
                                                      let u1 =
                                                        bnorm
                                                          goal.FStar_Tactics_Types.context
                                                          u
                                                         in
                                                      let uu____3650 =
                                                        let uu____3651 =
                                                          let uu____3654 =
                                                            let uu____3655 =
                                                              FStar_Syntax_Util.head_and_args
                                                                u1
                                                               in
                                                            FStar_Pervasives_Native.fst
                                                              uu____3655
                                                             in
                                                          FStar_Syntax_Subst.compress
                                                            uu____3654
                                                           in
                                                        uu____3651.FStar_Syntax_Syntax.n
                                                         in
                                                      match uu____3650 with
                                                      | FStar_Syntax_Syntax.Tm_uvar
                                                          (uvar,uu____3683)
                                                          ->
                                                          bind get
                                                            (fun ps  ->
                                                               let uu____3711
                                                                 =
                                                                 uopt &&
                                                                   (uvar_free
                                                                    uvar ps)
                                                                  in
                                                               if uu____3711
                                                               then ret ()
                                                               else
                                                                 (let uu____3715
                                                                    =
                                                                    let uu____3718
                                                                    =
                                                                    let uu___95_3719
                                                                    = goal
                                                                     in
                                                                    let uu____3720
                                                                    =
                                                                    bnorm
                                                                    goal.FStar_Tactics_Types.context
                                                                    u1  in
                                                                    let uu____3721
                                                                    =
                                                                    bnorm
                                                                    goal.FStar_Tactics_Types.context
                                                                    bv.FStar_Syntax_Syntax.sort
                                                                     in
                                                                    {
                                                                    FStar_Tactics_Types.context
                                                                    =
                                                                    (uu___95_3719.FStar_Tactics_Types.context);
                                                                    FStar_Tactics_Types.witness
                                                                    =
                                                                    uu____3720;
                                                                    FStar_Tactics_Types.goal_ty
                                                                    =
                                                                    uu____3721;
                                                                    FStar_Tactics_Types.opts
                                                                    =
                                                                    (uu___95_3719.FStar_Tactics_Types.opts);
                                                                    FStar_Tactics_Types.is_guard
                                                                    = false
                                                                    }  in
                                                                    [uu____3718]
                                                                     in
                                                                  add_goals
                                                                    uu____3715))
                                                      | t -> ret ()))))))))
  
let try_unif : 'a . 'a tac -> 'a tac -> 'a tac =
  fun t  ->
    fun t'  -> mk_tac (fun ps  -> try run t ps with | NoUnif  -> run t' ps)
  
let (apply : Prims.bool -> FStar_Syntax_Syntax.term -> unit tac) =
  fun uopt  ->
    fun tm  ->
      let uu____3776 =
        mlog
          (fun uu____3781  ->
             let uu____3782 = FStar_Syntax_Print.term_to_string tm  in
             FStar_Util.print1 "apply: tm = %s\n" uu____3782)
          (fun uu____3785  ->
             let uu____3786 = cur_goal ()  in
             bind uu____3786
               (fun goal  ->
                  let uu____3792 = __tc goal.FStar_Tactics_Types.context tm
                     in
                  bind uu____3792
                    (fun uu____3814  ->
                       match uu____3814 with
                       | (tm1,typ,guard) ->
                           let typ1 =
                             bnorm goal.FStar_Tactics_Types.context typ  in
                           let uu____3827 =
                             let uu____3830 =
                               let uu____3833 = __apply uopt tm1 typ1  in
                               bind uu____3833
                                 (fun uu____3837  ->
                                    proc_guard "apply guard"
                                      goal.FStar_Tactics_Types.context guard
                                      goal.FStar_Tactics_Types.opts)
                                in
                             focus uu____3830  in
                           let uu____3838 =
                             let uu____3841 =
                               tts goal.FStar_Tactics_Types.context tm1  in
                             let uu____3842 =
                               tts goal.FStar_Tactics_Types.context typ1  in
                             let uu____3843 =
                               tts goal.FStar_Tactics_Types.context
                                 goal.FStar_Tactics_Types.goal_ty
                                in
                             fail3
                               "Cannot instantiate %s (of type %s) to match goal (%s)"
                               uu____3841 uu____3842 uu____3843
                              in
                           try_unif uu____3827 uu____3838)))
         in
      FStar_All.pipe_left (wrap_err "apply") uu____3776
  
let (lemma_or_sq :
  FStar_Syntax_Syntax.comp ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun c  ->
    let ct = FStar_Syntax_Util.comp_to_comp_typ_nouniv c  in
    let uu____3866 =
      FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
        FStar_Parser_Const.effect_Lemma_lid
       in
    if uu____3866
    then
      let uu____3873 =
        match ct.FStar_Syntax_Syntax.effect_args with
        | pre::post::uu____3892 ->
            ((FStar_Pervasives_Native.fst pre),
              (FStar_Pervasives_Native.fst post))
        | uu____3933 -> failwith "apply_lemma: impossible: not a lemma"  in
      match uu____3873 with
      | (pre,post) ->
          let post1 =
            let uu____3969 =
              let uu____3978 =
                FStar_Syntax_Syntax.as_arg FStar_Syntax_Util.exp_unit  in
              [uu____3978]  in
            FStar_Syntax_Util.mk_app post uu____3969  in
          FStar_Pervasives_Native.Some (pre, post1)
    else
      (let uu____3992 =
         FStar_Syntax_Util.is_pure_effect ct.FStar_Syntax_Syntax.effect_name
          in
       if uu____3992
       then
         let uu____3999 =
           FStar_Syntax_Util.un_squash ct.FStar_Syntax_Syntax.result_typ  in
         FStar_Util.map_opt uu____3999
           (fun post  -> (FStar_Syntax_Util.t_true, post))
       else FStar_Pervasives_Native.None)
  
let (apply_lemma : FStar_Syntax_Syntax.term -> unit tac) =
  fun tm  ->
    let uu____4032 =
      let uu____4035 =
        mlog
          (fun uu____4040  ->
             let uu____4041 = FStar_Syntax_Print.term_to_string tm  in
             FStar_Util.print1 "apply_lemma: tm = %s\n" uu____4041)
          (fun uu____4045  ->
             let is_unit_t t =
               let uu____4051 =
                 let uu____4052 = FStar_Syntax_Subst.compress t  in
                 uu____4052.FStar_Syntax_Syntax.n  in
               match uu____4051 with
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.unit_lid
                   -> true
               | uu____4056 -> false  in
             let uu____4057 = cur_goal ()  in
             bind uu____4057
               (fun goal  ->
                  let uu____4063 = __tc goal.FStar_Tactics_Types.context tm
                     in
                  bind uu____4063
                    (fun uu____4086  ->
                       match uu____4086 with
                       | (tm1,t,guard) ->
                           let uu____4098 =
                             FStar_Syntax_Util.arrow_formals_comp t  in
                           (match uu____4098 with
                            | (bs,comp) ->
                                let uu____4125 = lemma_or_sq comp  in
                                (match uu____4125 with
                                 | FStar_Pervasives_Native.None  ->
                                     fail "not a lemma or squashed function"
                                 | FStar_Pervasives_Native.Some (pre,post) ->
                                     let uu____4144 =
                                       FStar_List.fold_left
                                         (fun uu____4190  ->
                                            fun uu____4191  ->
                                              match (uu____4190, uu____4191)
                                              with
                                              | ((uvs,guard1,subst1),(b,aq))
                                                  ->
                                                  let b_t =
                                                    FStar_Syntax_Subst.subst
                                                      subst1
                                                      b.FStar_Syntax_Syntax.sort
                                                     in
                                                  let uu____4294 =
                                                    is_unit_t b_t  in
                                                  if uu____4294
                                                  then
                                                    (((FStar_Syntax_Util.exp_unit,
                                                        aq) :: uvs), guard1,
                                                      ((FStar_Syntax_Syntax.NT
                                                          (b,
                                                            FStar_Syntax_Util.exp_unit))
                                                      :: subst1))
                                                  else
                                                    (let uu____4332 =
                                                       FStar_TypeChecker_Util.new_implicit_var
                                                         "apply_lemma"
                                                         (goal.FStar_Tactics_Types.goal_ty).FStar_Syntax_Syntax.pos
                                                         goal.FStar_Tactics_Types.context
                                                         b_t
                                                        in
                                                     match uu____4332 with
                                                     | (u,uu____4362,g_u) ->
                                                         let uu____4376 =
                                                           FStar_TypeChecker_Rel.conj_guard
                                                             guard1 g_u
                                                            in
                                                         (((u, aq) :: uvs),
                                                           uu____4376,
                                                           ((FStar_Syntax_Syntax.NT
                                                               (b, u)) ::
                                                           subst1))))
                                         ([], guard, []) bs
                                        in
                                     (match uu____4144 with
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
                                          let uu____4447 =
                                            let uu____4450 =
                                              FStar_Syntax_Util.mk_squash
                                                FStar_Syntax_Syntax.U_zero
                                                post1
                                               in
                                            do_unify
                                              goal.FStar_Tactics_Types.context
                                              uu____4450
                                              goal.FStar_Tactics_Types.goal_ty
                                             in
                                          bind uu____4447
                                            (fun b  ->
                                               if Prims.op_Negation b
                                               then
                                                 let uu____4458 =
                                                   tts
                                                     goal.FStar_Tactics_Types.context
                                                     tm1
                                                    in
                                                 let uu____4459 =
                                                   let uu____4460 =
                                                     FStar_Syntax_Util.mk_squash
                                                       FStar_Syntax_Syntax.U_zero
                                                       post1
                                                      in
                                                   tts
                                                     goal.FStar_Tactics_Types.context
                                                     uu____4460
                                                    in
                                                 let uu____4461 =
                                                   tts
                                                     goal.FStar_Tactics_Types.context
                                                     goal.FStar_Tactics_Types.goal_ty
                                                    in
                                                 fail3
                                                   "Cannot instantiate lemma %s (with postcondition: %s) to match goal (%s)"
                                                   uu____4458 uu____4459
                                                   uu____4461
                                               else
                                                 (let uu____4463 =
                                                    add_implicits
                                                      implicits.FStar_TypeChecker_Env.implicits
                                                     in
                                                  bind uu____4463
                                                    (fun uu____4468  ->
                                                       let uu____4469 =
                                                         solve goal
                                                           FStar_Syntax_Util.exp_unit
                                                          in
                                                       bind uu____4469
                                                         (fun uu____4477  ->
                                                            let is_free_uvar
                                                              uv t1 =
                                                              let free_uvars
                                                                =
                                                                let uu____4490
                                                                  =
                                                                  let uu____4497
                                                                    =
                                                                    FStar_Syntax_Free.uvars
                                                                    t1  in
                                                                  FStar_Util.set_elements
                                                                    uu____4497
                                                                   in
                                                                FStar_List.map
                                                                  FStar_Pervasives_Native.fst
                                                                  uu____4490
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
                                                              let uu____4542
                                                                =
                                                                FStar_Syntax_Util.head_and_args
                                                                  t1
                                                                 in
                                                              match uu____4542
                                                              with
                                                              | (hd1,uu____4558)
                                                                  ->
                                                                  (match 
                                                                    hd1.FStar_Syntax_Syntax.n
                                                                   with
                                                                   | 
                                                                   FStar_Syntax_Syntax.Tm_uvar
                                                                    (uv,uu____4580)
                                                                    ->
                                                                    appears
                                                                    uv goals
                                                                   | 
                                                                   uu____4605
                                                                    -> false)
                                                               in
                                                            let uu____4606 =
                                                              FStar_All.pipe_right
                                                                implicits.FStar_TypeChecker_Env.implicits
                                                                (mapM
                                                                   (fun
                                                                    uu____4678
                                                                     ->
                                                                    match uu____4678
                                                                    with
                                                                    | 
                                                                    (_msg,env,_uvar,term,typ,uu____4706)
                                                                    ->
                                                                    let uu____4707
                                                                    =
                                                                    FStar_Syntax_Util.head_and_args
                                                                    term  in
                                                                    (match uu____4707
                                                                    with
                                                                    | 
                                                                    (hd1,uu____4733)
                                                                    ->
                                                                    let uu____4754
                                                                    =
                                                                    let uu____4755
                                                                    =
                                                                    FStar_Syntax_Subst.compress
                                                                    hd1  in
                                                                    uu____4755.FStar_Syntax_Syntax.n
                                                                     in
                                                                    (match uu____4754
                                                                    with
                                                                    | 
                                                                    FStar_Syntax_Syntax.Tm_uvar
                                                                    uu____4768
                                                                    ->
                                                                    let uu____4785
                                                                    =
                                                                    let uu____4794
                                                                    =
                                                                    let uu____4797
                                                                    =
                                                                    let uu___98_4798
                                                                    = goal
                                                                     in
                                                                    let uu____4799
                                                                    =
                                                                    bnorm
                                                                    goal.FStar_Tactics_Types.context
                                                                    term  in
                                                                    let uu____4800
                                                                    =
                                                                    bnorm
                                                                    goal.FStar_Tactics_Types.context
                                                                    typ  in
                                                                    {
                                                                    FStar_Tactics_Types.context
                                                                    =
                                                                    (uu___98_4798.FStar_Tactics_Types.context);
                                                                    FStar_Tactics_Types.witness
                                                                    =
                                                                    uu____4799;
                                                                    FStar_Tactics_Types.goal_ty
                                                                    =
                                                                    uu____4800;
                                                                    FStar_Tactics_Types.opts
                                                                    =
                                                                    (uu___98_4798.FStar_Tactics_Types.opts);
                                                                    FStar_Tactics_Types.is_guard
                                                                    =
                                                                    (uu___98_4798.FStar_Tactics_Types.is_guard)
                                                                    }  in
                                                                    [uu____4797]
                                                                     in
                                                                    (uu____4794,
                                                                    [])  in
                                                                    ret
                                                                    uu____4785
                                                                    | 
                                                                    uu____4813
                                                                    ->
                                                                    let g_typ
                                                                    =
                                                                    let uu____4815
                                                                    =
                                                                    FStar_Options.__temp_fast_implicits
                                                                    ()  in
                                                                    if
                                                                    uu____4815
                                                                    then
                                                                    FStar_TypeChecker_TcTerm.check_type_of_well_typed_term
                                                                    false env
                                                                    term typ
                                                                    else
                                                                    (let term1
                                                                    =
                                                                    bnorm env
                                                                    term  in
                                                                    let uu____4818
                                                                    =
                                                                    let uu____4825
                                                                    =
                                                                    FStar_TypeChecker_Env.set_expected_typ
                                                                    env typ
                                                                     in
                                                                    env.FStar_TypeChecker_Env.type_of
                                                                    uu____4825
                                                                    term1  in
                                                                    match uu____4818
                                                                    with
                                                                    | 
                                                                    (uu____4826,uu____4827,g_typ)
                                                                    -> g_typ)
                                                                     in
                                                                    let uu____4829
                                                                    =
                                                                    goal_from_guard
                                                                    "apply_lemma solved arg"
                                                                    goal.FStar_Tactics_Types.context
                                                                    g_typ
                                                                    goal.FStar_Tactics_Types.opts
                                                                     in
                                                                    bind
                                                                    uu____4829
                                                                    (fun
                                                                    uu___62_4845
                                                                     ->
                                                                    match uu___62_4845
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
                                                            bind uu____4606
                                                              (fun goals_  ->
                                                                 let sub_goals
                                                                   =
                                                                   let uu____4913
                                                                    =
                                                                    FStar_List.map
                                                                    FStar_Pervasives_Native.fst
                                                                    goals_
                                                                     in
                                                                   FStar_List.flatten
                                                                    uu____4913
                                                                    in
                                                                 let smt_goals
                                                                   =
                                                                   let uu____4935
                                                                    =
                                                                    FStar_List.map
                                                                    FStar_Pervasives_Native.snd
                                                                    goals_
                                                                     in
                                                                   FStar_List.flatten
                                                                    uu____4935
                                                                    in
                                                                 let rec filter'
                                                                   a f xs =
                                                                   match xs
                                                                   with
                                                                   | 
                                                                   [] -> []
                                                                   | 
                                                                   x::xs1 ->
                                                                    let uu____4993
                                                                    = f x xs1
                                                                     in
                                                                    if
                                                                    uu____4993
                                                                    then
                                                                    let uu____4996
                                                                    =
                                                                    filter'
                                                                    () f xs1
                                                                     in x ::
                                                                    uu____4996
                                                                    else
                                                                    filter'
                                                                    () f xs1
                                                                    in
                                                                 let sub_goals1
                                                                   =
                                                                   Obj.magic
                                                                    (filter'
                                                                    ()
                                                                    (fun a270
                                                                     ->
                                                                    fun a271 
                                                                    ->
                                                                    (Obj.magic
                                                                    (fun g 
                                                                    ->
                                                                    fun goals
                                                                     ->
                                                                    let uu____5010
                                                                    =
                                                                    checkone
                                                                    g.FStar_Tactics_Types.witness
                                                                    goals  in
                                                                    Prims.op_Negation
                                                                    uu____5010))
                                                                    a270 a271)
                                                                    (Obj.magic
                                                                    sub_goals))
                                                                    in
                                                                 let uu____5011
                                                                   =
                                                                   proc_guard
                                                                    "apply_lemma guard"
                                                                    goal.FStar_Tactics_Types.context
                                                                    guard
                                                                    goal.FStar_Tactics_Types.opts
                                                                    in
                                                                 bind
                                                                   uu____5011
                                                                   (fun
                                                                    uu____5016
                                                                     ->
                                                                    let uu____5017
                                                                    =
                                                                    let uu____5020
                                                                    =
                                                                    let uu____5021
                                                                    =
                                                                    let uu____5022
                                                                    =
                                                                    FStar_Syntax_Util.mk_squash
                                                                    FStar_Syntax_Syntax.U_zero
                                                                    pre1  in
                                                                    istrivial
                                                                    goal.FStar_Tactics_Types.context
                                                                    uu____5022
                                                                     in
                                                                    Prims.op_Negation
                                                                    uu____5021
                                                                     in
                                                                    if
                                                                    uu____5020
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
                                                                    uu____5017
                                                                    (fun
                                                                    uu____5028
                                                                     ->
                                                                    let uu____5029
                                                                    =
                                                                    add_smt_goals
                                                                    smt_goals
                                                                     in
                                                                    bind
                                                                    uu____5029
                                                                    (fun
                                                                    uu____5033
                                                                     ->
                                                                    add_goals
                                                                    sub_goals1))))))))))))))
         in
      focus uu____4035  in
    FStar_All.pipe_left (wrap_err "apply_lemma") uu____4032
  
let (destruct_eq' :
  FStar_Reflection_Data.typ ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun typ  ->
    let uu____5055 = FStar_Syntax_Util.destruct_typ_as_formula typ  in
    match uu____5055 with
    | FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn
        (l,uu____5065::(e1,uu____5067)::(e2,uu____5069)::[])) when
        FStar_Ident.lid_equals l FStar_Parser_Const.eq2_lid ->
        FStar_Pervasives_Native.Some (e1, e2)
    | uu____5128 -> FStar_Pervasives_Native.None
  
let (destruct_eq :
  FStar_Reflection_Data.typ ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun typ  ->
    let uu____5152 = destruct_eq' typ  in
    match uu____5152 with
    | FStar_Pervasives_Native.Some t -> FStar_Pervasives_Native.Some t
    | FStar_Pervasives_Native.None  ->
        let uu____5182 = FStar_Syntax_Util.un_squash typ  in
        (match uu____5182 with
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
        let uu____5243 = FStar_TypeChecker_Env.pop_bv e1  in
        match uu____5243 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (bv',e') ->
            if FStar_Syntax_Syntax.bv_eq bvar bv'
            then FStar_Pervasives_Native.Some (e', [])
            else
              (let uu____5291 = aux e'  in
               FStar_Util.map_opt uu____5291
                 (fun uu____5315  ->
                    match uu____5315 with | (e'',bvs) -> (e'', (bv' :: bvs))))
         in
      let uu____5336 = aux e  in
      FStar_Util.map_opt uu____5336
        (fun uu____5360  ->
           match uu____5360 with | (e',bvs) -> (e', (FStar_List.rev bvs)))
  
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
          let uu____5427 = split_env b1 g.FStar_Tactics_Types.context  in
          FStar_Util.map_opt uu____5427
            (fun uu____5451  ->
               match uu____5451 with
               | (e0,bvs) ->
                   let s1 bv =
                     let uu___99_5469 = bv  in
                     let uu____5470 =
                       FStar_Syntax_Subst.subst s bv.FStar_Syntax_Syntax.sort
                        in
                     {
                       FStar_Syntax_Syntax.ppname =
                         (uu___99_5469.FStar_Syntax_Syntax.ppname);
                       FStar_Syntax_Syntax.index =
                         (uu___99_5469.FStar_Syntax_Syntax.index);
                       FStar_Syntax_Syntax.sort = uu____5470
                     }  in
                   let bvs1 = FStar_List.map s1 bvs  in
                   let c = push_bvs e0 (b2 :: bvs1)  in
                   let w =
                     FStar_Syntax_Subst.subst s g.FStar_Tactics_Types.witness
                      in
                   let t =
                     FStar_Syntax_Subst.subst s g.FStar_Tactics_Types.goal_ty
                      in
                   let uu___100_5479 = g  in
                   {
                     FStar_Tactics_Types.context = c;
                     FStar_Tactics_Types.witness = w;
                     FStar_Tactics_Types.goal_ty = t;
                     FStar_Tactics_Types.opts =
                       (uu___100_5479.FStar_Tactics_Types.opts);
                     FStar_Tactics_Types.is_guard =
                       (uu___100_5479.FStar_Tactics_Types.is_guard)
                   })
  
let (rewrite : FStar_Syntax_Syntax.binder -> unit tac) =
  fun h  ->
    let uu____5489 = cur_goal ()  in
    bind uu____5489
      (fun goal  ->
         let uu____5497 = h  in
         match uu____5497 with
         | (bv,uu____5501) ->
             mlog
               (fun uu____5505  ->
                  let uu____5506 = FStar_Syntax_Print.bv_to_string bv  in
                  let uu____5507 =
                    tts goal.FStar_Tactics_Types.context
                      bv.FStar_Syntax_Syntax.sort
                     in
                  FStar_Util.print2 "+++Rewrite %s : %s\n" uu____5506
                    uu____5507)
               (fun uu____5510  ->
                  let uu____5511 =
                    split_env bv goal.FStar_Tactics_Types.context  in
                  match uu____5511 with
                  | FStar_Pervasives_Native.None  ->
                      fail "rewrite: binder not found in environment"
                  | FStar_Pervasives_Native.Some (e0,bvs) ->
                      let uu____5540 =
                        destruct_eq bv.FStar_Syntax_Syntax.sort  in
                      (match uu____5540 with
                       | FStar_Pervasives_Native.Some (x,e) ->
                           let uu____5555 =
                             let uu____5556 = FStar_Syntax_Subst.compress x
                                in
                             uu____5556.FStar_Syntax_Syntax.n  in
                           (match uu____5555 with
                            | FStar_Syntax_Syntax.Tm_name x1 ->
                                let s = [FStar_Syntax_Syntax.NT (x1, e)]  in
                                let s1 bv1 =
                                  let uu___101_5570 = bv1  in
                                  let uu____5571 =
                                    FStar_Syntax_Subst.subst s
                                      bv1.FStar_Syntax_Syntax.sort
                                     in
                                  {
                                    FStar_Syntax_Syntax.ppname =
                                      (uu___101_5570.FStar_Syntax_Syntax.ppname);
                                    FStar_Syntax_Syntax.index =
                                      (uu___101_5570.FStar_Syntax_Syntax.index);
                                    FStar_Syntax_Syntax.sort = uu____5571
                                  }  in
                                let bvs1 = FStar_List.map s1 bvs  in
                                let uu____5577 =
                                  let uu___102_5578 = goal  in
                                  let uu____5579 = push_bvs e0 (bv :: bvs1)
                                     in
                                  let uu____5580 =
                                    FStar_Syntax_Subst.subst s
                                      goal.FStar_Tactics_Types.witness
                                     in
                                  let uu____5581 =
                                    FStar_Syntax_Subst.subst s
                                      goal.FStar_Tactics_Types.goal_ty
                                     in
                                  {
                                    FStar_Tactics_Types.context = uu____5579;
                                    FStar_Tactics_Types.witness = uu____5580;
                                    FStar_Tactics_Types.goal_ty = uu____5581;
                                    FStar_Tactics_Types.opts =
                                      (uu___102_5578.FStar_Tactics_Types.opts);
                                    FStar_Tactics_Types.is_guard =
                                      (uu___102_5578.FStar_Tactics_Types.is_guard)
                                  }  in
                                replace_cur uu____5577
                            | uu____5582 ->
                                fail
                                  "rewrite: Not an equality hypothesis with a variable on the LHS")
                       | uu____5583 ->
                           fail "rewrite: Not an equality hypothesis")))
  
let (rename_to : FStar_Syntax_Syntax.binder -> Prims.string -> unit tac) =
  fun b  ->
    fun s  ->
      let uu____5604 = cur_goal ()  in
      bind uu____5604
        (fun goal  ->
           let uu____5615 = b  in
           match uu____5615 with
           | (bv,uu____5619) ->
               let bv' =
                 let uu____5621 =
                   let uu___103_5622 = bv  in
                   let uu____5623 =
                     FStar_Ident.mk_ident
                       (s,
                         ((bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange))
                      in
                   {
                     FStar_Syntax_Syntax.ppname = uu____5623;
                     FStar_Syntax_Syntax.index =
                       (uu___103_5622.FStar_Syntax_Syntax.index);
                     FStar_Syntax_Syntax.sort =
                       (uu___103_5622.FStar_Syntax_Syntax.sort)
                   }  in
                 FStar_Syntax_Syntax.freshen_bv uu____5621  in
               let s1 =
                 let uu____5627 =
                   let uu____5628 =
                     let uu____5635 = FStar_Syntax_Syntax.bv_to_name bv'  in
                     (bv, uu____5635)  in
                   FStar_Syntax_Syntax.NT uu____5628  in
                 [uu____5627]  in
               let uu____5636 = subst_goal bv bv' s1 goal  in
               (match uu____5636 with
                | FStar_Pervasives_Native.None  ->
                    fail "rename_to: binder not found in environment"
                | FStar_Pervasives_Native.Some goal1 -> replace_cur goal1))
  
let (binder_retype : FStar_Syntax_Syntax.binder -> unit tac) =
  fun b  ->
    let uu____5651 = cur_goal ()  in
    bind uu____5651
      (fun goal  ->
         let uu____5660 = b  in
         match uu____5660 with
         | (bv,uu____5664) ->
             let uu____5665 = split_env bv goal.FStar_Tactics_Types.context
                in
             (match uu____5665 with
              | FStar_Pervasives_Native.None  ->
                  fail "binder_retype: binder is not present in environment"
              | FStar_Pervasives_Native.Some (e0,bvs) ->
                  let uu____5694 = FStar_Syntax_Util.type_u ()  in
                  (match uu____5694 with
                   | (ty,u) ->
                       let uu____5703 = new_uvar "binder_retype" e0 ty  in
                       bind uu____5703
                         (fun t'  ->
                            let bv'' =
                              let uu___104_5713 = bv  in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___104_5713.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___104_5713.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = t'
                              }  in
                            let s =
                              let uu____5717 =
                                let uu____5718 =
                                  let uu____5725 =
                                    FStar_Syntax_Syntax.bv_to_name bv''  in
                                  (bv, uu____5725)  in
                                FStar_Syntax_Syntax.NT uu____5718  in
                              [uu____5717]  in
                            let bvs1 =
                              FStar_List.map
                                (fun b1  ->
                                   let uu___105_5733 = b1  in
                                   let uu____5734 =
                                     FStar_Syntax_Subst.subst s
                                       b1.FStar_Syntax_Syntax.sort
                                      in
                                   {
                                     FStar_Syntax_Syntax.ppname =
                                       (uu___105_5733.FStar_Syntax_Syntax.ppname);
                                     FStar_Syntax_Syntax.index =
                                       (uu___105_5733.FStar_Syntax_Syntax.index);
                                     FStar_Syntax_Syntax.sort = uu____5734
                                   }) bvs
                               in
                            let env' = push_bvs e0 (bv'' :: bvs1)  in
                            bind __dismiss
                              (fun uu____5740  ->
                                 let uu____5741 =
                                   let uu____5744 =
                                     let uu____5747 =
                                       let uu___106_5748 = goal  in
                                       let uu____5749 =
                                         FStar_Syntax_Subst.subst s
                                           goal.FStar_Tactics_Types.witness
                                          in
                                       let uu____5750 =
                                         FStar_Syntax_Subst.subst s
                                           goal.FStar_Tactics_Types.goal_ty
                                          in
                                       {
                                         FStar_Tactics_Types.context = env';
                                         FStar_Tactics_Types.witness =
                                           uu____5749;
                                         FStar_Tactics_Types.goal_ty =
                                           uu____5750;
                                         FStar_Tactics_Types.opts =
                                           (uu___106_5748.FStar_Tactics_Types.opts);
                                         FStar_Tactics_Types.is_guard =
                                           (uu___106_5748.FStar_Tactics_Types.is_guard)
                                       }  in
                                     [uu____5747]  in
                                   add_goals uu____5744  in
                                 bind uu____5741
                                   (fun uu____5753  ->
                                      let uu____5754 =
                                        FStar_Syntax_Util.mk_eq2
                                          (FStar_Syntax_Syntax.U_succ u) ty
                                          bv.FStar_Syntax_Syntax.sort t'
                                         in
                                      add_irrelevant_goal
                                        "binder_retype equation" e0
                                        uu____5754
                                        goal.FStar_Tactics_Types.opts))))))
  
let (norm_binder_type :
  FStar_Syntax_Embeddings.norm_step Prims.list ->
    FStar_Syntax_Syntax.binder -> unit tac)
  =
  fun s  ->
    fun b  ->
      let uu____5773 = cur_goal ()  in
      bind uu____5773
        (fun goal  ->
           let uu____5782 = b  in
           match uu____5782 with
           | (bv,uu____5786) ->
               let uu____5787 = split_env bv goal.FStar_Tactics_Types.context
                  in
               (match uu____5787 with
                | FStar_Pervasives_Native.None  ->
                    fail
                      "binder_retype: binder is not present in environment"
                | FStar_Pervasives_Native.Some (e0,bvs) ->
                    let steps =
                      let uu____5819 =
                        FStar_TypeChecker_Normalize.tr_norm_steps s  in
                      FStar_List.append
                        [FStar_TypeChecker_Normalize.Reify;
                        FStar_TypeChecker_Normalize.UnfoldTac] uu____5819
                       in
                    let sort' =
                      normalize steps e0 bv.FStar_Syntax_Syntax.sort  in
                    let bv' =
                      let uu___107_5824 = bv  in
                      {
                        FStar_Syntax_Syntax.ppname =
                          (uu___107_5824.FStar_Syntax_Syntax.ppname);
                        FStar_Syntax_Syntax.index =
                          (uu___107_5824.FStar_Syntax_Syntax.index);
                        FStar_Syntax_Syntax.sort = sort'
                      }  in
                    let env' = push_bvs e0 (bv' :: bvs)  in
                    replace_cur
                      (let uu___108_5828 = goal  in
                       {
                         FStar_Tactics_Types.context = env';
                         FStar_Tactics_Types.witness =
                           (uu___108_5828.FStar_Tactics_Types.witness);
                         FStar_Tactics_Types.goal_ty =
                           (uu___108_5828.FStar_Tactics_Types.goal_ty);
                         FStar_Tactics_Types.opts =
                           (uu___108_5828.FStar_Tactics_Types.opts);
                         FStar_Tactics_Types.is_guard =
                           (uu___108_5828.FStar_Tactics_Types.is_guard)
                       })))
  
let (revert : unit -> unit tac) =
  fun uu____5835  ->
    let uu____5838 = cur_goal ()  in
    bind uu____5838
      (fun goal  ->
         let uu____5844 =
           FStar_TypeChecker_Env.pop_bv goal.FStar_Tactics_Types.context  in
         match uu____5844 with
         | FStar_Pervasives_Native.None  ->
             fail "Cannot revert; empty context"
         | FStar_Pervasives_Native.Some (x,env') ->
             let typ' =
               let uu____5866 =
                 FStar_Syntax_Syntax.mk_Total
                   goal.FStar_Tactics_Types.goal_ty
                  in
               FStar_Syntax_Util.arrow [(x, FStar_Pervasives_Native.None)]
                 uu____5866
                in
             let w' =
               FStar_Syntax_Util.abs [(x, FStar_Pervasives_Native.None)]
                 goal.FStar_Tactics_Types.witness
                 FStar_Pervasives_Native.None
                in
             replace_cur
               (let uu___109_5900 = goal  in
                {
                  FStar_Tactics_Types.context = env';
                  FStar_Tactics_Types.witness = w';
                  FStar_Tactics_Types.goal_ty = typ';
                  FStar_Tactics_Types.opts =
                    (uu___109_5900.FStar_Tactics_Types.opts);
                  FStar_Tactics_Types.is_guard =
                    (uu___109_5900.FStar_Tactics_Types.is_guard)
                }))
  
let (free_in :
  FStar_Syntax_Syntax.bv -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun bv  ->
    fun t  ->
      let uu____5911 = FStar_Syntax_Free.names t  in
      FStar_Util.set_mem bv uu____5911
  
let rec (clear : FStar_Syntax_Syntax.binder -> unit tac) =
  fun b  ->
    let bv = FStar_Pervasives_Native.fst b  in
    let uu____5924 = cur_goal ()  in
    bind uu____5924
      (fun goal  ->
         mlog
           (fun uu____5932  ->
              let uu____5933 = FStar_Syntax_Print.binder_to_string b  in
              let uu____5934 =
                let uu____5935 =
                  let uu____5936 =
                    FStar_TypeChecker_Env.all_binders
                      goal.FStar_Tactics_Types.context
                     in
                  FStar_All.pipe_right uu____5936 FStar_List.length  in
                FStar_All.pipe_right uu____5935 FStar_Util.string_of_int  in
              FStar_Util.print2 "Clear of (%s), env has %s binders\n"
                uu____5933 uu____5934)
           (fun uu____5947  ->
              let uu____5948 = split_env bv goal.FStar_Tactics_Types.context
                 in
              match uu____5948 with
              | FStar_Pervasives_Native.None  ->
                  fail "Cannot clear; binder not in environment"
              | FStar_Pervasives_Native.Some (e',bvs) ->
                  let rec check1 bvs1 =
                    match bvs1 with
                    | [] -> ret ()
                    | bv'::bvs2 ->
                        let uu____5994 =
                          free_in bv bv'.FStar_Syntax_Syntax.sort  in
                        if uu____5994
                        then
                          let uu____5997 =
                            let uu____5998 =
                              FStar_Syntax_Print.bv_to_string bv'  in
                            FStar_Util.format1
                              "Cannot clear; binder present in the type of %s"
                              uu____5998
                             in
                          fail uu____5997
                        else check1 bvs2
                     in
                  let uu____6000 =
                    free_in bv goal.FStar_Tactics_Types.goal_ty  in
                  if uu____6000
                  then fail "Cannot clear; binder present in goal"
                  else
                    (let uu____6004 = check1 bvs  in
                     bind uu____6004
                       (fun uu____6010  ->
                          let env' = push_bvs e' bvs  in
                          let uu____6012 =
                            new_uvar "clear.witness" env'
                              goal.FStar_Tactics_Types.goal_ty
                             in
                          bind uu____6012
                            (fun ut  ->
                               let uu____6018 =
                                 do_unify goal.FStar_Tactics_Types.context
                                   goal.FStar_Tactics_Types.witness ut
                                  in
                               bind uu____6018
                                 (fun b1  ->
                                    if b1
                                    then
                                      replace_cur
                                        (let uu___110_6027 = goal  in
                                         {
                                           FStar_Tactics_Types.context = env';
                                           FStar_Tactics_Types.witness = ut;
                                           FStar_Tactics_Types.goal_ty =
                                             (uu___110_6027.FStar_Tactics_Types.goal_ty);
                                           FStar_Tactics_Types.opts =
                                             (uu___110_6027.FStar_Tactics_Types.opts);
                                           FStar_Tactics_Types.is_guard =
                                             (uu___110_6027.FStar_Tactics_Types.is_guard)
                                         })
                                    else
                                      fail
                                        "Cannot clear; binder appears in witness"))))))
  
let (clear_top : unit -> unit tac) =
  fun uu____6035  ->
    let uu____6038 = cur_goal ()  in
    bind uu____6038
      (fun goal  ->
         let uu____6044 =
           FStar_TypeChecker_Env.pop_bv goal.FStar_Tactics_Types.context  in
         match uu____6044 with
         | FStar_Pervasives_Native.None  ->
             fail "Cannot clear; empty context"
         | FStar_Pervasives_Native.Some (x,uu____6058) ->
             let uu____6063 = FStar_Syntax_Syntax.mk_binder x  in
             clear uu____6063)
  
let (prune : Prims.string -> unit tac) =
  fun s  ->
    let uu____6073 = cur_goal ()  in
    bind uu____6073
      (fun g  ->
         let ctx = g.FStar_Tactics_Types.context  in
         let ctx' =
           let uu____6083 = FStar_Ident.path_of_text s  in
           FStar_TypeChecker_Env.rem_proof_ns ctx uu____6083  in
         let g' =
           let uu___111_6085 = g  in
           {
             FStar_Tactics_Types.context = ctx';
             FStar_Tactics_Types.witness =
               (uu___111_6085.FStar_Tactics_Types.witness);
             FStar_Tactics_Types.goal_ty =
               (uu___111_6085.FStar_Tactics_Types.goal_ty);
             FStar_Tactics_Types.opts =
               (uu___111_6085.FStar_Tactics_Types.opts);
             FStar_Tactics_Types.is_guard =
               (uu___111_6085.FStar_Tactics_Types.is_guard)
           }  in
         bind __dismiss (fun uu____6087  -> add_goals [g']))
  
let (addns : Prims.string -> unit tac) =
  fun s  ->
    let uu____6097 = cur_goal ()  in
    bind uu____6097
      (fun g  ->
         let ctx = g.FStar_Tactics_Types.context  in
         let ctx' =
           let uu____6107 = FStar_Ident.path_of_text s  in
           FStar_TypeChecker_Env.add_proof_ns ctx uu____6107  in
         let g' =
           let uu___112_6109 = g  in
           {
             FStar_Tactics_Types.context = ctx';
             FStar_Tactics_Types.witness =
               (uu___112_6109.FStar_Tactics_Types.witness);
             FStar_Tactics_Types.goal_ty =
               (uu___112_6109.FStar_Tactics_Types.goal_ty);
             FStar_Tactics_Types.opts =
               (uu___112_6109.FStar_Tactics_Types.opts);
             FStar_Tactics_Types.is_guard =
               (uu___112_6109.FStar_Tactics_Types.is_guard)
           }  in
         bind __dismiss (fun uu____6111  -> add_goals [g']))
  
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
            let uu____6151 = FStar_Syntax_Subst.compress t  in
            uu____6151.FStar_Syntax_Syntax.n  in
          let uu____6154 =
            if d = FStar_Tactics_Types.TopDown
            then
              f env
                (let uu___116_6160 = t  in
                 {
                   FStar_Syntax_Syntax.n = tn;
                   FStar_Syntax_Syntax.pos =
                     (uu___116_6160.FStar_Syntax_Syntax.pos);
                   FStar_Syntax_Syntax.vars =
                     (uu___116_6160.FStar_Syntax_Syntax.vars)
                 })
            else ret t  in
          bind uu____6154
            (fun t1  ->
               let ff = tac_fold_env d f env  in
               let tn1 =
                 let uu____6175 =
                   let uu____6176 = FStar_Syntax_Subst.compress t1  in
                   uu____6176.FStar_Syntax_Syntax.n  in
                 match uu____6175 with
                 | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
                     let uu____6203 = ff hd1  in
                     bind uu____6203
                       (fun hd2  ->
                          let fa uu____6224 =
                            match uu____6224 with
                            | (a,q) ->
                                let uu____6237 = ff a  in
                                bind uu____6237 (fun a1  -> ret (a1, q))
                             in
                          let uu____6250 = mapM fa args  in
                          bind uu____6250
                            (fun args1  ->
                               ret (FStar_Syntax_Syntax.Tm_app (hd2, args1))))
                 | FStar_Syntax_Syntax.Tm_abs (bs,t2,k) ->
                     let uu____6310 = FStar_Syntax_Subst.open_term bs t2  in
                     (match uu____6310 with
                      | (bs1,t') ->
                          let uu____6319 =
                            let uu____6322 =
                              FStar_TypeChecker_Env.push_binders env bs1  in
                            tac_fold_env d f uu____6322 t'  in
                          bind uu____6319
                            (fun t''  ->
                               let uu____6326 =
                                 let uu____6327 =
                                   let uu____6344 =
                                     FStar_Syntax_Subst.close_binders bs1  in
                                   let uu____6345 =
                                     FStar_Syntax_Subst.close bs1 t''  in
                                   (uu____6344, uu____6345, k)  in
                                 FStar_Syntax_Syntax.Tm_abs uu____6327  in
                               ret uu____6326))
                 | FStar_Syntax_Syntax.Tm_arrow (bs,k) -> ret tn
                 | FStar_Syntax_Syntax.Tm_match (hd1,brs) ->
                     let uu____6404 = ff hd1  in
                     bind uu____6404
                       (fun hd2  ->
                          let ffb br =
                            let uu____6418 =
                              FStar_Syntax_Subst.open_branch br  in
                            match uu____6418 with
                            | (pat,w,e) ->
                                let bvs = FStar_Syntax_Syntax.pat_bvs pat  in
                                let ff1 =
                                  let uu____6449 =
                                    FStar_TypeChecker_Env.push_bvs env bvs
                                     in
                                  tac_fold_env d f uu____6449  in
                                let uu____6450 = ff1 e  in
                                bind uu____6450
                                  (fun e1  ->
                                     let br1 =
                                       FStar_Syntax_Subst.close_branch
                                         (pat, w, e1)
                                        in
                                     ret br1)
                             in
                          let uu____6463 = mapM ffb brs  in
                          bind uu____6463
                            (fun brs1  ->
                               ret (FStar_Syntax_Syntax.Tm_match (hd2, brs1))))
                 | FStar_Syntax_Syntax.Tm_let
                     ((false
                       ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inl bv;
                          FStar_Syntax_Syntax.lbunivs = uu____6477;
                          FStar_Syntax_Syntax.lbtyp = uu____6478;
                          FStar_Syntax_Syntax.lbeff = uu____6479;
                          FStar_Syntax_Syntax.lbdef = def;
                          FStar_Syntax_Syntax.lbattrs = uu____6481;
                          FStar_Syntax_Syntax.lbpos = uu____6482;_}::[]),e)
                     ->
                     let lb =
                       let uu____6507 =
                         let uu____6508 = FStar_Syntax_Subst.compress t1  in
                         uu____6508.FStar_Syntax_Syntax.n  in
                       match uu____6507 with
                       | FStar_Syntax_Syntax.Tm_let
                           ((false ,lb::[]),uu____6512) -> lb
                       | uu____6525 -> failwith "impossible"  in
                     let fflb lb1 =
                       let uu____6533 = ff lb1.FStar_Syntax_Syntax.lbdef  in
                       bind uu____6533
                         (fun def1  ->
                            ret
                              (let uu___113_6539 = lb1  in
                               {
                                 FStar_Syntax_Syntax.lbname =
                                   (uu___113_6539.FStar_Syntax_Syntax.lbname);
                                 FStar_Syntax_Syntax.lbunivs =
                                   (uu___113_6539.FStar_Syntax_Syntax.lbunivs);
                                 FStar_Syntax_Syntax.lbtyp =
                                   (uu___113_6539.FStar_Syntax_Syntax.lbtyp);
                                 FStar_Syntax_Syntax.lbeff =
                                   (uu___113_6539.FStar_Syntax_Syntax.lbeff);
                                 FStar_Syntax_Syntax.lbdef = def1;
                                 FStar_Syntax_Syntax.lbattrs =
                                   (uu___113_6539.FStar_Syntax_Syntax.lbattrs);
                                 FStar_Syntax_Syntax.lbpos =
                                   (uu___113_6539.FStar_Syntax_Syntax.lbpos)
                               }))
                        in
                     let uu____6540 = fflb lb  in
                     bind uu____6540
                       (fun lb1  ->
                          let uu____6550 =
                            let uu____6555 =
                              let uu____6556 =
                                FStar_Syntax_Syntax.mk_binder bv  in
                              [uu____6556]  in
                            FStar_Syntax_Subst.open_term uu____6555 e  in
                          match uu____6550 with
                          | (bs,e1) ->
                              let ff1 =
                                let uu____6567 =
                                  FStar_TypeChecker_Env.push_binders env bs
                                   in
                                tac_fold_env d f uu____6567  in
                              let uu____6568 = ff1 e1  in
                              bind uu____6568
                                (fun e2  ->
                                   let e3 = FStar_Syntax_Subst.close bs e2
                                      in
                                   ret
                                     (FStar_Syntax_Syntax.Tm_let
                                        ((false, [lb1]), e3))))
                 | FStar_Syntax_Syntax.Tm_let ((true ,lbs),e) ->
                     let fflb lb =
                       let uu____6606 = ff lb.FStar_Syntax_Syntax.lbdef  in
                       bind uu____6606
                         (fun def  ->
                            ret
                              (let uu___114_6612 = lb  in
                               {
                                 FStar_Syntax_Syntax.lbname =
                                   (uu___114_6612.FStar_Syntax_Syntax.lbname);
                                 FStar_Syntax_Syntax.lbunivs =
                                   (uu___114_6612.FStar_Syntax_Syntax.lbunivs);
                                 FStar_Syntax_Syntax.lbtyp =
                                   (uu___114_6612.FStar_Syntax_Syntax.lbtyp);
                                 FStar_Syntax_Syntax.lbeff =
                                   (uu___114_6612.FStar_Syntax_Syntax.lbeff);
                                 FStar_Syntax_Syntax.lbdef = def;
                                 FStar_Syntax_Syntax.lbattrs =
                                   (uu___114_6612.FStar_Syntax_Syntax.lbattrs);
                                 FStar_Syntax_Syntax.lbpos =
                                   (uu___114_6612.FStar_Syntax_Syntax.lbpos)
                               }))
                        in
                     let uu____6613 = FStar_Syntax_Subst.open_let_rec lbs e
                        in
                     (match uu____6613 with
                      | (lbs1,e1) ->
                          let uu____6628 = mapM fflb lbs1  in
                          bind uu____6628
                            (fun lbs2  ->
                               let uu____6640 = ff e1  in
                               bind uu____6640
                                 (fun e2  ->
                                    let uu____6648 =
                                      FStar_Syntax_Subst.close_let_rec lbs2
                                        e2
                                       in
                                    match uu____6648 with
                                    | (lbs3,e3) ->
                                        ret
                                          (FStar_Syntax_Syntax.Tm_let
                                             ((true, lbs3), e3)))))
                 | FStar_Syntax_Syntax.Tm_ascribed (t2,asc,eff) ->
                     let uu____6714 = ff t2  in
                     bind uu____6714
                       (fun t3  ->
                          ret
                            (FStar_Syntax_Syntax.Tm_ascribed (t3, asc, eff)))
                 | FStar_Syntax_Syntax.Tm_meta (t2,m) ->
                     let uu____6743 = ff t2  in
                     bind uu____6743
                       (fun t3  -> ret (FStar_Syntax_Syntax.Tm_meta (t3, m)))
                 | uu____6748 -> ret tn  in
               bind tn1
                 (fun tn2  ->
                    let t' =
                      let uu___115_6755 = t1  in
                      {
                        FStar_Syntax_Syntax.n = tn2;
                        FStar_Syntax_Syntax.pos =
                          (uu___115_6755.FStar_Syntax_Syntax.pos);
                        FStar_Syntax_Syntax.vars =
                          (uu___115_6755.FStar_Syntax_Syntax.vars)
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
            let uu____6794 = FStar_TypeChecker_TcTerm.tc_term env t  in
            match uu____6794 with
            | (t1,lcomp,g) ->
                let uu____6806 =
                  (let uu____6809 =
                     FStar_Syntax_Util.is_pure_or_ghost_lcomp lcomp  in
                   Prims.op_Negation uu____6809) ||
                    (let uu____6811 = FStar_TypeChecker_Rel.is_trivial g  in
                     Prims.op_Negation uu____6811)
                   in
                if uu____6806
                then ret t1
                else
                  (let rewrite_eq =
                     let typ = lcomp.FStar_Syntax_Syntax.res_typ  in
                     let uu____6821 = new_uvar "pointwise_rec" env typ  in
                     bind uu____6821
                       (fun ut  ->
                          let uu____6828 =
                            log ps
                              (fun uu____6832  ->
                                 let uu____6833 =
                                   FStar_Syntax_Print.term_to_string t1  in
                                 let uu____6834 =
                                   FStar_Syntax_Print.term_to_string ut  in
                                 FStar_Util.print2
                                   "Pointwise_rec: making equality\n\t%s ==\n\t%s\n"
                                   uu____6833 uu____6834)
                             in
                          let uu____6835 =
                            let uu____6838 =
                              let uu____6839 =
                                FStar_TypeChecker_TcTerm.universe_of env typ
                                 in
                              FStar_Syntax_Util.mk_eq2 uu____6839 typ t1 ut
                               in
                            add_irrelevant_goal "pointwise_rec equation" env
                              uu____6838 opts
                             in
                          bind uu____6835
                            (fun uu____6842  ->
                               let uu____6843 =
                                 bind tau
                                   (fun uu____6849  ->
                                      let ut1 =
                                        FStar_TypeChecker_Normalize.reduce_uvar_solutions
                                          env ut
                                         in
                                      let uu____6851 =
                                        log ps
                                          (fun uu____6855  ->
                                             let uu____6856 =
                                               FStar_Syntax_Print.term_to_string
                                                 t1
                                                in
                                             let uu____6857 =
                                               FStar_Syntax_Print.term_to_string
                                                 ut1
                                                in
                                             FStar_Util.print2
                                               "Pointwise_rec: succeeded rewriting\n\t%s to\n\t%s\n"
                                               uu____6856 uu____6857)
                                         in
                                      ret ut1)
                                  in
                               focus uu____6843))
                      in
                   let uu____6858 = trytac' rewrite_eq  in
                   bind uu____6858
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
          let uu____7026 = FStar_Syntax_Subst.compress t  in
          maybe_continue ctrl uu____7026
            (fun t1  ->
               let uu____7030 =
                 f env
                   (let uu___119_7039 = t1  in
                    {
                      FStar_Syntax_Syntax.n = (t1.FStar_Syntax_Syntax.n);
                      FStar_Syntax_Syntax.pos =
                        (uu___119_7039.FStar_Syntax_Syntax.pos);
                      FStar_Syntax_Syntax.vars =
                        (uu___119_7039.FStar_Syntax_Syntax.vars)
                    })
                  in
               bind uu____7030
                 (fun uu____7051  ->
                    match uu____7051 with
                    | (t2,ctrl1) ->
                        maybe_continue ctrl1 t2
                          (fun t3  ->
                             let uu____7070 =
                               let uu____7071 =
                                 FStar_Syntax_Subst.compress t3  in
                               uu____7071.FStar_Syntax_Syntax.n  in
                             match uu____7070 with
                             | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
                                 let uu____7104 =
                                   ctrl_tac_fold f env ctrl1 hd1  in
                                 bind uu____7104
                                   (fun uu____7129  ->
                                      match uu____7129 with
                                      | (hd2,ctrl2) ->
                                          let ctrl3 = keep_going ctrl2  in
                                          let uu____7145 =
                                            ctrl_tac_fold_args f env ctrl3
                                              args
                                             in
                                          bind uu____7145
                                            (fun uu____7172  ->
                                               match uu____7172 with
                                               | (args1,ctrl4) ->
                                                   ret
                                                     ((let uu___117_7202 = t3
                                                          in
                                                       {
                                                         FStar_Syntax_Syntax.n
                                                           =
                                                           (FStar_Syntax_Syntax.Tm_app
                                                              (hd2, args1));
                                                         FStar_Syntax_Syntax.pos
                                                           =
                                                           (uu___117_7202.FStar_Syntax_Syntax.pos);
                                                         FStar_Syntax_Syntax.vars
                                                           =
                                                           (uu___117_7202.FStar_Syntax_Syntax.vars)
                                                       }), ctrl4)))
                             | FStar_Syntax_Syntax.Tm_abs (bs,t4,k) ->
                                 let uu____7228 =
                                   FStar_Syntax_Subst.open_term bs t4  in
                                 (match uu____7228 with
                                  | (bs1,t') ->
                                      let uu____7243 =
                                        let uu____7250 =
                                          FStar_TypeChecker_Env.push_binders
                                            env bs1
                                           in
                                        ctrl_tac_fold f uu____7250 ctrl1 t'
                                         in
                                      bind uu____7243
                                        (fun uu____7268  ->
                                           match uu____7268 with
                                           | (t'',ctrl2) ->
                                               let uu____7283 =
                                                 let uu____7290 =
                                                   let uu___118_7293 = t4  in
                                                   let uu____7296 =
                                                     let uu____7297 =
                                                       let uu____7314 =
                                                         FStar_Syntax_Subst.close_binders
                                                           bs1
                                                          in
                                                       let uu____7315 =
                                                         FStar_Syntax_Subst.close
                                                           bs1 t''
                                                          in
                                                       (uu____7314,
                                                         uu____7315, k)
                                                        in
                                                     FStar_Syntax_Syntax.Tm_abs
                                                       uu____7297
                                                      in
                                                   {
                                                     FStar_Syntax_Syntax.n =
                                                       uu____7296;
                                                     FStar_Syntax_Syntax.pos
                                                       =
                                                       (uu___118_7293.FStar_Syntax_Syntax.pos);
                                                     FStar_Syntax_Syntax.vars
                                                       =
                                                       (uu___118_7293.FStar_Syntax_Syntax.vars)
                                                   }  in
                                                 (uu____7290, ctrl2)  in
                                               ret uu____7283))
                             | FStar_Syntax_Syntax.Tm_arrow (bs,k) ->
                                 ret (t3, ctrl1)
                             | uu____7348 -> ret (t3, ctrl1))))

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
              let uu____7399 = ctrl_tac_fold f env ctrl t  in
              bind uu____7399
                (fun uu____7427  ->
                   match uu____7427 with
                   | (t1,ctrl1) ->
                       let uu____7446 = ctrl_tac_fold_args f env ctrl1 ts1
                          in
                       bind uu____7446
                         (fun uu____7477  ->
                            match uu____7477 with
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
              let uu____7573 =
                let uu____7580 =
                  add_irrelevant_goal "dummy" env FStar_Syntax_Util.t_true
                    opts
                   in
                bind uu____7580
                  (fun uu____7589  ->
                     let uu____7590 = ctrl t1  in
                     bind uu____7590
                       (fun res  ->
                          let uu____7613 = trivial ()  in
                          bind uu____7613 (fun uu____7621  -> ret res)))
                 in
              bind uu____7573
                (fun uu____7637  ->
                   match uu____7637 with
                   | (should_rewrite,ctrl1) ->
                       if Prims.op_Negation should_rewrite
                       then ret (t1, ctrl1)
                       else
                         (let uu____7661 =
                            FStar_TypeChecker_TcTerm.tc_term env t1  in
                          match uu____7661 with
                          | (t2,lcomp,g) ->
                              let uu____7677 =
                                (let uu____7680 =
                                   FStar_Syntax_Util.is_pure_or_ghost_lcomp
                                     lcomp
                                    in
                                 Prims.op_Negation uu____7680) ||
                                  (let uu____7682 =
                                     FStar_TypeChecker_Rel.is_trivial g  in
                                   Prims.op_Negation uu____7682)
                                 in
                              if uu____7677
                              then ret (t2, globalStop)
                              else
                                (let typ = lcomp.FStar_Syntax_Syntax.res_typ
                                    in
                                 let uu____7697 =
                                   new_uvar "pointwise_rec" env typ  in
                                 bind uu____7697
                                   (fun ut  ->
                                      let uu____7708 =
                                        log ps
                                          (fun uu____7712  ->
                                             let uu____7713 =
                                               FStar_Syntax_Print.term_to_string
                                                 t2
                                                in
                                             let uu____7714 =
                                               FStar_Syntax_Print.term_to_string
                                                 ut
                                                in
                                             FStar_Util.print2
                                               "Pointwise_rec: making equality\n\t%s ==\n\t%s\n"
                                               uu____7713 uu____7714)
                                         in
                                      let uu____7715 =
                                        let uu____7718 =
                                          let uu____7719 =
                                            FStar_TypeChecker_TcTerm.universe_of
                                              env typ
                                             in
                                          FStar_Syntax_Util.mk_eq2 uu____7719
                                            typ t2 ut
                                           in
                                        add_irrelevant_goal
                                          "rewrite_rec equation" env
                                          uu____7718 opts
                                         in
                                      bind uu____7715
                                        (fun uu____7726  ->
                                           let uu____7727 =
                                             bind rewriter
                                               (fun uu____7741  ->
                                                  let ut1 =
                                                    FStar_TypeChecker_Normalize.reduce_uvar_solutions
                                                      env ut
                                                     in
                                                  let uu____7743 =
                                                    log ps
                                                      (fun uu____7747  ->
                                                         let uu____7748 =
                                                           FStar_Syntax_Print.term_to_string
                                                             t2
                                                            in
                                                         let uu____7749 =
                                                           FStar_Syntax_Print.term_to_string
                                                             ut1
                                                            in
                                                         FStar_Util.print2
                                                           "rewrite_rec: succeeded rewriting\n\t%s to\n\t%s\n"
                                                           uu____7748
                                                           uu____7749)
                                                     in
                                                  ret (ut1, ctrl1))
                                              in
                                           focus uu____7727)))))
  
let (topdown_rewrite :
  (FStar_Syntax_Syntax.term ->
     (Prims.bool,FStar_BigInt.t) FStar_Pervasives_Native.tuple2 tac)
    -> unit tac -> unit tac)
  =
  fun ctrl  ->
    fun rewriter  ->
      bind get
        (fun ps  ->
           let uu____7797 =
             match ps.FStar_Tactics_Types.goals with
             | g::gs -> (g, gs)
             | [] -> failwith "Pointwise: no goals"  in
           match uu____7797 with
           | (g,gs) ->
               let gt1 = g.FStar_Tactics_Types.goal_ty  in
               let uu____7831 =
                 log ps
                   (fun uu____7834  ->
                      let uu____7835 = FStar_Syntax_Print.term_to_string gt1
                         in
                      FStar_Util.print1 "Topdown_rewrite starting with %s\n"
                        uu____7835)
                  in
               bind dismiss_all
                 (fun uu____7838  ->
                    let uu____7839 =
                      ctrl_tac_fold
                        (rewrite_rec ps ctrl rewriter
                           g.FStar_Tactics_Types.opts)
                        g.FStar_Tactics_Types.context keepGoing gt1
                       in
                    bind uu____7839
                      (fun uu____7857  ->
                         match uu____7857 with
                         | (gt',uu____7865) ->
                             let uu____7866 =
                               log ps
                                 (fun uu____7869  ->
                                    let uu____7870 =
                                      FStar_Syntax_Print.term_to_string gt'
                                       in
                                    FStar_Util.print1
                                      "Topdown_rewrite seems to have succeded with %s\n"
                                      uu____7870)
                                in
                             let uu____7871 = push_goals gs  in
                             bind uu____7871
                               (fun uu____7875  ->
                                  add_goals
                                    [(let uu___120_7877 = g  in
                                      {
                                        FStar_Tactics_Types.context =
                                          (uu___120_7877.FStar_Tactics_Types.context);
                                        FStar_Tactics_Types.witness =
                                          (uu___120_7877.FStar_Tactics_Types.witness);
                                        FStar_Tactics_Types.goal_ty = gt';
                                        FStar_Tactics_Types.opts =
                                          (uu___120_7877.FStar_Tactics_Types.opts);
                                        FStar_Tactics_Types.is_guard =
                                          (uu___120_7877.FStar_Tactics_Types.is_guard)
                                      })]))))
  
let (pointwise : FStar_Tactics_Types.direction -> unit tac -> unit tac) =
  fun d  ->
    fun tau  ->
      bind get
        (fun ps  ->
           let uu____7903 =
             match ps.FStar_Tactics_Types.goals with
             | g::gs -> (g, gs)
             | [] -> failwith "Pointwise: no goals"  in
           match uu____7903 with
           | (g,gs) ->
               let gt1 = g.FStar_Tactics_Types.goal_ty  in
               let uu____7937 =
                 log ps
                   (fun uu____7940  ->
                      let uu____7941 = FStar_Syntax_Print.term_to_string gt1
                         in
                      FStar_Util.print1 "Pointwise starting with %s\n"
                        uu____7941)
                  in
               bind dismiss_all
                 (fun uu____7944  ->
                    let uu____7945 =
                      tac_fold_env d
                        (pointwise_rec ps tau g.FStar_Tactics_Types.opts)
                        g.FStar_Tactics_Types.context gt1
                       in
                    bind uu____7945
                      (fun gt'  ->
                         let uu____7952 =
                           log ps
                             (fun uu____7955  ->
                                let uu____7956 =
                                  FStar_Syntax_Print.term_to_string gt'  in
                                FStar_Util.print1
                                  "Pointwise seems to have succeded with %s\n"
                                  uu____7956)
                            in
                         let uu____7957 = push_goals gs  in
                         bind uu____7957
                           (fun uu____7961  ->
                              add_goals
                                [(let uu___121_7963 = g  in
                                  {
                                    FStar_Tactics_Types.context =
                                      (uu___121_7963.FStar_Tactics_Types.context);
                                    FStar_Tactics_Types.witness =
                                      (uu___121_7963.FStar_Tactics_Types.witness);
                                    FStar_Tactics_Types.goal_ty = gt';
                                    FStar_Tactics_Types.opts =
                                      (uu___121_7963.FStar_Tactics_Types.opts);
                                    FStar_Tactics_Types.is_guard =
                                      (uu___121_7963.FStar_Tactics_Types.is_guard)
                                  })]))))
  
let (trefl : unit -> unit tac) =
  fun uu____7970  ->
    let uu____7973 = cur_goal ()  in
    bind uu____7973
      (fun g  ->
         let uu____7991 =
           FStar_Syntax_Util.un_squash g.FStar_Tactics_Types.goal_ty  in
         match uu____7991 with
         | FStar_Pervasives_Native.Some t ->
             let uu____8003 = FStar_Syntax_Util.head_and_args' t  in
             (match uu____8003 with
              | (hd1,args) ->
                  let uu____8036 =
                    let uu____8049 =
                      let uu____8050 = FStar_Syntax_Util.un_uinst hd1  in
                      uu____8050.FStar_Syntax_Syntax.n  in
                    (uu____8049, args)  in
                  (match uu____8036 with
                   | (FStar_Syntax_Syntax.Tm_fvar
                      fv,uu____8064::(l,uu____8066)::(r,uu____8068)::[]) when
                       FStar_Syntax_Syntax.fv_eq_lid fv
                         FStar_Parser_Const.eq2_lid
                       ->
                       let uu____8115 =
                         do_unify g.FStar_Tactics_Types.context l r  in
                       bind uu____8115
                         (fun b  ->
                            if Prims.op_Negation b
                            then
                              let uu____8124 =
                                tts g.FStar_Tactics_Types.context l  in
                              let uu____8125 =
                                tts g.FStar_Tactics_Types.context r  in
                              fail2
                                "trefl: not a trivial equality (%s vs %s)"
                                uu____8124 uu____8125
                            else solve g FStar_Syntax_Util.exp_unit)
                   | (hd2,uu____8128) ->
                       let uu____8145 = tts g.FStar_Tactics_Types.context t
                          in
                       fail1 "trefl: not an equality (%s)" uu____8145))
         | FStar_Pervasives_Native.None  -> fail "not an irrelevant goal")
  
let (dup : unit -> unit tac) =
  fun uu____8154  ->
    let uu____8157 = cur_goal ()  in
    bind uu____8157
      (fun g  ->
         let uu____8163 =
           new_uvar "dup" g.FStar_Tactics_Types.context
             g.FStar_Tactics_Types.goal_ty
            in
         bind uu____8163
           (fun u  ->
              let g' =
                let uu___122_8170 = g  in
                {
                  FStar_Tactics_Types.context =
                    (uu___122_8170.FStar_Tactics_Types.context);
                  FStar_Tactics_Types.witness = u;
                  FStar_Tactics_Types.goal_ty =
                    (uu___122_8170.FStar_Tactics_Types.goal_ty);
                  FStar_Tactics_Types.opts =
                    (uu___122_8170.FStar_Tactics_Types.opts);
                  FStar_Tactics_Types.is_guard =
                    (uu___122_8170.FStar_Tactics_Types.is_guard)
                }  in
              bind __dismiss
                (fun uu____8173  ->
                   let uu____8174 =
                     let uu____8177 =
                       let uu____8178 =
                         FStar_TypeChecker_TcTerm.universe_of
                           g.FStar_Tactics_Types.context
                           g.FStar_Tactics_Types.goal_ty
                          in
                       FStar_Syntax_Util.mk_eq2 uu____8178
                         g.FStar_Tactics_Types.goal_ty u
                         g.FStar_Tactics_Types.witness
                        in
                     add_irrelevant_goal "dup equation"
                       g.FStar_Tactics_Types.context uu____8177
                       g.FStar_Tactics_Types.opts
                      in
                   bind uu____8174
                     (fun uu____8181  ->
                        let uu____8182 = add_goals [g']  in
                        bind uu____8182 (fun uu____8186  -> ret ())))))
  
let (flip : unit -> unit tac) =
  fun uu____8193  ->
    bind get
      (fun ps  ->
         match ps.FStar_Tactics_Types.goals with
         | g1::g2::gs ->
             set
               (let uu___123_8210 = ps  in
                {
                  FStar_Tactics_Types.main_context =
                    (uu___123_8210.FStar_Tactics_Types.main_context);
                  FStar_Tactics_Types.main_goal =
                    (uu___123_8210.FStar_Tactics_Types.main_goal);
                  FStar_Tactics_Types.all_implicits =
                    (uu___123_8210.FStar_Tactics_Types.all_implicits);
                  FStar_Tactics_Types.goals = (g2 :: g1 :: gs);
                  FStar_Tactics_Types.smt_goals =
                    (uu___123_8210.FStar_Tactics_Types.smt_goals);
                  FStar_Tactics_Types.depth =
                    (uu___123_8210.FStar_Tactics_Types.depth);
                  FStar_Tactics_Types.__dump =
                    (uu___123_8210.FStar_Tactics_Types.__dump);
                  FStar_Tactics_Types.psc =
                    (uu___123_8210.FStar_Tactics_Types.psc);
                  FStar_Tactics_Types.entry_range =
                    (uu___123_8210.FStar_Tactics_Types.entry_range);
                  FStar_Tactics_Types.guard_policy =
                    (uu___123_8210.FStar_Tactics_Types.guard_policy);
                  FStar_Tactics_Types.freshness =
                    (uu___123_8210.FStar_Tactics_Types.freshness)
                })
         | uu____8211 -> fail "flip: less than 2 goals")
  
let (later : unit -> unit tac) =
  fun uu____8220  ->
    bind get
      (fun ps  ->
         match ps.FStar_Tactics_Types.goals with
         | [] -> ret ()
         | g::gs ->
             set
               (let uu___124_8233 = ps  in
                {
                  FStar_Tactics_Types.main_context =
                    (uu___124_8233.FStar_Tactics_Types.main_context);
                  FStar_Tactics_Types.main_goal =
                    (uu___124_8233.FStar_Tactics_Types.main_goal);
                  FStar_Tactics_Types.all_implicits =
                    (uu___124_8233.FStar_Tactics_Types.all_implicits);
                  FStar_Tactics_Types.goals = (FStar_List.append gs [g]);
                  FStar_Tactics_Types.smt_goals =
                    (uu___124_8233.FStar_Tactics_Types.smt_goals);
                  FStar_Tactics_Types.depth =
                    (uu___124_8233.FStar_Tactics_Types.depth);
                  FStar_Tactics_Types.__dump =
                    (uu___124_8233.FStar_Tactics_Types.__dump);
                  FStar_Tactics_Types.psc =
                    (uu___124_8233.FStar_Tactics_Types.psc);
                  FStar_Tactics_Types.entry_range =
                    (uu___124_8233.FStar_Tactics_Types.entry_range);
                  FStar_Tactics_Types.guard_policy =
                    (uu___124_8233.FStar_Tactics_Types.guard_policy);
                  FStar_Tactics_Types.freshness =
                    (uu___124_8233.FStar_Tactics_Types.freshness)
                }))
  
let (qed : unit -> unit tac) =
  fun uu____8240  ->
    bind get
      (fun ps  ->
         match ps.FStar_Tactics_Types.goals with
         | [] -> ret ()
         | uu____8247 -> fail "Not done!")
  
let (cases :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 tac)
  =
  fun t  ->
    let uu____8267 =
      let uu____8274 = cur_goal ()  in
      bind uu____8274
        (fun g  ->
           let uu____8284 = __tc g.FStar_Tactics_Types.context t  in
           bind uu____8284
             (fun uu____8320  ->
                match uu____8320 with
                | (t1,typ,guard) ->
                    let uu____8336 = FStar_Syntax_Util.head_and_args typ  in
                    (match uu____8336 with
                     | (hd1,args) ->
                         let uu____8379 =
                           let uu____8392 =
                             let uu____8393 = FStar_Syntax_Util.un_uinst hd1
                                in
                             uu____8393.FStar_Syntax_Syntax.n  in
                           (uu____8392, args)  in
                         (match uu____8379 with
                          | (FStar_Syntax_Syntax.Tm_fvar
                             fv,(p,uu____8412)::(q,uu____8414)::[]) when
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
                                let uu___125_8452 = g  in
                                let uu____8453 =
                                  FStar_TypeChecker_Env.push_bv
                                    g.FStar_Tactics_Types.context v_p
                                   in
                                {
                                  FStar_Tactics_Types.context = uu____8453;
                                  FStar_Tactics_Types.witness =
                                    (uu___125_8452.FStar_Tactics_Types.witness);
                                  FStar_Tactics_Types.goal_ty =
                                    (uu___125_8452.FStar_Tactics_Types.goal_ty);
                                  FStar_Tactics_Types.opts =
                                    (uu___125_8452.FStar_Tactics_Types.opts);
                                  FStar_Tactics_Types.is_guard =
                                    (uu___125_8452.FStar_Tactics_Types.is_guard)
                                }  in
                              let g2 =
                                let uu___126_8455 = g  in
                                let uu____8456 =
                                  FStar_TypeChecker_Env.push_bv
                                    g.FStar_Tactics_Types.context v_q
                                   in
                                {
                                  FStar_Tactics_Types.context = uu____8456;
                                  FStar_Tactics_Types.witness =
                                    (uu___126_8455.FStar_Tactics_Types.witness);
                                  FStar_Tactics_Types.goal_ty =
                                    (uu___126_8455.FStar_Tactics_Types.goal_ty);
                                  FStar_Tactics_Types.opts =
                                    (uu___126_8455.FStar_Tactics_Types.opts);
                                  FStar_Tactics_Types.is_guard =
                                    (uu___126_8455.FStar_Tactics_Types.is_guard)
                                }  in
                              bind __dismiss
                                (fun uu____8463  ->
                                   let uu____8464 = add_goals [g1; g2]  in
                                   bind uu____8464
                                     (fun uu____8473  ->
                                        let uu____8474 =
                                          let uu____8479 =
                                            FStar_Syntax_Syntax.bv_to_name
                                              v_p
                                             in
                                          let uu____8480 =
                                            FStar_Syntax_Syntax.bv_to_name
                                              v_q
                                             in
                                          (uu____8479, uu____8480)  in
                                        ret uu____8474))
                          | uu____8485 ->
                              let uu____8498 =
                                tts g.FStar_Tactics_Types.context typ  in
                              fail1 "Not a disjunction: %s" uu____8498))))
       in
    FStar_All.pipe_left (wrap_err "cases") uu____8267
  
let (set_options : Prims.string -> unit tac) =
  fun s  ->
    let uu____8528 = cur_goal ()  in
    bind uu____8528
      (fun g  ->
         let uu____8539 = FStar_Options.push ()  in
         let uu____8540 =
           let uu____8541 = FStar_Util.smap_copy g.FStar_Tactics_Types.opts
              in
           FStar_Options.set uu____8541  in
         let res = FStar_Options.set_options FStar_Options.Set s  in
         let opts' = FStar_Options.peek ()  in
         let uu____8544 = FStar_Options.pop ()  in
         match res with
         | FStar_Getopt.Success  ->
             let g' =
               let uu___127_8548 = g  in
               {
                 FStar_Tactics_Types.context =
                   (uu___127_8548.FStar_Tactics_Types.context);
                 FStar_Tactics_Types.witness =
                   (uu___127_8548.FStar_Tactics_Types.witness);
                 FStar_Tactics_Types.goal_ty =
                   (uu___127_8548.FStar_Tactics_Types.goal_ty);
                 FStar_Tactics_Types.opts = opts';
                 FStar_Tactics_Types.is_guard =
                   (uu___127_8548.FStar_Tactics_Types.is_guard)
               }  in
             replace_cur g'
         | FStar_Getopt.Error err ->
             fail2 "Setting options `%s` failed: %s" s err
         | FStar_Getopt.Help  ->
             fail1 "Setting options `%s` failed (got `Help`?)" s)
  
let (top_env : unit -> env tac) =
  fun uu____8556  ->
    bind get
      (fun ps  -> FStar_All.pipe_left ret ps.FStar_Tactics_Types.main_context)
  
let (cur_env : unit -> env tac) =
  fun uu____8569  ->
    let uu____8572 = cur_goal ()  in
    bind uu____8572
      (fun g  -> FStar_All.pipe_left ret g.FStar_Tactics_Types.context)
  
let (cur_goal' : unit -> FStar_Syntax_Syntax.term tac) =
  fun uu____8585  ->
    let uu____8588 = cur_goal ()  in
    bind uu____8588
      (fun g  -> FStar_All.pipe_left ret g.FStar_Tactics_Types.goal_ty)
  
let (cur_witness : unit -> FStar_Syntax_Syntax.term tac) =
  fun uu____8601  ->
    let uu____8604 = cur_goal ()  in
    bind uu____8604
      (fun g  -> FStar_All.pipe_left ret g.FStar_Tactics_Types.witness)
  
let (unquote :
  FStar_Reflection_Data.typ ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term tac)
  =
  fun ty  ->
    fun tm  ->
      let uu____8625 =
        let uu____8628 = cur_goal ()  in
        bind uu____8628
          (fun goal  ->
             let env =
               FStar_TypeChecker_Env.set_expected_typ
                 goal.FStar_Tactics_Types.context ty
                in
             let uu____8636 = __tc env tm  in
             bind uu____8636
               (fun uu____8656  ->
                  match uu____8656 with
                  | (tm1,typ,guard) ->
                      let uu____8668 =
                        proc_guard "unquote" env guard
                          goal.FStar_Tactics_Types.opts
                         in
                      bind uu____8668 (fun uu____8672  -> ret tm1)))
         in
      FStar_All.pipe_left (wrap_err "unquote") uu____8625
  
let (uvar_env :
  env ->
    FStar_Reflection_Data.typ FStar_Pervasives_Native.option ->
      FStar_Syntax_Syntax.term tac)
  =
  fun env  ->
    fun ty  ->
      let uu____8695 =
        match ty with
        | FStar_Pervasives_Native.Some ty1 -> ret ty1
        | FStar_Pervasives_Native.None  ->
            let uu____8701 =
              let uu____8702 = FStar_Syntax_Util.type_u ()  in
              FStar_All.pipe_left FStar_Pervasives_Native.fst uu____8702  in
            new_uvar "uvar_env.2" env uu____8701
         in
      bind uu____8695
        (fun typ  ->
           let uu____8714 = new_uvar "uvar_env" env typ  in
           bind uu____8714 (fun t  -> ret t))
  
let (unshelve : FStar_Syntax_Syntax.term -> unit tac) =
  fun t  ->
    let uu____8728 =
      bind get
        (fun ps  ->
           let env = ps.FStar_Tactics_Types.main_context  in
           let opts =
             match ps.FStar_Tactics_Types.goals with
             | g::uu____8745 -> g.FStar_Tactics_Types.opts
             | uu____8748 -> FStar_Options.peek ()  in
           let uu____8751 = FStar_Syntax_Util.head_and_args t  in
           match uu____8751 with
           | ({
                FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                  (uu____8768,typ);
                FStar_Syntax_Syntax.pos = uu____8770;
                FStar_Syntax_Syntax.vars = uu____8771;_},uu____8772)
               ->
               let uu____8817 =
                 let uu____8820 =
                   let uu____8821 = bnorm env t  in
                   let uu____8822 = bnorm env typ  in
                   {
                     FStar_Tactics_Types.context = env;
                     FStar_Tactics_Types.witness = uu____8821;
                     FStar_Tactics_Types.goal_ty = uu____8822;
                     FStar_Tactics_Types.opts = opts;
                     FStar_Tactics_Types.is_guard = false
                   }  in
                 [uu____8820]  in
               add_goals uu____8817
           | uu____8823 -> fail "not a uvar")
       in
    FStar_All.pipe_left (wrap_err "unshelve") uu____8728
  
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
          (fun uu____8880  ->
             let uu____8881 = FStar_Options.unsafe_tactic_exec ()  in
             if uu____8881
             then
               let s =
                 FStar_Util.launch_process true "tactic_launch" prog args
                   input (fun uu____8887  -> fun uu____8888  -> false)
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
        (fun uu____8906  ->
           let uu____8907 =
             FStar_Syntax_Syntax.gen_bv nm FStar_Pervasives_Native.None t  in
           ret uu____8907)
  
let (change : FStar_Reflection_Data.typ -> unit tac) =
  fun ty  ->
    let uu____8917 =
      mlog
        (fun uu____8922  ->
           let uu____8923 = FStar_Syntax_Print.term_to_string ty  in
           FStar_Util.print1 "change: ty = %s\n" uu____8923)
        (fun uu____8926  ->
           let uu____8927 = cur_goal ()  in
           bind uu____8927
             (fun g  ->
                let uu____8933 = __tc g.FStar_Tactics_Types.context ty  in
                bind uu____8933
                  (fun uu____8953  ->
                     match uu____8953 with
                     | (ty1,uu____8963,guard) ->
                         let uu____8965 =
                           proc_guard "change" g.FStar_Tactics_Types.context
                             guard g.FStar_Tactics_Types.opts
                            in
                         bind uu____8965
                           (fun uu____8970  ->
                              let uu____8971 =
                                do_unify g.FStar_Tactics_Types.context
                                  g.FStar_Tactics_Types.goal_ty ty1
                                 in
                              bind uu____8971
                                (fun bb  ->
                                   if bb
                                   then
                                     replace_cur
                                       (let uu___128_8980 = g  in
                                        {
                                          FStar_Tactics_Types.context =
                                            (uu___128_8980.FStar_Tactics_Types.context);
                                          FStar_Tactics_Types.witness =
                                            (uu___128_8980.FStar_Tactics_Types.witness);
                                          FStar_Tactics_Types.goal_ty = ty1;
                                          FStar_Tactics_Types.opts =
                                            (uu___128_8980.FStar_Tactics_Types.opts);
                                          FStar_Tactics_Types.is_guard =
                                            (uu___128_8980.FStar_Tactics_Types.is_guard)
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
                                      let uu____8987 =
                                        do_unify
                                          g.FStar_Tactics_Types.context ng
                                          nty
                                         in
                                      bind uu____8987
                                        (fun b  ->
                                           if b
                                           then
                                             replace_cur
                                               (let uu___129_8996 = g  in
                                                {
                                                  FStar_Tactics_Types.context
                                                    =
                                                    (uu___129_8996.FStar_Tactics_Types.context);
                                                  FStar_Tactics_Types.witness
                                                    =
                                                    (uu___129_8996.FStar_Tactics_Types.witness);
                                                  FStar_Tactics_Types.goal_ty
                                                    = ty1;
                                                  FStar_Tactics_Types.opts =
                                                    (uu___129_8996.FStar_Tactics_Types.opts);
                                                  FStar_Tactics_Types.is_guard
                                                    =
                                                    (uu___129_8996.FStar_Tactics_Types.is_guard)
                                                })
                                           else fail "not convertible")))))))
       in
    FStar_All.pipe_left (wrap_err "change") uu____8917
  
let rec last : 'a . 'a Prims.list -> 'a =
  fun l  ->
    match l with
    | [] -> failwith "last: empty list"
    | x::[] -> x
    | uu____9018::xs -> last xs
  
let rec init : 'a . 'a Prims.list -> 'a Prims.list =
  fun l  ->
    match l with
    | [] -> failwith "init: empty list"
    | x::[] -> []
    | x::xs -> let uu____9046 = init xs  in x :: uu____9046
  
let rec (inspect :
  FStar_Syntax_Syntax.term -> FStar_Reflection_Data.term_view tac) =
  fun t  ->
    let t1 = FStar_Syntax_Util.unascribe t  in
    let t2 = FStar_Syntax_Util.un_uinst t1  in
    match t2.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_meta (t3,uu____9063) -> inspect t3
    | FStar_Syntax_Syntax.Tm_name bv ->
        FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_Var bv)
    | FStar_Syntax_Syntax.Tm_bvar bv ->
        FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_BVar bv)
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_FVar fv)
    | FStar_Syntax_Syntax.Tm_app (hd1,[]) ->
        failwith "inspect: empty arguments on Tm_app"
    | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
        let uu____9120 = last args  in
        (match uu____9120 with
         | (a,q) ->
             let q' = FStar_Reflection_Basic.inspect_aqual q  in
             let uu____9142 =
               let uu____9143 =
                 let uu____9148 =
                   let uu____9151 =
                     let uu____9154 = init args  in
                     FStar_Syntax_Syntax.mk_Tm_app hd1 uu____9154  in
                   uu____9151 FStar_Pervasives_Native.None
                     t2.FStar_Syntax_Syntax.pos
                    in
                 (uu____9148, (a, q'))  in
               FStar_Reflection_Data.Tv_App uu____9143  in
             FStar_All.pipe_left ret uu____9142)
    | FStar_Syntax_Syntax.Tm_abs ([],uu____9175,uu____9176) ->
        failwith "inspect: empty arguments on Tm_abs"
    | FStar_Syntax_Syntax.Tm_abs (bs,t3,k) ->
        let uu____9220 = FStar_Syntax_Subst.open_term bs t3  in
        (match uu____9220 with
         | (bs1,t4) ->
             (match bs1 with
              | [] -> failwith "impossible"
              | b::bs2 ->
                  let uu____9253 =
                    let uu____9254 =
                      let uu____9259 = FStar_Syntax_Util.abs bs2 t4 k  in
                      (b, uu____9259)  in
                    FStar_Reflection_Data.Tv_Abs uu____9254  in
                  FStar_All.pipe_left ret uu____9253))
    | FStar_Syntax_Syntax.Tm_type uu____9266 ->
        FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_Type ())
    | FStar_Syntax_Syntax.Tm_arrow ([],k) ->
        failwith "inspect: empty binders on arrow"
    | FStar_Syntax_Syntax.Tm_arrow uu____9286 ->
        let uu____9299 = FStar_Syntax_Util.arrow_one t2  in
        (match uu____9299 with
         | FStar_Pervasives_Native.Some (b,c) ->
             FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_Arrow (b, c))
         | FStar_Pervasives_Native.None  -> failwith "impossible")
    | FStar_Syntax_Syntax.Tm_refine (bv,t3) ->
        let b = FStar_Syntax_Syntax.mk_binder bv  in
        let uu____9329 = FStar_Syntax_Subst.open_term [b] t3  in
        (match uu____9329 with
         | (b',t4) ->
             let b1 =
               match b' with
               | b'1::[] -> b'1
               | uu____9360 -> failwith "impossible"  in
             FStar_All.pipe_left ret
               (FStar_Reflection_Data.Tv_Refine
                  ((FStar_Pervasives_Native.fst b1), t4)))
    | FStar_Syntax_Syntax.Tm_constant c ->
        let uu____9368 =
          let uu____9369 = FStar_Reflection_Basic.inspect_const c  in
          FStar_Reflection_Data.Tv_Const uu____9369  in
        FStar_All.pipe_left ret uu____9368
    | FStar_Syntax_Syntax.Tm_uvar (u,t3) ->
        let uu____9398 =
          let uu____9399 =
            let uu____9404 =
              let uu____9405 = FStar_Syntax_Unionfind.uvar_id u  in
              FStar_BigInt.of_int_fs uu____9405  in
            (uu____9404, t3)  in
          FStar_Reflection_Data.Tv_Uvar uu____9399  in
        FStar_All.pipe_left ret uu____9398
    | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),t21) ->
        if lb.FStar_Syntax_Syntax.lbunivs <> []
        then FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown
        else
          (match lb.FStar_Syntax_Syntax.lbname with
           | FStar_Util.Inr uu____9433 ->
               FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown
           | FStar_Util.Inl bv ->
               let b = FStar_Syntax_Syntax.mk_binder bv  in
               let uu____9438 = FStar_Syntax_Subst.open_term [b] t21  in
               (match uu____9438 with
                | (bs,t22) ->
                    let b1 =
                      match bs with
                      | b1::[] -> b1
                      | uu____9469 ->
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
           | FStar_Util.Inr uu____9501 ->
               FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown
           | FStar_Util.Inl bv ->
               let uu____9505 = FStar_Syntax_Subst.open_let_rec [lb] t21  in
               (match uu____9505 with
                | (lbs,t22) ->
                    (match lbs with
                     | lb1::[] ->
                         (match lb1.FStar_Syntax_Syntax.lbname with
                          | FStar_Util.Inr uu____9525 ->
                              ret FStar_Reflection_Data.Tv_Unknown
                          | FStar_Util.Inl bv1 ->
                              FStar_All.pipe_left ret
                                (FStar_Reflection_Data.Tv_Let
                                   (true, bv1,
                                     (lb1.FStar_Syntax_Syntax.lbdef), t22)))
                     | uu____9531 ->
                         failwith
                           "impossible: open_term returned different amount of binders")))
    | FStar_Syntax_Syntax.Tm_match (t3,brs) ->
        let rec inspect_pat p =
          match p.FStar_Syntax_Syntax.v with
          | FStar_Syntax_Syntax.Pat_constant c ->
              let uu____9584 = FStar_Reflection_Basic.inspect_const c  in
              FStar_Reflection_Data.Pat_Constant uu____9584
          | FStar_Syntax_Syntax.Pat_cons (fv,ps) ->
              let uu____9603 =
                let uu____9610 =
                  FStar_List.map
                    (fun uu____9622  ->
                       match uu____9622 with
                       | (p1,uu____9630) -> inspect_pat p1) ps
                   in
                (fv, uu____9610)  in
              FStar_Reflection_Data.Pat_Cons uu____9603
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
            (fun uu___63_9684  ->
               match uu___63_9684 with
               | (pat,uu____9706,t4) ->
                   let uu____9724 = inspect_pat pat  in (uu____9724, t4))
            brs1
           in
        FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_Match (t3, brs2))
    | FStar_Syntax_Syntax.Tm_unknown  ->
        FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown
    | uu____9741 ->
        let uu____9742 =
          let uu____9743 =
            let uu____9748 =
              let uu____9749 = FStar_Syntax_Print.tag_of_term t2  in
              let uu____9750 = FStar_Syntax_Print.term_to_string t2  in
              FStar_Util.format2
                "inspect: outside of expected syntax (%s, %s)\n" uu____9749
                uu____9750
               in
            (FStar_Errors.Warning_CantInspect, uu____9748)  in
          FStar_Errors.log_issue t2.FStar_Syntax_Syntax.pos uu____9743  in
        FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown
  
let (pack : FStar_Reflection_Data.term_view -> FStar_Syntax_Syntax.term tac)
  =
  fun tv  ->
    match tv with
    | FStar_Reflection_Data.Tv_Var bv ->
        let uu____9763 = FStar_Syntax_Syntax.bv_to_name bv  in
        FStar_All.pipe_left ret uu____9763
    | FStar_Reflection_Data.Tv_BVar bv ->
        let uu____9767 = FStar_Syntax_Syntax.bv_to_tm bv  in
        FStar_All.pipe_left ret uu____9767
    | FStar_Reflection_Data.Tv_FVar fv ->
        let uu____9771 = FStar_Syntax_Syntax.fv_to_tm fv  in
        FStar_All.pipe_left ret uu____9771
    | FStar_Reflection_Data.Tv_App (l,(r,q)) ->
        let q' = FStar_Reflection_Basic.pack_aqual q  in
        let uu____9782 = FStar_Syntax_Util.mk_app l [(r, q')]  in
        FStar_All.pipe_left ret uu____9782
    | FStar_Reflection_Data.Tv_Abs (b,t) ->
        let uu____9803 =
          FStar_Syntax_Util.abs [b] t FStar_Pervasives_Native.None  in
        FStar_All.pipe_left ret uu____9803
    | FStar_Reflection_Data.Tv_Arrow (b,c) ->
        let uu____9808 = FStar_Syntax_Util.arrow [b] c  in
        FStar_All.pipe_left ret uu____9808
    | FStar_Reflection_Data.Tv_Type () ->
        FStar_All.pipe_left ret FStar_Syntax_Util.ktype
    | FStar_Reflection_Data.Tv_Refine (bv,t) ->
        let uu____9829 = FStar_Syntax_Util.refine bv t  in
        FStar_All.pipe_left ret uu____9829
    | FStar_Reflection_Data.Tv_Const c ->
        let uu____9841 =
          let uu____9844 =
            let uu____9849 =
              let uu____9850 = FStar_Reflection_Basic.pack_const c  in
              FStar_Syntax_Syntax.Tm_constant uu____9850  in
            FStar_Syntax_Syntax.mk uu____9849  in
          uu____9844 FStar_Pervasives_Native.None FStar_Range.dummyRange  in
        FStar_All.pipe_left ret uu____9841
    | FStar_Reflection_Data.Tv_Uvar (u,t) ->
        let uu____9864 =
          let uu____9867 = FStar_BigInt.to_int_fs u  in
          FStar_Syntax_Util.uvar_from_id uu____9867 t  in
        FStar_All.pipe_left ret uu____9864
    | FStar_Reflection_Data.Tv_Let (false ,bv,t1,t2) ->
        let lb =
          FStar_Syntax_Util.mk_letbinding (FStar_Util.Inl bv) []
            bv.FStar_Syntax_Syntax.sort FStar_Parser_Const.effect_Tot_lid t1
            [] FStar_Range.dummyRange
           in
        let uu____9882 =
          let uu____9885 =
            let uu____9890 =
              let uu____9891 =
                let uu____9904 =
                  let uu____9905 =
                    let uu____9906 = FStar_Syntax_Syntax.mk_binder bv  in
                    [uu____9906]  in
                  FStar_Syntax_Subst.close uu____9905 t2  in
                ((false, [lb]), uu____9904)  in
              FStar_Syntax_Syntax.Tm_let uu____9891  in
            FStar_Syntax_Syntax.mk uu____9890  in
          uu____9885 FStar_Pervasives_Native.None FStar_Range.dummyRange  in
        FStar_All.pipe_left ret uu____9882
    | FStar_Reflection_Data.Tv_Let (true ,bv,t1,t2) ->
        let lb =
          FStar_Syntax_Util.mk_letbinding (FStar_Util.Inl bv) []
            bv.FStar_Syntax_Syntax.sort FStar_Parser_Const.effect_Tot_lid t1
            [] FStar_Range.dummyRange
           in
        let uu____9932 = FStar_Syntax_Subst.close_let_rec [lb] t2  in
        (match uu____9932 with
         | (lbs,body) ->
             let uu____9947 =
               FStar_Syntax_Syntax.mk
                 (FStar_Syntax_Syntax.Tm_let ((true, lbs), body))
                 FStar_Pervasives_Native.None FStar_Range.dummyRange
                in
             FStar_All.pipe_left ret uu____9947)
    | FStar_Reflection_Data.Tv_Match (t,brs) ->
        let wrap v1 =
          {
            FStar_Syntax_Syntax.v = v1;
            FStar_Syntax_Syntax.p = FStar_Range.dummyRange
          }  in
        let rec pack_pat p =
          match p with
          | FStar_Reflection_Data.Pat_Constant c ->
              let uu____9985 =
                let uu____9986 = FStar_Reflection_Basic.pack_const c  in
                FStar_Syntax_Syntax.Pat_constant uu____9986  in
              FStar_All.pipe_left wrap uu____9985
          | FStar_Reflection_Data.Pat_Cons (fv,ps) ->
              let uu____9995 =
                let uu____9996 =
                  let uu____10009 =
                    FStar_List.map
                      (fun p1  ->
                         let uu____10023 = pack_pat p1  in
                         (uu____10023, false)) ps
                     in
                  (fv, uu____10009)  in
                FStar_Syntax_Syntax.Pat_cons uu____9996  in
              FStar_All.pipe_left wrap uu____9995
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
            (fun uu___64_10073  ->
               match uu___64_10073 with
               | (pat,t1) ->
                   let uu____10090 = pack_pat pat  in
                   (uu____10090, FStar_Pervasives_Native.None, t1)) brs
           in
        let brs2 = FStar_List.map FStar_Syntax_Subst.close_branch brs1  in
        let uu____10100 =
          FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_match (t, brs2))
            FStar_Pervasives_Native.None FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____10100
    | FStar_Reflection_Data.Tv_AscribedT (e,t,tacopt) ->
        let uu____10120 =
          FStar_Syntax_Syntax.mk
            (FStar_Syntax_Syntax.Tm_ascribed
               (e, ((FStar_Util.Inl t), tacopt),
                 FStar_Pervasives_Native.None)) FStar_Pervasives_Native.None
            FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____10120
    | FStar_Reflection_Data.Tv_AscribedC (e,c,tacopt) ->
        let uu____10162 =
          FStar_Syntax_Syntax.mk
            (FStar_Syntax_Syntax.Tm_ascribed
               (e, ((FStar_Util.Inr c), tacopt),
                 FStar_Pervasives_Native.None)) FStar_Pervasives_Native.None
            FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____10162
    | FStar_Reflection_Data.Tv_Unknown  ->
        let uu____10197 =
          FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown
            FStar_Pervasives_Native.None FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____10197
  
let (goal_of_goal_ty :
  env ->
    FStar_Reflection_Data.typ ->
      (FStar_Tactics_Types.goal,FStar_TypeChecker_Env.guard_t)
        FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun typ  ->
      let uu____10226 =
        FStar_TypeChecker_Util.new_implicit_var "proofstate_of_goal_ty"
          typ.FStar_Syntax_Syntax.pos env typ
         in
      match uu____10226 with
      | (u,uu____10244,g_u) ->
          let g =
            let uu____10259 = FStar_Options.peek ()  in
            {
              FStar_Tactics_Types.context = env;
              FStar_Tactics_Types.witness = u;
              FStar_Tactics_Types.goal_ty = typ;
              FStar_Tactics_Types.opts = uu____10259;
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
      let uu____10274 = goal_of_goal_ty env typ  in
      match uu____10274 with
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
  