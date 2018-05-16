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
        let uu____489 =
          let uu____492 =
            let uu____493 =
              FStar_Util.string_of_int ps.FStar_Tactics_Types.depth  in
            FStar_Util.format2 "State dump @ depth %s (%s):\n" uu____493 msg
             in
          let uu____494 =
            let uu____497 =
              if ps.FStar_Tactics_Types.entry_range <> FStar_Range.dummyRange
              then
                let uu____498 =
                  FStar_Range.string_of_def_range
                    ps.FStar_Tactics_Types.entry_range
                   in
                FStar_Util.format1 "Location: %s\n" uu____498
              else ""  in
            let uu____500 =
              let uu____503 =
                let uu____504 =
                  FStar_Util.string_of_int
                    (FStar_List.length ps.FStar_Tactics_Types.goals)
                   in
                let uu____505 =
                  let uu____506 =
                    FStar_List.map (goal_to_string ps)
                      ps.FStar_Tactics_Types.goals
                     in
                  FStar_String.concat "\n" uu____506  in
                FStar_Util.format2 "ACTIVE goals (%s):\n%s\n" uu____504
                  uu____505
                 in
              let uu____509 =
                let uu____512 =
                  let uu____513 =
                    FStar_Util.string_of_int
                      (FStar_List.length ps.FStar_Tactics_Types.smt_goals)
                     in
                  let uu____514 =
                    let uu____515 =
                      FStar_List.map (goal_to_string ps)
                        ps.FStar_Tactics_Types.smt_goals
                       in
                    FStar_String.concat "\n" uu____515  in
                  FStar_Util.format2 "SMT goals (%s):\n%s\n" uu____513
                    uu____514
                   in
                [uu____512]  in
              uu____503 :: uu____509  in
            uu____497 :: uu____500  in
          uu____492 :: uu____494  in
        FStar_String.concat "" uu____489
  
let (goal_to_json : FStar_Tactics_Types.goal -> FStar_Util.json) =
  fun g  ->
    let g_binders =
      let uu____524 =
        let uu____525 = FStar_Tactics_Types.goal_env g  in
        FStar_TypeChecker_Env.all_binders uu____525  in
      let uu____526 =
        let uu____531 =
          let uu____532 = FStar_Tactics_Types.goal_env g  in
          FStar_TypeChecker_Env.dsenv uu____532  in
        FStar_Syntax_Print.binders_to_json uu____531  in
      FStar_All.pipe_right uu____524 uu____526  in
    let uu____533 =
      let uu____540 =
        let uu____547 =
          let uu____552 =
            let uu____553 =
              let uu____560 =
                let uu____565 =
                  let uu____566 =
                    let uu____567 = FStar_Tactics_Types.goal_env g  in
                    let uu____568 = FStar_Tactics_Types.goal_witness g  in
                    tts uu____567 uu____568  in
                  FStar_Util.JsonStr uu____566  in
                ("witness", uu____565)  in
              let uu____569 =
                let uu____576 =
                  let uu____581 =
                    let uu____582 =
                      let uu____583 = FStar_Tactics_Types.goal_env g  in
                      let uu____584 = FStar_Tactics_Types.goal_type g  in
                      tts uu____583 uu____584  in
                    FStar_Util.JsonStr uu____582  in
                  ("type", uu____581)  in
                [uu____576]  in
              uu____560 :: uu____569  in
            FStar_Util.JsonAssoc uu____553  in
          ("goal", uu____552)  in
        [uu____547]  in
      ("hyps", g_binders) :: uu____540  in
    FStar_Util.JsonAssoc uu____533
  
let (ps_to_json :
  (Prims.string,FStar_Tactics_Types.proofstate)
    FStar_Pervasives_Native.tuple2 -> FStar_Util.json)
  =
  fun uu____617  ->
    match uu____617 with
    | (msg,ps) ->
        let uu____624 =
          let uu____631 =
            let uu____638 =
              let uu____645 =
                let uu____652 =
                  let uu____657 =
                    let uu____658 =
                      FStar_List.map goal_to_json
                        ps.FStar_Tactics_Types.goals
                       in
                    FStar_Util.JsonList uu____658  in
                  ("goals", uu____657)  in
                let uu____661 =
                  let uu____668 =
                    let uu____673 =
                      let uu____674 =
                        FStar_List.map goal_to_json
                          ps.FStar_Tactics_Types.smt_goals
                         in
                      FStar_Util.JsonList uu____674  in
                    ("smt-goals", uu____673)  in
                  [uu____668]  in
                uu____652 :: uu____661  in
              ("depth", (FStar_Util.JsonInt (ps.FStar_Tactics_Types.depth)))
                :: uu____645
               in
            ("label", (FStar_Util.JsonStr msg)) :: uu____638  in
          let uu____697 =
            if ps.FStar_Tactics_Types.entry_range <> FStar_Range.dummyRange
            then
              let uu____710 =
                let uu____715 =
                  FStar_Range.json_of_def_range
                    ps.FStar_Tactics_Types.entry_range
                   in
                ("location", uu____715)  in
              [uu____710]
            else []  in
          FStar_List.append uu____631 uu____697  in
        FStar_Util.JsonAssoc uu____624
  
let (dump_proofstate :
  FStar_Tactics_Types.proofstate -> Prims.string -> unit) =
  fun ps  ->
    fun msg  ->
      FStar_Options.with_saved_options
        (fun uu____745  ->
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
         (let uu____768 = FStar_Tactics_Types.subst_proof_state subst1 ps  in
          dump_cur uu____768 msg);
         FStar_Tactics_Result.Success ((), ps))
  
let (print_proof_state : Prims.string -> unit tac) =
  fun msg  ->
    mk_tac
      (fun ps  ->
         let psc = ps.FStar_Tactics_Types.psc  in
         let subst1 = FStar_TypeChecker_Normalize.psc_subst psc  in
         (let uu____786 = FStar_Tactics_Types.subst_proof_state subst1 ps  in
          dump_proofstate uu____786 msg);
         FStar_Tactics_Result.Success ((), ps))
  
let mlog : 'a . (unit -> unit) -> (unit -> 'a tac) -> 'a tac =
  fun f  -> fun cont  -> bind get (fun ps  -> log ps f; cont ()) 
let fail : 'a . Prims.string -> 'a tac =
  fun msg  ->
    mk_tac
      (fun ps  ->
         (let uu____840 =
            FStar_TypeChecker_Env.debug ps.FStar_Tactics_Types.main_context
              (FStar_Options.Other "TacFail")
             in
          if uu____840
          then dump_proofstate ps (Prims.strcat "TACTIC FAILING: " msg)
          else ());
         FStar_Tactics_Result.Failed (msg, ps))
  
let fail1 : 'Auu____848 . Prims.string -> Prims.string -> 'Auu____848 tac =
  fun msg  ->
    fun x  -> let uu____861 = FStar_Util.format1 msg x  in fail uu____861
  
let fail2 :
  'Auu____870 .
    Prims.string -> Prims.string -> Prims.string -> 'Auu____870 tac
  =
  fun msg  ->
    fun x  ->
      fun y  -> let uu____888 = FStar_Util.format2 msg x y  in fail uu____888
  
let fail3 :
  'Auu____899 .
    Prims.string ->
      Prims.string -> Prims.string -> Prims.string -> 'Auu____899 tac
  =
  fun msg  ->
    fun x  ->
      fun y  ->
        fun z  ->
          let uu____922 = FStar_Util.format3 msg x y z  in fail uu____922
  
let fail4 :
  'Auu____935 .
    Prims.string ->
      Prims.string ->
        Prims.string -> Prims.string -> Prims.string -> 'Auu____935 tac
  =
  fun msg  ->
    fun x  ->
      fun y  ->
        fun z  ->
          fun w  ->
            let uu____963 = FStar_Util.format4 msg x y z w  in fail uu____963
  
let trytac' : 'a . 'a tac -> (Prims.string,'a) FStar_Util.either tac =
  fun t  ->
    mk_tac
      (fun ps  ->
         let tx = FStar_Syntax_Unionfind.new_transaction ()  in
         let uu____996 = run t ps  in
         match uu____996 with
         | FStar_Tactics_Result.Success (a,q) ->
             (FStar_Syntax_Unionfind.commit tx;
              FStar_Tactics_Result.Success ((FStar_Util.Inr a), q))
         | FStar_Tactics_Result.Failed (m,q) ->
             (FStar_Syntax_Unionfind.rollback tx;
              (let ps1 =
                 let uu___342_1020 = ps  in
                 {
                   FStar_Tactics_Types.main_context =
                     (uu___342_1020.FStar_Tactics_Types.main_context);
                   FStar_Tactics_Types.main_goal =
                     (uu___342_1020.FStar_Tactics_Types.main_goal);
                   FStar_Tactics_Types.all_implicits =
                     (uu___342_1020.FStar_Tactics_Types.all_implicits);
                   FStar_Tactics_Types.goals =
                     (uu___342_1020.FStar_Tactics_Types.goals);
                   FStar_Tactics_Types.smt_goals =
                     (uu___342_1020.FStar_Tactics_Types.smt_goals);
                   FStar_Tactics_Types.depth =
                     (uu___342_1020.FStar_Tactics_Types.depth);
                   FStar_Tactics_Types.__dump =
                     (uu___342_1020.FStar_Tactics_Types.__dump);
                   FStar_Tactics_Types.psc =
                     (uu___342_1020.FStar_Tactics_Types.psc);
                   FStar_Tactics_Types.entry_range =
                     (uu___342_1020.FStar_Tactics_Types.entry_range);
                   FStar_Tactics_Types.guard_policy =
                     (uu___342_1020.FStar_Tactics_Types.guard_policy);
                   FStar_Tactics_Types.freshness =
                     (q.FStar_Tactics_Types.freshness);
                   FStar_Tactics_Types.tac_verb_dbg =
                     (uu___342_1020.FStar_Tactics_Types.tac_verb_dbg)
                 }  in
               FStar_Tactics_Result.Success ((FStar_Util.Inl m), ps1))))
  
let trytac : 'a . 'a tac -> 'a FStar_Pervasives_Native.option tac =
  fun t  ->
    let uu____1047 = trytac' t  in
    bind uu____1047
      (fun r  ->
         match r with
         | FStar_Util.Inr v1 -> ret (FStar_Pervasives_Native.Some v1)
         | FStar_Util.Inl uu____1074 -> ret FStar_Pervasives_Native.None)
  
let trytac_exn : 'a . 'a tac -> 'a FStar_Pervasives_Native.option tac =
  fun t  ->
    mk_tac
      (fun ps  ->
         try let uu____1110 = trytac t  in run uu____1110 ps
         with
         | FStar_Errors.Err (uu____1126,msg) ->
             (log ps
                (fun uu____1130  ->
                   FStar_Util.print1 "trytac_exn error: (%s)" msg);
              FStar_Tactics_Result.Success (FStar_Pervasives_Native.None, ps))
         | FStar_Errors.Error (uu____1135,msg,uu____1137) ->
             (log ps
                (fun uu____1140  ->
                   FStar_Util.print1 "trytac_exn error: (%s)" msg);
              FStar_Tactics_Result.Success (FStar_Pervasives_Native.None, ps)))
  
let wrap_err : 'a . Prims.string -> 'a tac -> 'a tac =
  fun pref  ->
    fun t  ->
      mk_tac
        (fun ps  ->
           let uu____1173 = run t ps  in
           match uu____1173 with
           | FStar_Tactics_Result.Success (a,q) ->
               FStar_Tactics_Result.Success (a, q)
           | FStar_Tactics_Result.Failed (msg,q) ->
               FStar_Tactics_Result.Failed
                 ((Prims.strcat pref (Prims.strcat ": " msg)), q))
  
let (set : FStar_Tactics_Types.proofstate -> unit tac) =
  fun p  -> mk_tac (fun uu____1192  -> FStar_Tactics_Result.Success ((), p)) 
let (__do_unify :
  env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.bool tac)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        (let uu____1213 =
           FStar_TypeChecker_Env.debug env (FStar_Options.Other "1346")  in
         if uu____1213
         then
           let uu____1214 = FStar_Syntax_Print.term_to_string t1  in
           let uu____1215 = FStar_Syntax_Print.term_to_string t2  in
           FStar_Util.print2 "%%%%%%%%do_unify %s =? %s\n" uu____1214
             uu____1215
         else ());
        (try
           let res = FStar_TypeChecker_Rel.teq_nosmt env t1 t2  in
           (let uu____1227 =
              FStar_TypeChecker_Env.debug env (FStar_Options.Other "1346")
               in
            if uu____1227
            then
              let uu____1228 = FStar_Util.string_of_bool res  in
              let uu____1229 = FStar_Syntax_Print.term_to_string t1  in
              let uu____1230 = FStar_Syntax_Print.term_to_string t2  in
              FStar_Util.print3 "%%%%%%%%do_unify (RESULT %s) %s =? %s\n"
                uu____1228 uu____1229 uu____1230
            else ());
           ret res
         with
         | FStar_Errors.Err (uu____1238,msg) ->
             mlog
               (fun uu____1241  ->
                  FStar_Util.print1 ">> do_unify error, (%s)\n" msg)
               (fun uu____1243  -> ret false)
         | FStar_Errors.Error (uu____1244,msg,r) ->
             mlog
               (fun uu____1249  ->
                  let uu____1250 = FStar_Range.string_of_range r  in
                  FStar_Util.print2 ">> do_unify error, (%s) at (%s)\n" msg
                    uu____1250) (fun uu____1252  -> ret false))
  
let (do_unify :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.bool tac)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        bind idtac
          (fun uu____1275  ->
             (let uu____1277 =
                FStar_TypeChecker_Env.debug env (FStar_Options.Other "1346")
                 in
              if uu____1277
              then
                (FStar_Options.push ();
                 (let uu____1279 =
                    FStar_Options.set_options FStar_Options.Set
                      "--debug_level Rel --debug_level RelCheck"
                     in
                  ()))
              else ());
             (let uu____1281 =
                let uu____1284 = __do_unify env t1 t2  in
                bind uu____1284
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
              bind uu____1281
                (fun r  ->
                   (let uu____1300 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "1346")
                       in
                    if uu____1300 then FStar_Options.pop () else ());
                   ret r)))
  
let (remove_solved_goals : unit tac) =
  bind get
    (fun ps  ->
       let ps' =
         let uu___347_1308 = ps  in
         let uu____1309 =
           FStar_List.filter
             (fun g  ->
                let uu____1315 = check_goal_solved g  in
                FStar_Option.isNone uu____1315) ps.FStar_Tactics_Types.goals
            in
         {
           FStar_Tactics_Types.main_context =
             (uu___347_1308.FStar_Tactics_Types.main_context);
           FStar_Tactics_Types.main_goal =
             (uu___347_1308.FStar_Tactics_Types.main_goal);
           FStar_Tactics_Types.all_implicits =
             (uu___347_1308.FStar_Tactics_Types.all_implicits);
           FStar_Tactics_Types.goals = uu____1309;
           FStar_Tactics_Types.smt_goals =
             (uu___347_1308.FStar_Tactics_Types.smt_goals);
           FStar_Tactics_Types.depth =
             (uu___347_1308.FStar_Tactics_Types.depth);
           FStar_Tactics_Types.__dump =
             (uu___347_1308.FStar_Tactics_Types.__dump);
           FStar_Tactics_Types.psc = (uu___347_1308.FStar_Tactics_Types.psc);
           FStar_Tactics_Types.entry_range =
             (uu___347_1308.FStar_Tactics_Types.entry_range);
           FStar_Tactics_Types.guard_policy =
             (uu___347_1308.FStar_Tactics_Types.guard_policy);
           FStar_Tactics_Types.freshness =
             (uu___347_1308.FStar_Tactics_Types.freshness);
           FStar_Tactics_Types.tac_verb_dbg =
             (uu___347_1308.FStar_Tactics_Types.tac_verb_dbg)
         }  in
       set ps')
  
let (set_solution :
  FStar_Tactics_Types.goal -> FStar_Syntax_Syntax.term -> unit tac) =
  fun goal  ->
    fun solution  ->
      let uu____1332 =
        FStar_Syntax_Unionfind.find
          (goal.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_head
         in
      match uu____1332 with
      | FStar_Pervasives_Native.Some uu____1337 ->
          let uu____1338 =
            let uu____1339 = goal_to_string_verbose goal  in
            FStar_Util.format1 "Goal %s is already solved" uu____1339  in
          fail uu____1338
      | FStar_Pervasives_Native.None  ->
          (FStar_Syntax_Unionfind.change
             (goal.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_head
             solution;
           ret ())
  
let (trysolve :
  FStar_Tactics_Types.goal -> FStar_Syntax_Syntax.term -> Prims.bool tac) =
  fun goal  ->
    fun solution  ->
      let uu____1355 = FStar_Tactics_Types.goal_env goal  in
      let uu____1356 = FStar_Tactics_Types.goal_witness goal  in
      do_unify uu____1355 solution uu____1356
  
let (__dismiss : unit tac) =
  bind get
    (fun p  ->
       let uu____1362 =
         let uu___348_1363 = p  in
         let uu____1364 = FStar_List.tl p.FStar_Tactics_Types.goals  in
         {
           FStar_Tactics_Types.main_context =
             (uu___348_1363.FStar_Tactics_Types.main_context);
           FStar_Tactics_Types.main_goal =
             (uu___348_1363.FStar_Tactics_Types.main_goal);
           FStar_Tactics_Types.all_implicits =
             (uu___348_1363.FStar_Tactics_Types.all_implicits);
           FStar_Tactics_Types.goals = uu____1364;
           FStar_Tactics_Types.smt_goals =
             (uu___348_1363.FStar_Tactics_Types.smt_goals);
           FStar_Tactics_Types.depth =
             (uu___348_1363.FStar_Tactics_Types.depth);
           FStar_Tactics_Types.__dump =
             (uu___348_1363.FStar_Tactics_Types.__dump);
           FStar_Tactics_Types.psc = (uu___348_1363.FStar_Tactics_Types.psc);
           FStar_Tactics_Types.entry_range =
             (uu___348_1363.FStar_Tactics_Types.entry_range);
           FStar_Tactics_Types.guard_policy =
             (uu___348_1363.FStar_Tactics_Types.guard_policy);
           FStar_Tactics_Types.freshness =
             (uu___348_1363.FStar_Tactics_Types.freshness);
           FStar_Tactics_Types.tac_verb_dbg =
             (uu___348_1363.FStar_Tactics_Types.tac_verb_dbg)
         }  in
       set uu____1362)
  
let (dismiss : unit -> unit tac) =
  fun uu____1373  ->
    bind get
      (fun p  ->
         match p.FStar_Tactics_Types.goals with
         | [] -> fail "dismiss: no more goals"
         | uu____1380 -> __dismiss)
  
let (solve :
  FStar_Tactics_Types.goal -> FStar_Syntax_Syntax.term -> unit tac) =
  fun goal  ->
    fun solution  ->
      let e = FStar_Tactics_Types.goal_env goal  in
      mlog
        (fun uu____1401  ->
           let uu____1402 =
             let uu____1403 = FStar_Tactics_Types.goal_witness goal  in
             FStar_Syntax_Print.term_to_string uu____1403  in
           let uu____1404 = FStar_Syntax_Print.term_to_string solution  in
           FStar_Util.print2 "solve %s := %s\n" uu____1402 uu____1404)
        (fun uu____1407  ->
           let uu____1408 = trysolve goal solution  in
           bind uu____1408
             (fun b  ->
                if b
                then bind __dismiss (fun uu____1416  -> remove_solved_goals)
                else
                  (let uu____1418 =
                     let uu____1419 =
                       let uu____1420 = FStar_Tactics_Types.goal_env goal  in
                       tts uu____1420 solution  in
                     let uu____1421 =
                       let uu____1422 = FStar_Tactics_Types.goal_env goal  in
                       let uu____1423 = FStar_Tactics_Types.goal_witness goal
                          in
                       tts uu____1422 uu____1423  in
                     let uu____1424 =
                       let uu____1425 = FStar_Tactics_Types.goal_env goal  in
                       let uu____1426 = FStar_Tactics_Types.goal_type goal
                          in
                       tts uu____1425 uu____1426  in
                     FStar_Util.format3 "%s does not solve %s : %s"
                       uu____1419 uu____1421 uu____1424
                      in
                   fail uu____1418)))
  
let (solve' :
  FStar_Tactics_Types.goal -> FStar_Syntax_Syntax.term -> unit tac) =
  fun goal  ->
    fun solution  ->
      let uu____1441 = set_solution goal solution  in
      bind uu____1441
        (fun uu____1445  ->
           bind __dismiss (fun uu____1447  -> remove_solved_goals))
  
let (dismiss_all : unit tac) =
  bind get
    (fun p  ->
       set
         (let uu___349_1454 = p  in
          {
            FStar_Tactics_Types.main_context =
              (uu___349_1454.FStar_Tactics_Types.main_context);
            FStar_Tactics_Types.main_goal =
              (uu___349_1454.FStar_Tactics_Types.main_goal);
            FStar_Tactics_Types.all_implicits =
              (uu___349_1454.FStar_Tactics_Types.all_implicits);
            FStar_Tactics_Types.goals = [];
            FStar_Tactics_Types.smt_goals =
              (uu___349_1454.FStar_Tactics_Types.smt_goals);
            FStar_Tactics_Types.depth =
              (uu___349_1454.FStar_Tactics_Types.depth);
            FStar_Tactics_Types.__dump =
              (uu___349_1454.FStar_Tactics_Types.__dump);
            FStar_Tactics_Types.psc = (uu___349_1454.FStar_Tactics_Types.psc);
            FStar_Tactics_Types.entry_range =
              (uu___349_1454.FStar_Tactics_Types.entry_range);
            FStar_Tactics_Types.guard_policy =
              (uu___349_1454.FStar_Tactics_Types.guard_policy);
            FStar_Tactics_Types.freshness =
              (uu___349_1454.FStar_Tactics_Types.freshness);
            FStar_Tactics_Types.tac_verb_dbg =
              (uu___349_1454.FStar_Tactics_Types.tac_verb_dbg)
          }))
  
let (nwarn : Prims.int FStar_ST.ref) =
  FStar_Util.mk_ref (Prims.parse_int "0") 
let (check_valid_goal : FStar_Tactics_Types.goal -> unit) =
  fun g  ->
    let uu____1473 = FStar_Options.defensive ()  in
    if uu____1473
    then
      let b = true  in
      let env = FStar_Tactics_Types.goal_env g  in
      let b1 =
        b &&
          (let uu____1478 = FStar_Tactics_Types.goal_witness g  in
           FStar_TypeChecker_Env.closed env uu____1478)
         in
      let b2 =
        b1 &&
          (let uu____1481 = FStar_Tactics_Types.goal_type g  in
           FStar_TypeChecker_Env.closed env uu____1481)
         in
      let rec aux b3 e =
        let uu____1493 = FStar_TypeChecker_Env.pop_bv e  in
        match uu____1493 with
        | FStar_Pervasives_Native.None  -> b3
        | FStar_Pervasives_Native.Some (bv,e1) ->
            let b4 =
              b3 &&
                (FStar_TypeChecker_Env.closed e1 bv.FStar_Syntax_Syntax.sort)
               in
            aux b4 e1
         in
      let uu____1511 =
        (let uu____1514 = aux b2 env  in Prims.op_Negation uu____1514) &&
          (let uu____1516 = FStar_ST.op_Bang nwarn  in
           uu____1516 < (Prims.parse_int "5"))
         in
      (if uu____1511
       then
         ((let uu____1541 =
             let uu____1542 = FStar_Tactics_Types.goal_type g  in
             uu____1542.FStar_Syntax_Syntax.pos  in
           let uu____1545 =
             let uu____1550 =
               let uu____1551 = goal_to_string_verbose g  in
               FStar_Util.format1
                 "The following goal is ill-formed. Keeping calm and carrying on...\n<%s>\n\n"
                 uu____1551
                in
             (FStar_Errors.Warning_IllFormedGoal, uu____1550)  in
           FStar_Errors.log_issue uu____1541 uu____1545);
          (let uu____1552 =
             let uu____1553 = FStar_ST.op_Bang nwarn  in
             uu____1553 + (Prims.parse_int "1")  in
           FStar_ST.op_Colon_Equals nwarn uu____1552))
       else ())
    else ()
  
let (add_goals : FStar_Tactics_Types.goal Prims.list -> unit tac) =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___350_1621 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___350_1621.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___350_1621.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___350_1621.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (FStar_List.append gs p.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (uu___350_1621.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___350_1621.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___350_1621.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___350_1621.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___350_1621.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___350_1621.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___350_1621.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___350_1621.FStar_Tactics_Types.tac_verb_dbg)
            }))
  
let (add_smt_goals : FStar_Tactics_Types.goal Prims.list -> unit tac) =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___351_1641 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___351_1641.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___351_1641.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___351_1641.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___351_1641.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (FStar_List.append gs p.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___351_1641.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___351_1641.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___351_1641.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___351_1641.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___351_1641.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___351_1641.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___351_1641.FStar_Tactics_Types.tac_verb_dbg)
            }))
  
let (push_goals : FStar_Tactics_Types.goal Prims.list -> unit tac) =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___352_1661 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___352_1661.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___352_1661.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___352_1661.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (FStar_List.append p.FStar_Tactics_Types.goals gs);
              FStar_Tactics_Types.smt_goals =
                (uu___352_1661.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___352_1661.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___352_1661.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___352_1661.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___352_1661.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___352_1661.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___352_1661.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___352_1661.FStar_Tactics_Types.tac_verb_dbg)
            }))
  
let (push_smt_goals : FStar_Tactics_Types.goal Prims.list -> unit tac) =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___353_1681 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___353_1681.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___353_1681.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___353_1681.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___353_1681.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (FStar_List.append p.FStar_Tactics_Types.smt_goals gs);
              FStar_Tactics_Types.depth =
                (uu___353_1681.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___353_1681.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___353_1681.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___353_1681.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___353_1681.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___353_1681.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___353_1681.FStar_Tactics_Types.tac_verb_dbg)
            }))
  
let (replace_cur : FStar_Tactics_Types.goal -> unit tac) =
  fun g  -> bind __dismiss (fun uu____1692  -> add_goals [g]) 
let (add_implicits : implicits -> unit tac) =
  fun i  ->
    bind get
      (fun p  ->
         set
           (let uu___354_1706 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___354_1706.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___354_1706.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (FStar_List.append i p.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___354_1706.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (uu___354_1706.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___354_1706.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___354_1706.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___354_1706.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___354_1706.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___354_1706.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___354_1706.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___354_1706.FStar_Tactics_Types.tac_verb_dbg)
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
        let uu____1742 =
          FStar_TypeChecker_Util.new_implicit_var reason
            typ.FStar_Syntax_Syntax.pos env typ
           in
        match uu____1742 with
        | (u,ctx_uvar,g_u) ->
            let uu____1776 =
              add_implicits g_u.FStar_TypeChecker_Env.implicits  in
            bind uu____1776
              (fun uu____1785  ->
                 let uu____1786 =
                   let uu____1791 =
                     let uu____1792 = FStar_List.hd ctx_uvar  in
                     FStar_Pervasives_Native.fst uu____1792  in
                   (u, uu____1791)  in
                 ret uu____1786)
  
let (is_true : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____1810 = FStar_Syntax_Util.un_squash t  in
    match uu____1810 with
    | FStar_Pervasives_Native.Some t' ->
        let uu____1820 =
          let uu____1821 = FStar_Syntax_Subst.compress t'  in
          uu____1821.FStar_Syntax_Syntax.n  in
        (match uu____1820 with
         | FStar_Syntax_Syntax.Tm_fvar fv ->
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.true_lid
         | uu____1825 -> false)
    | uu____1826 -> false
  
let (is_false : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____1836 = FStar_Syntax_Util.un_squash t  in
    match uu____1836 with
    | FStar_Pervasives_Native.Some t' ->
        let uu____1846 =
          let uu____1847 = FStar_Syntax_Subst.compress t'  in
          uu____1847.FStar_Syntax_Syntax.n  in
        (match uu____1846 with
         | FStar_Syntax_Syntax.Tm_fvar fv ->
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.false_lid
         | uu____1851 -> false)
    | uu____1852 -> false
  
let (cur_goal : unit -> FStar_Tactics_Types.goal tac) =
  fun uu____1863  ->
    bind get
      (fun p  ->
         match p.FStar_Tactics_Types.goals with
         | [] -> fail "No more goals (1)"
         | hd1::tl1 ->
             let uu____1874 =
               FStar_Syntax_Unionfind.find
                 (hd1.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_head
                in
             (match uu____1874 with
              | FStar_Pervasives_Native.None  -> ret hd1
              | FStar_Pervasives_Native.Some t ->
                  ((let uu____1881 = goal_to_string_verbose hd1  in
                    let uu____1882 = FStar_Syntax_Print.term_to_string t  in
                    FStar_Util.print2
                      "!!!!!!!!!!!! GOAL IS ALREADY SOLVED! %s\nsol is %s\n"
                      uu____1881 uu____1882);
                   ret hd1)))
  
let (tadmit : unit -> unit tac) =
  fun uu____1889  ->
    let uu____1892 =
      bind get
        (fun ps  ->
           let uu____1898 = cur_goal ()  in
           bind uu____1898
             (fun g  ->
                (let uu____1905 =
                   let uu____1906 = FStar_Tactics_Types.goal_type g  in
                   uu____1906.FStar_Syntax_Syntax.pos  in
                 let uu____1909 =
                   let uu____1914 =
                     let uu____1915 = goal_to_string ps g  in
                     FStar_Util.format1 "Tactics admitted goal <%s>\n\n"
                       uu____1915
                      in
                   (FStar_Errors.Warning_TacAdmit, uu____1914)  in
                 FStar_Errors.log_issue uu____1905 uu____1909);
                solve' g FStar_Syntax_Util.exp_unit))
       in
    FStar_All.pipe_left (wrap_err "tadmit") uu____1892
  
let (fresh : unit -> FStar_BigInt.t tac) =
  fun uu____1926  ->
    bind get
      (fun ps  ->
         let n1 = ps.FStar_Tactics_Types.freshness  in
         let ps1 =
           let uu___355_1936 = ps  in
           {
             FStar_Tactics_Types.main_context =
               (uu___355_1936.FStar_Tactics_Types.main_context);
             FStar_Tactics_Types.main_goal =
               (uu___355_1936.FStar_Tactics_Types.main_goal);
             FStar_Tactics_Types.all_implicits =
               (uu___355_1936.FStar_Tactics_Types.all_implicits);
             FStar_Tactics_Types.goals =
               (uu___355_1936.FStar_Tactics_Types.goals);
             FStar_Tactics_Types.smt_goals =
               (uu___355_1936.FStar_Tactics_Types.smt_goals);
             FStar_Tactics_Types.depth =
               (uu___355_1936.FStar_Tactics_Types.depth);
             FStar_Tactics_Types.__dump =
               (uu___355_1936.FStar_Tactics_Types.__dump);
             FStar_Tactics_Types.psc =
               (uu___355_1936.FStar_Tactics_Types.psc);
             FStar_Tactics_Types.entry_range =
               (uu___355_1936.FStar_Tactics_Types.entry_range);
             FStar_Tactics_Types.guard_policy =
               (uu___355_1936.FStar_Tactics_Types.guard_policy);
             FStar_Tactics_Types.freshness = (n1 + (Prims.parse_int "1"));
             FStar_Tactics_Types.tac_verb_dbg =
               (uu___355_1936.FStar_Tactics_Types.tac_verb_dbg)
           }  in
         let uu____1937 = set ps1  in
         bind uu____1937
           (fun uu____1942  ->
              let uu____1943 = FStar_BigInt.of_int_fs n1  in ret uu____1943))
  
let (ngoals : unit -> FStar_BigInt.t tac) =
  fun uu____1950  ->
    bind get
      (fun ps  ->
         let n1 = FStar_List.length ps.FStar_Tactics_Types.goals  in
         let uu____1958 = FStar_BigInt.of_int_fs n1  in ret uu____1958)
  
let (ngoals_smt : unit -> FStar_BigInt.t tac) =
  fun uu____1971  ->
    bind get
      (fun ps  ->
         let n1 = FStar_List.length ps.FStar_Tactics_Types.smt_goals  in
         let uu____1979 = FStar_BigInt.of_int_fs n1  in ret uu____1979)
  
let (is_guard : unit -> Prims.bool tac) =
  fun uu____1992  ->
    let uu____1995 = cur_goal ()  in
    bind uu____1995 (fun g  -> ret g.FStar_Tactics_Types.is_guard)
  
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
            let uu____2027 = env.FStar_TypeChecker_Env.universe_of env phi
               in
            FStar_Syntax_Util.mk_squash uu____2027 phi  in
          let uu____2028 = new_uvar reason env typ  in
          bind uu____2028
            (fun uu____2043  ->
               match uu____2043 with
               | (uu____2050,ctx_uvar) ->
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
             (fun uu____2095  ->
                let uu____2096 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.print1 "Tac> __tc(%s)\n" uu____2096)
             (fun uu____2099  ->
                let e1 =
                  let uu___356_2101 = e  in
                  {
                    FStar_TypeChecker_Env.solver =
                      (uu___356_2101.FStar_TypeChecker_Env.solver);
                    FStar_TypeChecker_Env.range =
                      (uu___356_2101.FStar_TypeChecker_Env.range);
                    FStar_TypeChecker_Env.curmodule =
                      (uu___356_2101.FStar_TypeChecker_Env.curmodule);
                    FStar_TypeChecker_Env.gamma =
                      (uu___356_2101.FStar_TypeChecker_Env.gamma);
                    FStar_TypeChecker_Env.gamma_sig =
                      (uu___356_2101.FStar_TypeChecker_Env.gamma_sig);
                    FStar_TypeChecker_Env.gamma_cache =
                      (uu___356_2101.FStar_TypeChecker_Env.gamma_cache);
                    FStar_TypeChecker_Env.modules =
                      (uu___356_2101.FStar_TypeChecker_Env.modules);
                    FStar_TypeChecker_Env.expected_typ =
                      (uu___356_2101.FStar_TypeChecker_Env.expected_typ);
                    FStar_TypeChecker_Env.sigtab =
                      (uu___356_2101.FStar_TypeChecker_Env.sigtab);
                    FStar_TypeChecker_Env.is_pattern =
                      (uu___356_2101.FStar_TypeChecker_Env.is_pattern);
                    FStar_TypeChecker_Env.instantiate_imp =
                      (uu___356_2101.FStar_TypeChecker_Env.instantiate_imp);
                    FStar_TypeChecker_Env.effects =
                      (uu___356_2101.FStar_TypeChecker_Env.effects);
                    FStar_TypeChecker_Env.generalize =
                      (uu___356_2101.FStar_TypeChecker_Env.generalize);
                    FStar_TypeChecker_Env.letrecs =
                      (uu___356_2101.FStar_TypeChecker_Env.letrecs);
                    FStar_TypeChecker_Env.top_level =
                      (uu___356_2101.FStar_TypeChecker_Env.top_level);
                    FStar_TypeChecker_Env.check_uvars =
                      (uu___356_2101.FStar_TypeChecker_Env.check_uvars);
                    FStar_TypeChecker_Env.use_eq =
                      (uu___356_2101.FStar_TypeChecker_Env.use_eq);
                    FStar_TypeChecker_Env.is_iface =
                      (uu___356_2101.FStar_TypeChecker_Env.is_iface);
                    FStar_TypeChecker_Env.admit =
                      (uu___356_2101.FStar_TypeChecker_Env.admit);
                    FStar_TypeChecker_Env.lax =
                      (uu___356_2101.FStar_TypeChecker_Env.lax);
                    FStar_TypeChecker_Env.lax_universes =
                      (uu___356_2101.FStar_TypeChecker_Env.lax_universes);
                    FStar_TypeChecker_Env.failhard =
                      (uu___356_2101.FStar_TypeChecker_Env.failhard);
                    FStar_TypeChecker_Env.nosynth =
                      (uu___356_2101.FStar_TypeChecker_Env.nosynth);
                    FStar_TypeChecker_Env.uvar_subtyping = false;
                    FStar_TypeChecker_Env.tc_term =
                      (uu___356_2101.FStar_TypeChecker_Env.tc_term);
                    FStar_TypeChecker_Env.type_of =
                      (uu___356_2101.FStar_TypeChecker_Env.type_of);
                    FStar_TypeChecker_Env.universe_of =
                      (uu___356_2101.FStar_TypeChecker_Env.universe_of);
                    FStar_TypeChecker_Env.check_type_of =
                      (uu___356_2101.FStar_TypeChecker_Env.check_type_of);
                    FStar_TypeChecker_Env.use_bv_sorts =
                      (uu___356_2101.FStar_TypeChecker_Env.use_bv_sorts);
                    FStar_TypeChecker_Env.qtbl_name_and_index =
                      (uu___356_2101.FStar_TypeChecker_Env.qtbl_name_and_index);
                    FStar_TypeChecker_Env.normalized_eff_names =
                      (uu___356_2101.FStar_TypeChecker_Env.normalized_eff_names);
                    FStar_TypeChecker_Env.proof_ns =
                      (uu___356_2101.FStar_TypeChecker_Env.proof_ns);
                    FStar_TypeChecker_Env.synth_hook =
                      (uu___356_2101.FStar_TypeChecker_Env.synth_hook);
                    FStar_TypeChecker_Env.splice =
                      (uu___356_2101.FStar_TypeChecker_Env.splice);
                    FStar_TypeChecker_Env.is_native_tactic =
                      (uu___356_2101.FStar_TypeChecker_Env.is_native_tactic);
                    FStar_TypeChecker_Env.identifier_info =
                      (uu___356_2101.FStar_TypeChecker_Env.identifier_info);
                    FStar_TypeChecker_Env.tc_hooks =
                      (uu___356_2101.FStar_TypeChecker_Env.tc_hooks);
                    FStar_TypeChecker_Env.dsenv =
                      (uu___356_2101.FStar_TypeChecker_Env.dsenv);
                    FStar_TypeChecker_Env.dep_graph =
                      (uu___356_2101.FStar_TypeChecker_Env.dep_graph)
                  }  in
                try
                  let uu____2121 =
                    (ps.FStar_Tactics_Types.main_context).FStar_TypeChecker_Env.type_of
                      e1 t
                     in
                  ret uu____2121
                with
                | FStar_Errors.Err (uu____2148,msg) ->
                    let uu____2150 = tts e1 t  in
                    let uu____2151 =
                      let uu____2152 = FStar_TypeChecker_Env.all_binders e1
                         in
                      FStar_All.pipe_right uu____2152
                        (FStar_Syntax_Print.binders_to_string ", ")
                       in
                    fail3 "Cannot type %s in context (%s). Error = (%s)"
                      uu____2150 uu____2151 msg
                | FStar_Errors.Error (uu____2159,msg,uu____2161) ->
                    let uu____2162 = tts e1 t  in
                    let uu____2163 =
                      let uu____2164 = FStar_TypeChecker_Env.all_binders e1
                         in
                      FStar_All.pipe_right uu____2164
                        (FStar_Syntax_Print.binders_to_string ", ")
                       in
                    fail3 "Cannot type %s in context (%s). Error = (%s)"
                      uu____2162 uu____2163 msg))
  
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
  fun uu____2191  ->
    bind get (fun ps  -> ret ps.FStar_Tactics_Types.guard_policy)
  
let (set_guard_policy : FStar_Tactics_Types.guard_policy -> unit tac) =
  fun pol  ->
    bind get
      (fun ps  ->
         set
           (let uu___359_2209 = ps  in
            {
              FStar_Tactics_Types.main_context =
                (uu___359_2209.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___359_2209.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___359_2209.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___359_2209.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (uu___359_2209.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___359_2209.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___359_2209.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___359_2209.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___359_2209.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy = pol;
              FStar_Tactics_Types.freshness =
                (uu___359_2209.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___359_2209.FStar_Tactics_Types.tac_verb_dbg)
            }))
  
let with_policy : 'a . FStar_Tactics_Types.guard_policy -> 'a tac -> 'a tac =
  fun pol  ->
    fun t  ->
      let uu____2233 = get_guard_policy ()  in
      bind uu____2233
        (fun old_pol  ->
           let uu____2239 = set_guard_policy pol  in
           bind uu____2239
             (fun uu____2243  ->
                bind t
                  (fun r  ->
                     let uu____2247 = set_guard_policy old_pol  in
                     bind uu____2247 (fun uu____2251  -> ret r))))
  
let (proc_guard :
  Prims.string ->
    env ->
      FStar_TypeChecker_Env.guard_t -> FStar_Options.optionstate -> unit tac)
  =
  fun reason  ->
    fun e  ->
      fun g  ->
        fun opts  ->
          let uu____2276 =
            let uu____2277 = FStar_TypeChecker_Rel.simplify_guard e g  in
            uu____2277.FStar_TypeChecker_Env.guard_f  in
          match uu____2276 with
          | FStar_TypeChecker_Common.Trivial  -> ret ()
          | FStar_TypeChecker_Common.NonTrivial f ->
              let uu____2281 = istrivial e f  in
              if uu____2281
              then ret ()
              else
                bind get
                  (fun ps  ->
                     match ps.FStar_Tactics_Types.guard_policy with
                     | FStar_Tactics_Types.Drop  -> ret ()
                     | FStar_Tactics_Types.Goal  ->
                         let uu____2289 = mk_irrelevant_goal reason e f opts
                            in
                         bind uu____2289
                           (fun goal  ->
                              let goal1 =
                                let uu___360_2296 = goal  in
                                {
                                  FStar_Tactics_Types.goal_main_env =
                                    (uu___360_2296.FStar_Tactics_Types.goal_main_env);
                                  FStar_Tactics_Types.goal_ctx_uvar =
                                    (uu___360_2296.FStar_Tactics_Types.goal_ctx_uvar);
                                  FStar_Tactics_Types.opts =
                                    (uu___360_2296.FStar_Tactics_Types.opts);
                                  FStar_Tactics_Types.is_guard = true
                                }  in
                              push_goals [goal1])
                     | FStar_Tactics_Types.SMT  ->
                         let uu____2297 = mk_irrelevant_goal reason e f opts
                            in
                         bind uu____2297
                           (fun goal  ->
                              let goal1 =
                                let uu___361_2304 = goal  in
                                {
                                  FStar_Tactics_Types.goal_main_env =
                                    (uu___361_2304.FStar_Tactics_Types.goal_main_env);
                                  FStar_Tactics_Types.goal_ctx_uvar =
                                    (uu___361_2304.FStar_Tactics_Types.goal_ctx_uvar);
                                  FStar_Tactics_Types.opts =
                                    (uu___361_2304.FStar_Tactics_Types.opts);
                                  FStar_Tactics_Types.is_guard = true
                                }  in
                              push_smt_goals [goal1])
                     | FStar_Tactics_Types.Force  ->
                         (try
                            let uu____2312 =
                              let uu____2313 =
                                let uu____2314 =
                                  FStar_TypeChecker_Rel.discharge_guard_no_smt
                                    e g
                                   in
                                FStar_All.pipe_left
                                  FStar_TypeChecker_Rel.is_trivial uu____2314
                                 in
                              Prims.op_Negation uu____2313  in
                            if uu____2312
                            then
                              mlog
                                (fun uu____2319  ->
                                   let uu____2320 =
                                     FStar_TypeChecker_Rel.guard_to_string e
                                       g
                                      in
                                   FStar_Util.print1 "guard = %s\n"
                                     uu____2320)
                                (fun uu____2322  ->
                                   fail1 "Forcing the guard failed %s)"
                                     reason)
                            else ret ()
                          with
                          | uu____2329 ->
                              mlog
                                (fun uu____2332  ->
                                   let uu____2333 =
                                     FStar_TypeChecker_Rel.guard_to_string e
                                       g
                                      in
                                   FStar_Util.print1 "guard = %s\n"
                                     uu____2333)
                                (fun uu____2335  ->
                                   fail1 "Forcing the guard failed (%s)"
                                     reason)))
  
let (tc : FStar_Syntax_Syntax.term -> FStar_Reflection_Data.typ tac) =
  fun t  ->
    let uu____2345 =
      let uu____2348 = cur_goal ()  in
      bind uu____2348
        (fun goal  ->
           let uu____2354 =
             let uu____2363 = FStar_Tactics_Types.goal_env goal  in
             __tc uu____2363 t  in
           bind uu____2354
             (fun uu____2375  ->
                match uu____2375 with
                | (t1,typ,guard) ->
                    let uu____2387 =
                      let uu____2390 = FStar_Tactics_Types.goal_env goal  in
                      proc_guard "tc" uu____2390 guard
                        goal.FStar_Tactics_Types.opts
                       in
                    bind uu____2387 (fun uu____2392  -> ret typ)))
       in
    FStar_All.pipe_left (wrap_err "tc") uu____2345
  
let (add_irrelevant_goal :
  Prims.string ->
    env -> FStar_Reflection_Data.typ -> FStar_Options.optionstate -> unit tac)
  =
  fun reason  ->
    fun env  ->
      fun phi  ->
        fun opts  ->
          let uu____2421 = mk_irrelevant_goal reason env phi opts  in
          bind uu____2421 (fun goal  -> add_goals [goal])
  
let (trivial : unit -> unit tac) =
  fun uu____2432  ->
    let uu____2435 = cur_goal ()  in
    bind uu____2435
      (fun goal  ->
         let uu____2441 =
           let uu____2442 = FStar_Tactics_Types.goal_env goal  in
           let uu____2443 = FStar_Tactics_Types.goal_type goal  in
           istrivial uu____2442 uu____2443  in
         if uu____2441
         then solve' goal FStar_Syntax_Util.exp_unit
         else
           (let uu____2447 =
              let uu____2448 = FStar_Tactics_Types.goal_env goal  in
              let uu____2449 = FStar_Tactics_Types.goal_type goal  in
              tts uu____2448 uu____2449  in
            fail1 "Not a trivial goal: %s" uu____2447))
  
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
          let uu____2478 =
            let uu____2479 = FStar_TypeChecker_Rel.simplify_guard e g  in
            uu____2479.FStar_TypeChecker_Env.guard_f  in
          match uu____2478 with
          | FStar_TypeChecker_Common.Trivial  ->
              ret FStar_Pervasives_Native.None
          | FStar_TypeChecker_Common.NonTrivial f ->
              let uu____2487 = istrivial e f  in
              if uu____2487
              then ret FStar_Pervasives_Native.None
              else
                (let uu____2495 = mk_irrelevant_goal reason e f opts  in
                 bind uu____2495
                   (fun goal  ->
                      ret
                        (FStar_Pervasives_Native.Some
                           (let uu___364_2505 = goal  in
                            {
                              FStar_Tactics_Types.goal_main_env =
                                (uu___364_2505.FStar_Tactics_Types.goal_main_env);
                              FStar_Tactics_Types.goal_ctx_uvar =
                                (uu___364_2505.FStar_Tactics_Types.goal_ctx_uvar);
                              FStar_Tactics_Types.opts =
                                (uu___364_2505.FStar_Tactics_Types.opts);
                              FStar_Tactics_Types.is_guard = true
                            }))))
  
let (smt : unit -> unit tac) =
  fun uu____2512  ->
    let uu____2515 = cur_goal ()  in
    bind uu____2515
      (fun g  ->
         let uu____2521 = is_irrelevant g  in
         if uu____2521
         then bind __dismiss (fun uu____2525  -> add_smt_goals [g])
         else
           (let uu____2527 =
              let uu____2528 = FStar_Tactics_Types.goal_env g  in
              let uu____2529 = FStar_Tactics_Types.goal_type g  in
              tts uu____2528 uu____2529  in
            fail1 "goal is not irrelevant: cannot dispatch to smt (%s)"
              uu____2527))
  
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
             let uu____2578 =
               try
                 let uu____2612 =
                   let uu____2621 = FStar_BigInt.to_int_fs n1  in
                   FStar_List.splitAt uu____2621 p.FStar_Tactics_Types.goals
                    in
                 ret uu____2612
               with | uu____2643 -> fail "divide: not enough goals"  in
             bind uu____2578
               (fun uu____2670  ->
                  match uu____2670 with
                  | (lgs,rgs) ->
                      let lp =
                        let uu___365_2696 = p  in
                        {
                          FStar_Tactics_Types.main_context =
                            (uu___365_2696.FStar_Tactics_Types.main_context);
                          FStar_Tactics_Types.main_goal =
                            (uu___365_2696.FStar_Tactics_Types.main_goal);
                          FStar_Tactics_Types.all_implicits =
                            (uu___365_2696.FStar_Tactics_Types.all_implicits);
                          FStar_Tactics_Types.goals = lgs;
                          FStar_Tactics_Types.smt_goals = [];
                          FStar_Tactics_Types.depth =
                            (uu___365_2696.FStar_Tactics_Types.depth);
                          FStar_Tactics_Types.__dump =
                            (uu___365_2696.FStar_Tactics_Types.__dump);
                          FStar_Tactics_Types.psc =
                            (uu___365_2696.FStar_Tactics_Types.psc);
                          FStar_Tactics_Types.entry_range =
                            (uu___365_2696.FStar_Tactics_Types.entry_range);
                          FStar_Tactics_Types.guard_policy =
                            (uu___365_2696.FStar_Tactics_Types.guard_policy);
                          FStar_Tactics_Types.freshness =
                            (uu___365_2696.FStar_Tactics_Types.freshness);
                          FStar_Tactics_Types.tac_verb_dbg =
                            (uu___365_2696.FStar_Tactics_Types.tac_verb_dbg)
                        }  in
                      let rp =
                        let uu___366_2698 = p  in
                        {
                          FStar_Tactics_Types.main_context =
                            (uu___366_2698.FStar_Tactics_Types.main_context);
                          FStar_Tactics_Types.main_goal =
                            (uu___366_2698.FStar_Tactics_Types.main_goal);
                          FStar_Tactics_Types.all_implicits =
                            (uu___366_2698.FStar_Tactics_Types.all_implicits);
                          FStar_Tactics_Types.goals = rgs;
                          FStar_Tactics_Types.smt_goals = [];
                          FStar_Tactics_Types.depth =
                            (uu___366_2698.FStar_Tactics_Types.depth);
                          FStar_Tactics_Types.__dump =
                            (uu___366_2698.FStar_Tactics_Types.__dump);
                          FStar_Tactics_Types.psc =
                            (uu___366_2698.FStar_Tactics_Types.psc);
                          FStar_Tactics_Types.entry_range =
                            (uu___366_2698.FStar_Tactics_Types.entry_range);
                          FStar_Tactics_Types.guard_policy =
                            (uu___366_2698.FStar_Tactics_Types.guard_policy);
                          FStar_Tactics_Types.freshness =
                            (uu___366_2698.FStar_Tactics_Types.freshness);
                          FStar_Tactics_Types.tac_verb_dbg =
                            (uu___366_2698.FStar_Tactics_Types.tac_verb_dbg)
                        }  in
                      let uu____2699 = set lp  in
                      bind uu____2699
                        (fun uu____2707  ->
                           bind l
                             (fun a  ->
                                bind get
                                  (fun lp'  ->
                                     let uu____2721 = set rp  in
                                     bind uu____2721
                                       (fun uu____2729  ->
                                          bind r
                                            (fun b  ->
                                               bind get
                                                 (fun rp'  ->
                                                    let p' =
                                                      let uu___367_2745 = p
                                                         in
                                                      {
                                                        FStar_Tactics_Types.main_context
                                                          =
                                                          (uu___367_2745.FStar_Tactics_Types.main_context);
                                                        FStar_Tactics_Types.main_goal
                                                          =
                                                          (uu___367_2745.FStar_Tactics_Types.main_goal);
                                                        FStar_Tactics_Types.all_implicits
                                                          =
                                                          (uu___367_2745.FStar_Tactics_Types.all_implicits);
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
                                                          (uu___367_2745.FStar_Tactics_Types.depth);
                                                        FStar_Tactics_Types.__dump
                                                          =
                                                          (uu___367_2745.FStar_Tactics_Types.__dump);
                                                        FStar_Tactics_Types.psc
                                                          =
                                                          (uu___367_2745.FStar_Tactics_Types.psc);
                                                        FStar_Tactics_Types.entry_range
                                                          =
                                                          (uu___367_2745.FStar_Tactics_Types.entry_range);
                                                        FStar_Tactics_Types.guard_policy
                                                          =
                                                          (uu___367_2745.FStar_Tactics_Types.guard_policy);
                                                        FStar_Tactics_Types.freshness
                                                          =
                                                          (uu___367_2745.FStar_Tactics_Types.freshness);
                                                        FStar_Tactics_Types.tac_verb_dbg
                                                          =
                                                          (uu___367_2745.FStar_Tactics_Types.tac_verb_dbg)
                                                      }  in
                                                    let uu____2746 = set p'
                                                       in
                                                    bind uu____2746
                                                      (fun uu____2754  ->
                                                         bind
                                                           remove_solved_goals
                                                           (fun uu____2760 
                                                              -> ret (a, b)))))))))))
  
let focus : 'a . 'a tac -> 'a tac =
  fun f  ->
    let uu____2781 = divide FStar_BigInt.one f idtac  in
    bind uu____2781
      (fun uu____2794  -> match uu____2794 with | (a,()) -> ret a)
  
let rec map : 'a . 'a tac -> 'a Prims.list tac =
  fun tau  ->
    bind get
      (fun p  ->
         match p.FStar_Tactics_Types.goals with
         | [] -> ret []
         | uu____2831::uu____2832 ->
             let uu____2835 =
               let uu____2844 = map tau  in
               divide FStar_BigInt.one tau uu____2844  in
             bind uu____2835
               (fun uu____2862  ->
                  match uu____2862 with | (h,t) -> ret (h :: t)))
  
let (seq : unit tac -> unit tac -> unit tac) =
  fun t1  ->
    fun t2  ->
      let uu____2903 =
        bind t1
          (fun uu____2908  ->
             let uu____2909 = map t2  in
             bind uu____2909 (fun uu____2917  -> ret ()))
         in
      focus uu____2903
  
let (intro : unit -> FStar_Syntax_Syntax.binder tac) =
  fun uu____2926  ->
    let uu____2929 =
      let uu____2932 = cur_goal ()  in
      bind uu____2932
        (fun goal  ->
           let uu____2941 =
             let uu____2948 = FStar_Tactics_Types.goal_type goal  in
             FStar_Syntax_Util.arrow_one uu____2948  in
           match uu____2941 with
           | FStar_Pervasives_Native.Some (b,c) ->
               let uu____2957 =
                 let uu____2958 = FStar_Syntax_Util.is_total_comp c  in
                 Prims.op_Negation uu____2958  in
               if uu____2957
               then fail "Codomain is effectful"
               else
                 (let env' =
                    let uu____2963 = FStar_Tactics_Types.goal_env goal  in
                    FStar_TypeChecker_Env.push_binders uu____2963 [b]  in
                  let typ' = comp_to_typ c  in
                  let uu____2973 = new_uvar "intro" env' typ'  in
                  bind uu____2973
                    (fun uu____2989  ->
                       match uu____2989 with
                       | (body,ctx_uvar) ->
                           let sol =
                             FStar_Syntax_Util.abs [b] body
                               FStar_Pervasives_Native.None
                              in
                           let uu____3009 = set_solution goal sol  in
                           bind uu____3009
                             (fun uu____3015  ->
                                let g =
                                  FStar_Tactics_Types.mk_goal env' ctx_uvar
                                    goal.FStar_Tactics_Types.opts
                                    goal.FStar_Tactics_Types.is_guard
                                   in
                                let uu____3017 =
                                  let uu____3020 = bnorm_goal g  in
                                  replace_cur uu____3020  in
                                bind uu____3017 (fun uu____3022  -> ret b))))
           | FStar_Pervasives_Native.None  ->
               let uu____3027 =
                 let uu____3028 = FStar_Tactics_Types.goal_env goal  in
                 let uu____3029 = FStar_Tactics_Types.goal_type goal  in
                 tts uu____3028 uu____3029  in
               fail1 "goal is not an arrow (%s)" uu____3027)
       in
    FStar_All.pipe_left (wrap_err "intro") uu____2929
  
let (intro_rec :
  unit ->
    (FStar_Syntax_Syntax.binder,FStar_Syntax_Syntax.binder)
      FStar_Pervasives_Native.tuple2 tac)
  =
  fun uu____3044  ->
    let uu____3051 = cur_goal ()  in
    bind uu____3051
      (fun goal  ->
         FStar_Util.print_string
           "WARNING (intro_rec): calling this is known to cause normalizer loops\n";
         FStar_Util.print_string
           "WARNING (intro_rec): proceed at your own risk...\n";
         (let uu____3068 =
            let uu____3075 = FStar_Tactics_Types.goal_type goal  in
            FStar_Syntax_Util.arrow_one uu____3075  in
          match uu____3068 with
          | FStar_Pervasives_Native.Some (b,c) ->
              let uu____3088 =
                let uu____3089 = FStar_Syntax_Util.is_total_comp c  in
                Prims.op_Negation uu____3089  in
              if uu____3088
              then fail "Codomain is effectful"
              else
                (let bv =
                   let uu____3102 = FStar_Tactics_Types.goal_type goal  in
                   FStar_Syntax_Syntax.gen_bv "__recf"
                     FStar_Pervasives_Native.None uu____3102
                    in
                 let bs =
                   let uu____3110 = FStar_Syntax_Syntax.mk_binder bv  in
                   [uu____3110; b]  in
                 let env' =
                   let uu____3128 = FStar_Tactics_Types.goal_env goal  in
                   FStar_TypeChecker_Env.push_binders uu____3128 bs  in
                 let uu____3129 =
                   let uu____3136 = comp_to_typ c  in
                   new_uvar "intro_rec" env' uu____3136  in
                 bind uu____3129
                   (fun uu____3155  ->
                      match uu____3155 with
                      | (u,ctx_uvar_u) ->
                          let lb =
                            let uu____3169 =
                              FStar_Tactics_Types.goal_type goal  in
                            let uu____3172 =
                              FStar_Syntax_Util.abs [b] u
                                FStar_Pervasives_Native.None
                               in
                            FStar_Syntax_Util.mk_letbinding
                              (FStar_Util.Inl bv) [] uu____3169
                              FStar_Parser_Const.effect_Tot_lid uu____3172 []
                              FStar_Range.dummyRange
                             in
                          let body = FStar_Syntax_Syntax.bv_to_name bv  in
                          let uu____3186 =
                            FStar_Syntax_Subst.close_let_rec [lb] body  in
                          (match uu____3186 with
                           | (lbs,body1) ->
                               let tm =
                                 let uu____3208 =
                                   let uu____3209 =
                                     FStar_Tactics_Types.goal_witness goal
                                      in
                                   uu____3209.FStar_Syntax_Syntax.pos  in
                                 FStar_Syntax_Syntax.mk
                                   (FStar_Syntax_Syntax.Tm_let
                                      ((true, lbs), body1))
                                   FStar_Pervasives_Native.None uu____3208
                                  in
                               let uu____3222 = set_solution goal tm  in
                               bind uu____3222
                                 (fun uu____3231  ->
                                    let uu____3232 =
                                      let uu____3235 =
                                        bnorm_goal
                                          (let uu___370_3238 = goal  in
                                           {
                                             FStar_Tactics_Types.goal_main_env
                                               =
                                               (uu___370_3238.FStar_Tactics_Types.goal_main_env);
                                             FStar_Tactics_Types.goal_ctx_uvar
                                               = ctx_uvar_u;
                                             FStar_Tactics_Types.opts =
                                               (uu___370_3238.FStar_Tactics_Types.opts);
                                             FStar_Tactics_Types.is_guard =
                                               (uu___370_3238.FStar_Tactics_Types.is_guard)
                                           })
                                         in
                                      replace_cur uu____3235  in
                                    bind uu____3232
                                      (fun uu____3245  ->
                                         let uu____3246 =
                                           let uu____3251 =
                                             FStar_Syntax_Syntax.mk_binder bv
                                              in
                                           (uu____3251, b)  in
                                         ret uu____3246)))))
          | FStar_Pervasives_Native.None  ->
              let uu____3260 =
                let uu____3261 = FStar_Tactics_Types.goal_env goal  in
                let uu____3262 = FStar_Tactics_Types.goal_type goal  in
                tts uu____3261 uu____3262  in
              fail1 "intro_rec: goal is not an arrow (%s)" uu____3260))
  
let (norm : FStar_Syntax_Embeddings.norm_step Prims.list -> unit tac) =
  fun s  ->
    let uu____3280 = cur_goal ()  in
    bind uu____3280
      (fun goal  ->
         mlog
           (fun uu____3287  ->
              let uu____3288 =
                let uu____3289 = FStar_Tactics_Types.goal_witness goal  in
                FStar_Syntax_Print.term_to_string uu____3289  in
              FStar_Util.print1 "norm: witness = %s\n" uu____3288)
           (fun uu____3294  ->
              let steps =
                let uu____3298 = FStar_TypeChecker_Normalize.tr_norm_steps s
                   in
                FStar_List.append
                  [FStar_TypeChecker_Normalize.Reify;
                  FStar_TypeChecker_Normalize.UnfoldTac] uu____3298
                 in
              let t =
                let uu____3302 = FStar_Tactics_Types.goal_env goal  in
                let uu____3303 = FStar_Tactics_Types.goal_type goal  in
                normalize steps uu____3302 uu____3303  in
              let uu____3304 = FStar_Tactics_Types.goal_with_type goal t  in
              replace_cur uu____3304))
  
let (norm_term_env :
  env ->
    FStar_Syntax_Embeddings.norm_step Prims.list ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term tac)
  =
  fun e  ->
    fun s  ->
      fun t  ->
        let uu____3328 =
          mlog
            (fun uu____3333  ->
               let uu____3334 = FStar_Syntax_Print.term_to_string t  in
               FStar_Util.print1 "norm_term: tm = %s\n" uu____3334)
            (fun uu____3336  ->
               bind get
                 (fun ps  ->
                    let opts =
                      match ps.FStar_Tactics_Types.goals with
                      | g::uu____3342 -> g.FStar_Tactics_Types.opts
                      | uu____3345 -> FStar_Options.peek ()  in
                    mlog
                      (fun uu____3350  ->
                         let uu____3351 = FStar_Syntax_Print.term_to_string t
                            in
                         FStar_Util.print1 "norm_term_env: t = %s\n"
                           uu____3351)
                      (fun uu____3354  ->
                         let uu____3355 = __tc e t  in
                         bind uu____3355
                           (fun uu____3376  ->
                              match uu____3376 with
                              | (t1,uu____3386,uu____3387) ->
                                  let steps =
                                    let uu____3391 =
                                      FStar_TypeChecker_Normalize.tr_norm_steps
                                        s
                                       in
                                    FStar_List.append
                                      [FStar_TypeChecker_Normalize.Reify;
                                      FStar_TypeChecker_Normalize.UnfoldTac]
                                      uu____3391
                                     in
                                  let t2 =
                                    normalize steps
                                      ps.FStar_Tactics_Types.main_context t1
                                     in
                                  ret t2))))
           in
        FStar_All.pipe_left (wrap_err "norm_term") uu____3328
  
let (refine_intro : unit -> unit tac) =
  fun uu____3405  ->
    let uu____3408 =
      let uu____3411 = cur_goal ()  in
      bind uu____3411
        (fun g  ->
           let uu____3418 =
             let uu____3429 = FStar_Tactics_Types.goal_env g  in
             let uu____3430 = FStar_Tactics_Types.goal_type g  in
             FStar_TypeChecker_Rel.base_and_refinement uu____3429 uu____3430
              in
           match uu____3418 with
           | (uu____3433,FStar_Pervasives_Native.None ) ->
               fail "not a refinement"
           | (t,FStar_Pervasives_Native.Some (bv,phi)) ->
               let g1 = FStar_Tactics_Types.goal_with_type g t  in
               let uu____3458 =
                 let uu____3463 =
                   let uu____3468 =
                     let uu____3469 = FStar_Syntax_Syntax.mk_binder bv  in
                     [uu____3469]  in
                   FStar_Syntax_Subst.open_term uu____3468 phi  in
                 match uu____3463 with
                 | (bvs,phi1) ->
                     let uu____3488 =
                       let uu____3489 = FStar_List.hd bvs  in
                       FStar_Pervasives_Native.fst uu____3489  in
                     (uu____3488, phi1)
                  in
               (match uu____3458 with
                | (bv1,phi1) ->
                    let uu____3502 =
                      let uu____3505 = FStar_Tactics_Types.goal_env g  in
                      let uu____3506 =
                        let uu____3507 =
                          let uu____3510 =
                            let uu____3511 =
                              let uu____3518 =
                                FStar_Tactics_Types.goal_witness g  in
                              (bv1, uu____3518)  in
                            FStar_Syntax_Syntax.NT uu____3511  in
                          [uu____3510]  in
                        FStar_Syntax_Subst.subst uu____3507 phi1  in
                      mk_irrelevant_goal "refine_intro refinement" uu____3505
                        uu____3506 g.FStar_Tactics_Types.opts
                       in
                    bind uu____3502
                      (fun g2  ->
                         bind __dismiss
                           (fun uu____3526  -> add_goals [g1; g2]))))
       in
    FStar_All.pipe_left (wrap_err "refine_intro") uu____3408
  
let (__exact_now : Prims.bool -> FStar_Syntax_Syntax.term -> unit tac) =
  fun set_expected_typ1  ->
    fun t  ->
      let uu____3545 = cur_goal ()  in
      bind uu____3545
        (fun goal  ->
           let env =
             if set_expected_typ1
             then
               let uu____3553 = FStar_Tactics_Types.goal_env goal  in
               let uu____3554 = FStar_Tactics_Types.goal_type goal  in
               FStar_TypeChecker_Env.set_expected_typ uu____3553 uu____3554
             else FStar_Tactics_Types.goal_env goal  in
           let uu____3556 = __tc env t  in
           bind uu____3556
             (fun uu____3575  ->
                match uu____3575 with
                | (t1,typ,guard) ->
                    mlog
                      (fun uu____3590  ->
                         let uu____3591 =
                           FStar_Syntax_Print.term_to_string typ  in
                         let uu____3592 =
                           let uu____3593 = FStar_Tactics_Types.goal_env goal
                              in
                           FStar_TypeChecker_Rel.guard_to_string uu____3593
                             guard
                            in
                         FStar_Util.print2
                           "__exact_now: got type %s\n__exact_now: and guard %s\n"
                           uu____3591 uu____3592)
                      (fun uu____3596  ->
                         let uu____3597 =
                           let uu____3600 = FStar_Tactics_Types.goal_env goal
                              in
                           proc_guard "__exact typing" uu____3600 guard
                             goal.FStar_Tactics_Types.opts
                            in
                         bind uu____3597
                           (fun uu____3602  ->
                              mlog
                                (fun uu____3606  ->
                                   let uu____3607 =
                                     FStar_Syntax_Print.term_to_string typ
                                      in
                                   let uu____3608 =
                                     let uu____3609 =
                                       FStar_Tactics_Types.goal_type goal  in
                                     FStar_Syntax_Print.term_to_string
                                       uu____3609
                                      in
                                   FStar_Util.print2
                                     "__exact_now: unifying %s and %s\n"
                                     uu____3607 uu____3608)
                                (fun uu____3612  ->
                                   let uu____3613 =
                                     let uu____3616 =
                                       FStar_Tactics_Types.goal_env goal  in
                                     let uu____3617 =
                                       FStar_Tactics_Types.goal_type goal  in
                                     do_unify uu____3616 typ uu____3617  in
                                   bind uu____3613
                                     (fun b  ->
                                        if b
                                        then solve goal t1
                                        else
                                          (let uu____3623 =
                                             let uu____3624 =
                                               FStar_Tactics_Types.goal_env
                                                 goal
                                                in
                                             tts uu____3624 t1  in
                                           let uu____3625 =
                                             let uu____3626 =
                                               FStar_Tactics_Types.goal_env
                                                 goal
                                                in
                                             tts uu____3626 typ  in
                                           let uu____3627 =
                                             let uu____3628 =
                                               FStar_Tactics_Types.goal_env
                                                 goal
                                                in
                                             let uu____3629 =
                                               FStar_Tactics_Types.goal_type
                                                 goal
                                                in
                                             tts uu____3628 uu____3629  in
                                           let uu____3630 =
                                             let uu____3631 =
                                               FStar_Tactics_Types.goal_env
                                                 goal
                                                in
                                             let uu____3632 =
                                               FStar_Tactics_Types.goal_witness
                                                 goal
                                                in
                                             tts uu____3631 uu____3632  in
                                           fail4
                                             "%s : %s does not exactly solve the goal %s (witness = %s)"
                                             uu____3623 uu____3625 uu____3627
                                             uu____3630)))))))
  
let (t_exact : Prims.bool -> FStar_Syntax_Syntax.term -> unit tac) =
  fun set_expected_typ1  ->
    fun tm  ->
      let uu____3647 =
        mlog
          (fun uu____3652  ->
             let uu____3653 = FStar_Syntax_Print.term_to_string tm  in
             FStar_Util.print1 "t_exact: tm = %s\n" uu____3653)
          (fun uu____3656  ->
             let uu____3657 =
               let uu____3664 = __exact_now set_expected_typ1 tm  in
               trytac' uu____3664  in
             bind uu____3657
               (fun uu___335_3673  ->
                  match uu___335_3673 with
                  | FStar_Util.Inr r -> ret ()
                  | FStar_Util.Inl e ->
                      mlog
                        (fun uu____3683  ->
                           FStar_Util.print_string
                             "__exact_now failed, trying refine...\n")
                        (fun uu____3686  ->
                           let uu____3687 =
                             let uu____3694 =
                               let uu____3697 =
                                 norm [FStar_Syntax_Embeddings.Delta]  in
                               bind uu____3697
                                 (fun uu____3702  ->
                                    let uu____3703 = refine_intro ()  in
                                    bind uu____3703
                                      (fun uu____3707  ->
                                         __exact_now set_expected_typ1 tm))
                                in
                             trytac' uu____3694  in
                           bind uu____3687
                             (fun uu___334_3714  ->
                                match uu___334_3714 with
                                | FStar_Util.Inr r -> ret ()
                                | FStar_Util.Inl uu____3722 -> fail e))))
         in
      FStar_All.pipe_left (wrap_err "exact") uu____3647
  
let (uvar_free_in_goal :
  FStar_Syntax_Syntax.uvar -> FStar_Tactics_Types.goal -> Prims.bool) =
  fun u  ->
    fun g  ->
      if g.FStar_Tactics_Types.is_guard
      then false
      else
        (let free_uvars =
           let uu____3751 =
             let uu____3754 =
               let uu____3757 = FStar_Tactics_Types.goal_type g  in
               FStar_Syntax_Free.uvars uu____3757  in
             FStar_Util.set_elements uu____3754  in
           FStar_List.map (fun u1  -> u1.FStar_Syntax_Syntax.ctx_uvar_head)
             uu____3751
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
          let uu____3835 = f x  in
          bind uu____3835
            (fun y  ->
               let uu____3843 = mapM f xs  in
               bind uu____3843 (fun ys  -> ret (y :: ys)))
  
exception NoUnif 
let (uu___is_NoUnif : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with | NoUnif  -> true | uu____3863 -> false
  
let rec (__apply :
  Prims.bool ->
    FStar_Syntax_Syntax.term -> FStar_Reflection_Data.typ -> unit tac)
  =
  fun uopt  ->
    fun tm  ->
      fun typ  ->
        let uu____3883 = cur_goal ()  in
        bind uu____3883
          (fun goal  ->
             mlog
               (fun uu____3890  ->
                  let uu____3891 = FStar_Syntax_Print.term_to_string tm  in
                  FStar_Util.print1 ">>> Calling __exact(%s)\n" uu____3891)
               (fun uu____3894  ->
                  let uu____3895 =
                    let uu____3900 =
                      let uu____3903 = t_exact false tm  in
                      with_policy FStar_Tactics_Types.Force uu____3903  in
                    trytac_exn uu____3900  in
                  bind uu____3895
                    (fun uu___336_3910  ->
                       match uu___336_3910 with
                       | FStar_Pervasives_Native.Some r -> ret ()
                       | FStar_Pervasives_Native.None  ->
                           mlog
                             (fun uu____3918  ->
                                let uu____3919 =
                                  FStar_Syntax_Print.term_to_string typ  in
                                FStar_Util.print1 ">>> typ = %s\n" uu____3919)
                             (fun uu____3922  ->
                                let uu____3923 =
                                  FStar_Syntax_Util.arrow_one typ  in
                                match uu____3923 with
                                | FStar_Pervasives_Native.None  ->
                                    FStar_Exn.raise NoUnif
                                | FStar_Pervasives_Native.Some ((bv,aq),c) ->
                                    mlog
                                      (fun uu____3947  ->
                                         let uu____3948 =
                                           FStar_Syntax_Print.binder_to_string
                                             (bv, aq)
                                            in
                                         FStar_Util.print1
                                           "__apply: pushing binder %s\n"
                                           uu____3948)
                                      (fun uu____3951  ->
                                         let uu____3952 =
                                           let uu____3953 =
                                             FStar_Syntax_Util.is_total_comp
                                               c
                                              in
                                           Prims.op_Negation uu____3953  in
                                         if uu____3952
                                         then
                                           fail "apply: not total codomain"
                                         else
                                           (let uu____3957 =
                                              let uu____3964 =
                                                FStar_Tactics_Types.goal_env
                                                  goal
                                                 in
                                              new_uvar "apply" uu____3964
                                                bv.FStar_Syntax_Syntax.sort
                                               in
                                            bind uu____3957
                                              (fun uu____3975  ->
                                                 match uu____3975 with
                                                 | (u,_goal_u) ->
                                                     let tm' =
                                                       FStar_Syntax_Syntax.mk_Tm_app
                                                         tm [(u, aq)]
                                                         FStar_Pervasives_Native.None
                                                         tm.FStar_Syntax_Syntax.pos
                                                        in
                                                     let typ' =
                                                       let uu____4002 =
                                                         comp_to_typ c  in
                                                       FStar_All.pipe_left
                                                         (FStar_Syntax_Subst.subst
                                                            [FStar_Syntax_Syntax.NT
                                                               (bv, u)])
                                                         uu____4002
                                                        in
                                                     let uu____4005 =
                                                       __apply uopt tm' typ'
                                                        in
                                                     bind uu____4005
                                                       (fun uu____4013  ->
                                                          let u1 =
                                                            let uu____4015 =
                                                              FStar_Tactics_Types.goal_env
                                                                goal
                                                               in
                                                            bnorm uu____4015
                                                              u
                                                             in
                                                          let uu____4016 =
                                                            let uu____4017 =
                                                              let uu____4020
                                                                =
                                                                let uu____4021
                                                                  =
                                                                  FStar_Syntax_Util.head_and_args
                                                                    u1
                                                                   in
                                                                FStar_Pervasives_Native.fst
                                                                  uu____4021
                                                                 in
                                                              FStar_Syntax_Subst.compress
                                                                uu____4020
                                                               in
                                                            uu____4017.FStar_Syntax_Syntax.n
                                                             in
                                                          match uu____4016
                                                          with
                                                          | FStar_Syntax_Syntax.Tm_uvar
                                                              (goal_u,uu____4049)
                                                              ->
                                                              bind get
                                                                (fun ps  ->
                                                                   let uu____4073
                                                                    =
                                                                    uopt &&
                                                                    (uvar_free
                                                                    goal_u.FStar_Syntax_Syntax.ctx_uvar_head
                                                                    ps)  in
                                                                   if
                                                                    uu____4073
                                                                   then
                                                                    ret ()
                                                                   else
                                                                    (let uu____4077
                                                                    =
                                                                    let uu____4080
                                                                    =
                                                                    bnorm_goal
                                                                    (let uu___371_4083
                                                                    = goal
                                                                     in
                                                                    {
                                                                    FStar_Tactics_Types.goal_main_env
                                                                    =
                                                                    (uu___371_4083.FStar_Tactics_Types.goal_main_env);
                                                                    FStar_Tactics_Types.goal_ctx_uvar
                                                                    = goal_u;
                                                                    FStar_Tactics_Types.opts
                                                                    =
                                                                    (uu___371_4083.FStar_Tactics_Types.opts);
                                                                    FStar_Tactics_Types.is_guard
                                                                    = false
                                                                    })  in
                                                                    [uu____4080]
                                                                     in
                                                                    add_goals
                                                                    uu____4077))
                                                          | t -> ret ()))))))))
  
let try_unif : 'a . 'a tac -> 'a tac -> 'a tac =
  fun t  ->
    fun t'  -> mk_tac (fun ps  -> try run t ps with | NoUnif  -> run t' ps)
  
let (apply : Prims.bool -> FStar_Syntax_Syntax.term -> unit tac) =
  fun uopt  ->
    fun tm  ->
      let uu____4138 =
        mlog
          (fun uu____4143  ->
             let uu____4144 = FStar_Syntax_Print.term_to_string tm  in
             FStar_Util.print1 "apply: tm = %s\n" uu____4144)
          (fun uu____4147  ->
             let uu____4148 = cur_goal ()  in
             bind uu____4148
               (fun goal  ->
                  let uu____4154 =
                    let uu____4163 = FStar_Tactics_Types.goal_env goal  in
                    __tc uu____4163 tm  in
                  bind uu____4154
                    (fun uu____4177  ->
                       match uu____4177 with
                       | (tm1,typ,guard) ->
                           let typ1 =
                             let uu____4190 =
                               FStar_Tactics_Types.goal_env goal  in
                             bnorm uu____4190 typ  in
                           let uu____4191 =
                             let uu____4194 =
                               let uu____4197 = __apply uopt tm1 typ1  in
                               bind uu____4197
                                 (fun uu____4202  ->
                                    let uu____4203 =
                                      FStar_Tactics_Types.goal_env goal  in
                                    proc_guard "apply guard" uu____4203 guard
                                      goal.FStar_Tactics_Types.opts)
                                in
                             focus uu____4194  in
                           let uu____4204 =
                             let uu____4207 =
                               let uu____4208 =
                                 FStar_Tactics_Types.goal_env goal  in
                               tts uu____4208 tm1  in
                             let uu____4209 =
                               let uu____4210 =
                                 FStar_Tactics_Types.goal_env goal  in
                               tts uu____4210 typ1  in
                             let uu____4211 =
                               let uu____4212 =
                                 FStar_Tactics_Types.goal_env goal  in
                               let uu____4213 =
                                 FStar_Tactics_Types.goal_type goal  in
                               tts uu____4212 uu____4213  in
                             fail3
                               "Cannot instantiate %s (of type %s) to match goal (%s)"
                               uu____4207 uu____4209 uu____4211
                              in
                           try_unif uu____4191 uu____4204)))
         in
      FStar_All.pipe_left (wrap_err "apply") uu____4138
  
let (lemma_or_sq :
  FStar_Syntax_Syntax.comp ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun c  ->
    let ct = FStar_Syntax_Util.comp_to_comp_typ_nouniv c  in
    let uu____4236 =
      FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
        FStar_Parser_Const.effect_Lemma_lid
       in
    if uu____4236
    then
      let uu____4243 =
        match ct.FStar_Syntax_Syntax.effect_args with
        | pre::post::uu____4258 ->
            ((FStar_Pervasives_Native.fst pre),
              (FStar_Pervasives_Native.fst post))
        | uu____4297 -> failwith "apply_lemma: impossible: not a lemma"  in
      match uu____4243 with
      | (pre,post) ->
          let post1 =
            let uu____4327 =
              let uu____4336 =
                FStar_Syntax_Syntax.as_arg FStar_Syntax_Util.exp_unit  in
              [uu____4336]  in
            FStar_Syntax_Util.mk_app post uu____4327  in
          FStar_Pervasives_Native.Some (pre, post1)
    else
      (let uu____4360 =
         FStar_Syntax_Util.is_pure_effect ct.FStar_Syntax_Syntax.effect_name
          in
       if uu____4360
       then
         let uu____4367 =
           FStar_Syntax_Util.un_squash ct.FStar_Syntax_Syntax.result_typ  in
         FStar_Util.map_opt uu____4367
           (fun post  -> (FStar_Syntax_Util.t_true, post))
       else FStar_Pervasives_Native.None)
  
let (apply_lemma : FStar_Syntax_Syntax.term -> unit tac) =
  fun tm  ->
    let uu____4400 =
      let uu____4403 =
        mlog
          (fun uu____4408  ->
             let uu____4409 = FStar_Syntax_Print.term_to_string tm  in
             FStar_Util.print1 "apply_lemma: tm = %s\n" uu____4409)
          (fun uu____4413  ->
             let is_unit_t t =
               let uu____4420 =
                 let uu____4421 = FStar_Syntax_Subst.compress t  in
                 uu____4421.FStar_Syntax_Syntax.n  in
               match uu____4420 with
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.unit_lid
                   -> true
               | uu____4425 -> false  in
             let uu____4426 = cur_goal ()  in
             bind uu____4426
               (fun goal  ->
                  let uu____4432 =
                    let uu____4441 = FStar_Tactics_Types.goal_env goal  in
                    __tc uu____4441 tm  in
                  bind uu____4432
                    (fun uu____4456  ->
                       match uu____4456 with
                       | (tm1,t,guard) ->
                           let uu____4468 =
                             FStar_Syntax_Util.arrow_formals_comp t  in
                           (match uu____4468 with
                            | (bs,comp) ->
                                let uu____4495 = lemma_or_sq comp  in
                                (match uu____4495 with
                                 | FStar_Pervasives_Native.None  ->
                                     fail "not a lemma or squashed function"
                                 | FStar_Pervasives_Native.Some (pre,post) ->
                                     let uu____4514 =
                                       FStar_List.fold_left
                                         (fun uu____4556  ->
                                            fun uu____4557  ->
                                              match (uu____4556, uu____4557)
                                              with
                                              | ((uvs,guard1,subst1),(b,aq))
                                                  ->
                                                  let b_t =
                                                    FStar_Syntax_Subst.subst
                                                      subst1
                                                      b.FStar_Syntax_Syntax.sort
                                                     in
                                                  let uu____4648 =
                                                    is_unit_t b_t  in
                                                  if uu____4648
                                                  then
                                                    (((FStar_Syntax_Util.exp_unit,
                                                        aq) :: uvs), guard1,
                                                      ((FStar_Syntax_Syntax.NT
                                                          (b,
                                                            FStar_Syntax_Util.exp_unit))
                                                      :: subst1))
                                                  else
                                                    (let uu____4678 =
                                                       let uu____4691 =
                                                         let uu____4692 =
                                                           FStar_Tactics_Types.goal_type
                                                             goal
                                                            in
                                                         uu____4692.FStar_Syntax_Syntax.pos
                                                          in
                                                       let uu____4695 =
                                                         FStar_Tactics_Types.goal_env
                                                           goal
                                                          in
                                                       FStar_TypeChecker_Util.new_implicit_var
                                                         "apply_lemma"
                                                         uu____4691
                                                         uu____4695 b_t
                                                        in
                                                     match uu____4678 with
                                                     | (u,uu____4711,g_u) ->
                                                         let uu____4725 =
                                                           FStar_TypeChecker_Rel.conj_guard
                                                             guard1 g_u
                                                            in
                                                         (((u, aq) :: uvs),
                                                           uu____4725,
                                                           ((FStar_Syntax_Syntax.NT
                                                               (b, u)) ::
                                                           subst1))))
                                         ([], guard, []) bs
                                        in
                                     (match uu____4514 with
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
                                          let uu____4786 =
                                            let uu____4789 =
                                              FStar_Tactics_Types.goal_env
                                                goal
                                               in
                                            let uu____4790 =
                                              FStar_Syntax_Util.mk_squash
                                                FStar_Syntax_Syntax.U_zero
                                                post1
                                               in
                                            let uu____4791 =
                                              FStar_Tactics_Types.goal_type
                                                goal
                                               in
                                            do_unify uu____4789 uu____4790
                                              uu____4791
                                             in
                                          bind uu____4786
                                            (fun b  ->
                                               if Prims.op_Negation b
                                               then
                                                 let uu____4799 =
                                                   let uu____4800 =
                                                     FStar_Tactics_Types.goal_env
                                                       goal
                                                      in
                                                   tts uu____4800 tm1  in
                                                 let uu____4801 =
                                                   let uu____4802 =
                                                     FStar_Tactics_Types.goal_env
                                                       goal
                                                      in
                                                   let uu____4803 =
                                                     FStar_Syntax_Util.mk_squash
                                                       FStar_Syntax_Syntax.U_zero
                                                       post1
                                                      in
                                                   tts uu____4802 uu____4803
                                                    in
                                                 let uu____4804 =
                                                   let uu____4805 =
                                                     FStar_Tactics_Types.goal_env
                                                       goal
                                                      in
                                                   let uu____4806 =
                                                     FStar_Tactics_Types.goal_type
                                                       goal
                                                      in
                                                   tts uu____4805 uu____4806
                                                    in
                                                 fail3
                                                   "Cannot instantiate lemma %s (with postcondition: %s) to match goal (%s)"
                                                   uu____4799 uu____4801
                                                   uu____4804
                                               else
                                                 (let uu____4808 =
                                                    add_implicits
                                                      implicits.FStar_TypeChecker_Env.implicits
                                                     in
                                                  bind uu____4808
                                                    (fun uu____4813  ->
                                                       let uu____4814 =
                                                         solve' goal
                                                           FStar_Syntax_Util.exp_unit
                                                          in
                                                       bind uu____4814
                                                         (fun uu____4822  ->
                                                            let is_free_uvar
                                                              uv t1 =
                                                              let free_uvars
                                                                =
                                                                let uu____4847
                                                                  =
                                                                  let uu____4850
                                                                    =
                                                                    FStar_Syntax_Free.uvars
                                                                    t1  in
                                                                  FStar_Util.set_elements
                                                                    uu____4850
                                                                   in
                                                                FStar_List.map
                                                                  (fun x  ->
                                                                    x.FStar_Syntax_Syntax.ctx_uvar_head)
                                                                  uu____4847
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
                                                                   let uu____4885
                                                                    =
                                                                    FStar_Tactics_Types.goal_type
                                                                    g'  in
                                                                   is_free_uvar
                                                                    uv
                                                                    uu____4885)
                                                                goals
                                                               in
                                                            let checkone t1
                                                              goals =
                                                              let uu____4901
                                                                =
                                                                FStar_Syntax_Util.head_and_args
                                                                  t1
                                                                 in
                                                              match uu____4901
                                                              with
                                                              | (hd1,uu____4917)
                                                                  ->
                                                                  (match 
                                                                    hd1.FStar_Syntax_Syntax.n
                                                                   with
                                                                   | 
                                                                   FStar_Syntax_Syntax.Tm_uvar
                                                                    (uv,uu____4939)
                                                                    ->
                                                                    appears
                                                                    uv.FStar_Syntax_Syntax.ctx_uvar_head
                                                                    goals
                                                                   | 
                                                                   uu____4960
                                                                    -> false)
                                                               in
                                                            let uu____4961 =
                                                              FStar_All.pipe_right
                                                                implicits.FStar_TypeChecker_Env.implicits
                                                                (mapM
                                                                   (fun
                                                                    uu____5024
                                                                     ->
                                                                    match uu____5024
                                                                    with
                                                                    | 
                                                                    (_msg,term,ctx_uvar,_range)
                                                                    ->
                                                                    let uu____5047
                                                                    =
                                                                    FStar_Syntax_Util.head_and_args
                                                                    term  in
                                                                    (match uu____5047
                                                                    with
                                                                    | 
                                                                    (hd1,uu____5073)
                                                                    ->
                                                                    let uu____5094
                                                                    =
                                                                    let uu____5095
                                                                    =
                                                                    FStar_Syntax_Subst.compress
                                                                    hd1  in
                                                                    uu____5095.FStar_Syntax_Syntax.n
                                                                     in
                                                                    (match uu____5094
                                                                    with
                                                                    | 
                                                                    FStar_Syntax_Syntax.Tm_uvar
                                                                    (ctx_uvar1,uu____5109)
                                                                    ->
                                                                    let goal1
                                                                    =
                                                                    bnorm_goal
                                                                    (let uu___374_5133
                                                                    = goal
                                                                     in
                                                                    {
                                                                    FStar_Tactics_Types.goal_main_env
                                                                    =
                                                                    (uu___374_5133.FStar_Tactics_Types.goal_main_env);
                                                                    FStar_Tactics_Types.goal_ctx_uvar
                                                                    =
                                                                    ctx_uvar1;
                                                                    FStar_Tactics_Types.opts
                                                                    =
                                                                    (uu___374_5133.FStar_Tactics_Types.opts);
                                                                    FStar_Tactics_Types.is_guard
                                                                    =
                                                                    (uu___374_5133.FStar_Tactics_Types.is_guard)
                                                                    })  in
                                                                    ret
                                                                    ([goal1],
                                                                    [])
                                                                    | 
                                                                    uu____5146
                                                                    ->
                                                                    let env =
                                                                    let uu___375_5148
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    goal  in
                                                                    {
                                                                    FStar_TypeChecker_Env.solver
                                                                    =
                                                                    (uu___375_5148.FStar_TypeChecker_Env.solver);
                                                                    FStar_TypeChecker_Env.range
                                                                    =
                                                                    (uu___375_5148.FStar_TypeChecker_Env.range);
                                                                    FStar_TypeChecker_Env.curmodule
                                                                    =
                                                                    (uu___375_5148.FStar_TypeChecker_Env.curmodule);
                                                                    FStar_TypeChecker_Env.gamma
                                                                    =
                                                                    (ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_gamma);
                                                                    FStar_TypeChecker_Env.gamma_sig
                                                                    =
                                                                    (uu___375_5148.FStar_TypeChecker_Env.gamma_sig);
                                                                    FStar_TypeChecker_Env.gamma_cache
                                                                    =
                                                                    (uu___375_5148.FStar_TypeChecker_Env.gamma_cache);
                                                                    FStar_TypeChecker_Env.modules
                                                                    =
                                                                    (uu___375_5148.FStar_TypeChecker_Env.modules);
                                                                    FStar_TypeChecker_Env.expected_typ
                                                                    =
                                                                    (uu___375_5148.FStar_TypeChecker_Env.expected_typ);
                                                                    FStar_TypeChecker_Env.sigtab
                                                                    =
                                                                    (uu___375_5148.FStar_TypeChecker_Env.sigtab);
                                                                    FStar_TypeChecker_Env.is_pattern
                                                                    =
                                                                    (uu___375_5148.FStar_TypeChecker_Env.is_pattern);
                                                                    FStar_TypeChecker_Env.instantiate_imp
                                                                    =
                                                                    (uu___375_5148.FStar_TypeChecker_Env.instantiate_imp);
                                                                    FStar_TypeChecker_Env.effects
                                                                    =
                                                                    (uu___375_5148.FStar_TypeChecker_Env.effects);
                                                                    FStar_TypeChecker_Env.generalize
                                                                    =
                                                                    (uu___375_5148.FStar_TypeChecker_Env.generalize);
                                                                    FStar_TypeChecker_Env.letrecs
                                                                    =
                                                                    (uu___375_5148.FStar_TypeChecker_Env.letrecs);
                                                                    FStar_TypeChecker_Env.top_level
                                                                    =
                                                                    (uu___375_5148.FStar_TypeChecker_Env.top_level);
                                                                    FStar_TypeChecker_Env.check_uvars
                                                                    =
                                                                    (uu___375_5148.FStar_TypeChecker_Env.check_uvars);
                                                                    FStar_TypeChecker_Env.use_eq
                                                                    =
                                                                    (uu___375_5148.FStar_TypeChecker_Env.use_eq);
                                                                    FStar_TypeChecker_Env.is_iface
                                                                    =
                                                                    (uu___375_5148.FStar_TypeChecker_Env.is_iface);
                                                                    FStar_TypeChecker_Env.admit
                                                                    =
                                                                    (uu___375_5148.FStar_TypeChecker_Env.admit);
                                                                    FStar_TypeChecker_Env.lax
                                                                    =
                                                                    (uu___375_5148.FStar_TypeChecker_Env.lax);
                                                                    FStar_TypeChecker_Env.lax_universes
                                                                    =
                                                                    (uu___375_5148.FStar_TypeChecker_Env.lax_universes);
                                                                    FStar_TypeChecker_Env.failhard
                                                                    =
                                                                    (uu___375_5148.FStar_TypeChecker_Env.failhard);
                                                                    FStar_TypeChecker_Env.nosynth
                                                                    =
                                                                    (uu___375_5148.FStar_TypeChecker_Env.nosynth);
                                                                    FStar_TypeChecker_Env.uvar_subtyping
                                                                    =
                                                                    (uu___375_5148.FStar_TypeChecker_Env.uvar_subtyping);
                                                                    FStar_TypeChecker_Env.tc_term
                                                                    =
                                                                    (uu___375_5148.FStar_TypeChecker_Env.tc_term);
                                                                    FStar_TypeChecker_Env.type_of
                                                                    =
                                                                    (uu___375_5148.FStar_TypeChecker_Env.type_of);
                                                                    FStar_TypeChecker_Env.universe_of
                                                                    =
                                                                    (uu___375_5148.FStar_TypeChecker_Env.universe_of);
                                                                    FStar_TypeChecker_Env.check_type_of
                                                                    =
                                                                    (uu___375_5148.FStar_TypeChecker_Env.check_type_of);
                                                                    FStar_TypeChecker_Env.use_bv_sorts
                                                                    =
                                                                    (uu___375_5148.FStar_TypeChecker_Env.use_bv_sorts);
                                                                    FStar_TypeChecker_Env.qtbl_name_and_index
                                                                    =
                                                                    (uu___375_5148.FStar_TypeChecker_Env.qtbl_name_and_index);
                                                                    FStar_TypeChecker_Env.normalized_eff_names
                                                                    =
                                                                    (uu___375_5148.FStar_TypeChecker_Env.normalized_eff_names);
                                                                    FStar_TypeChecker_Env.proof_ns
                                                                    =
                                                                    (uu___375_5148.FStar_TypeChecker_Env.proof_ns);
                                                                    FStar_TypeChecker_Env.synth_hook
                                                                    =
                                                                    (uu___375_5148.FStar_TypeChecker_Env.synth_hook);
                                                                    FStar_TypeChecker_Env.splice
                                                                    =
                                                                    (uu___375_5148.FStar_TypeChecker_Env.splice);
                                                                    FStar_TypeChecker_Env.is_native_tactic
                                                                    =
                                                                    (uu___375_5148.FStar_TypeChecker_Env.is_native_tactic);
                                                                    FStar_TypeChecker_Env.identifier_info
                                                                    =
                                                                    (uu___375_5148.FStar_TypeChecker_Env.identifier_info);
                                                                    FStar_TypeChecker_Env.tc_hooks
                                                                    =
                                                                    (uu___375_5148.FStar_TypeChecker_Env.tc_hooks);
                                                                    FStar_TypeChecker_Env.dsenv
                                                                    =
                                                                    (uu___375_5148.FStar_TypeChecker_Env.dsenv);
                                                                    FStar_TypeChecker_Env.dep_graph
                                                                    =
                                                                    (uu___375_5148.FStar_TypeChecker_Env.dep_graph)
                                                                    }  in
                                                                    let g_typ
                                                                    =
                                                                    let uu____5150
                                                                    =
                                                                    FStar_Options.__temp_fast_implicits
                                                                    ()  in
                                                                    if
                                                                    uu____5150
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
                                                                    let uu____5153
                                                                    =
                                                                    let uu____5160
                                                                    =
                                                                    FStar_TypeChecker_Env.set_expected_typ
                                                                    env
                                                                    ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_typ
                                                                     in
                                                                    env.FStar_TypeChecker_Env.type_of
                                                                    uu____5160
                                                                    term1  in
                                                                    match uu____5153
                                                                    with
                                                                    | 
                                                                    (uu____5161,uu____5162,g_typ)
                                                                    -> g_typ)
                                                                     in
                                                                    let uu____5164
                                                                    =
                                                                    let uu____5169
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    goal  in
                                                                    goal_from_guard
                                                                    "apply_lemma solved arg"
                                                                    uu____5169
                                                                    g_typ
                                                                    goal.FStar_Tactics_Types.opts
                                                                     in
                                                                    bind
                                                                    uu____5164
                                                                    (fun
                                                                    uu___337_5181
                                                                     ->
                                                                    match uu___337_5181
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
                                                            bind uu____4961
                                                              (fun goals_  ->
                                                                 let sub_goals
                                                                   =
                                                                   let uu____5249
                                                                    =
                                                                    FStar_List.map
                                                                    FStar_Pervasives_Native.fst
                                                                    goals_
                                                                     in
                                                                   FStar_List.flatten
                                                                    uu____5249
                                                                    in
                                                                 let smt_goals
                                                                   =
                                                                   let uu____5271
                                                                    =
                                                                    FStar_List.map
                                                                    FStar_Pervasives_Native.snd
                                                                    goals_
                                                                     in
                                                                   FStar_List.flatten
                                                                    uu____5271
                                                                    in
                                                                 let rec filter'
                                                                   f xs =
                                                                   match xs
                                                                   with
                                                                   | 
                                                                   [] -> []
                                                                   | 
                                                                   x::xs1 ->
                                                                    let uu____5332
                                                                    = f x xs1
                                                                     in
                                                                    if
                                                                    uu____5332
                                                                    then
                                                                    let uu____5335
                                                                    =
                                                                    filter' f
                                                                    xs1  in x
                                                                    ::
                                                                    uu____5335
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
                                                                    let uu____5349
                                                                    =
                                                                    let uu____5350
                                                                    =
                                                                    FStar_Tactics_Types.goal_witness
                                                                    g  in
                                                                    checkone
                                                                    uu____5350
                                                                    goals  in
                                                                    Prims.op_Negation
                                                                    uu____5349)
                                                                    sub_goals
                                                                    in
                                                                 let uu____5351
                                                                   =
                                                                   let uu____5354
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    goal  in
                                                                   proc_guard
                                                                    "apply_lemma guard"
                                                                    uu____5354
                                                                    guard
                                                                    goal.FStar_Tactics_Types.opts
                                                                    in
                                                                 bind
                                                                   uu____5351
                                                                   (fun
                                                                    uu____5357
                                                                     ->
                                                                    let uu____5358
                                                                    =
                                                                    let uu____5361
                                                                    =
                                                                    let uu____5362
                                                                    =
                                                                    let uu____5363
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    goal  in
                                                                    let uu____5364
                                                                    =
                                                                    FStar_Syntax_Util.mk_squash
                                                                    FStar_Syntax_Syntax.U_zero
                                                                    pre1  in
                                                                    istrivial
                                                                    uu____5363
                                                                    uu____5364
                                                                     in
                                                                    Prims.op_Negation
                                                                    uu____5362
                                                                     in
                                                                    if
                                                                    uu____5361
                                                                    then
                                                                    let uu____5367
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    goal  in
                                                                    add_irrelevant_goal
                                                                    "apply_lemma precondition"
                                                                    uu____5367
                                                                    pre1
                                                                    goal.FStar_Tactics_Types.opts
                                                                    else
                                                                    ret ()
                                                                     in
                                                                    bind
                                                                    uu____5358
                                                                    (fun
                                                                    uu____5371
                                                                     ->
                                                                    let uu____5372
                                                                    =
                                                                    add_smt_goals
                                                                    smt_goals
                                                                     in
                                                                    bind
                                                                    uu____5372
                                                                    (fun
                                                                    uu____5376
                                                                     ->
                                                                    add_goals
                                                                    sub_goals1))))))))))))))
         in
      focus uu____4403  in
    FStar_All.pipe_left (wrap_err "apply_lemma") uu____4400
  
let (destruct_eq' :
  FStar_Reflection_Data.typ ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun typ  ->
    let uu____5398 = FStar_Syntax_Util.destruct_typ_as_formula typ  in
    match uu____5398 with
    | FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn
        (l,uu____5408::(e1,uu____5410)::(e2,uu____5412)::[])) when
        FStar_Ident.lid_equals l FStar_Parser_Const.eq2_lid ->
        FStar_Pervasives_Native.Some (e1, e2)
    | uu____5455 -> FStar_Pervasives_Native.None
  
let (destruct_eq :
  FStar_Reflection_Data.typ ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun typ  ->
    let uu____5479 = destruct_eq' typ  in
    match uu____5479 with
    | FStar_Pervasives_Native.Some t -> FStar_Pervasives_Native.Some t
    | FStar_Pervasives_Native.None  ->
        let uu____5509 = FStar_Syntax_Util.un_squash typ  in
        (match uu____5509 with
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
        let uu____5571 = FStar_TypeChecker_Env.pop_bv e1  in
        match uu____5571 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (bv',e') ->
            if FStar_Syntax_Syntax.bv_eq bvar bv'
            then FStar_Pervasives_Native.Some (e', [])
            else
              (let uu____5619 = aux e'  in
               FStar_Util.map_opt uu____5619
                 (fun uu____5643  ->
                    match uu____5643 with | (e'',bvs) -> (e'', (bv' :: bvs))))
         in
      let uu____5664 = aux e  in
      FStar_Util.map_opt uu____5664
        (fun uu____5688  ->
           match uu____5688 with | (e',bvs) -> (e', (FStar_List.rev bvs)))
  
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
          let uu____5755 =
            let uu____5764 = FStar_Tactics_Types.goal_env g  in
            split_env b1 uu____5764  in
          FStar_Util.map_opt uu____5755
            (fun uu____5779  ->
               match uu____5779 with
               | (e0,bvs) ->
                   let s1 bv =
                     let uu___376_5798 = bv  in
                     let uu____5799 =
                       FStar_Syntax_Subst.subst s bv.FStar_Syntax_Syntax.sort
                        in
                     {
                       FStar_Syntax_Syntax.ppname =
                         (uu___376_5798.FStar_Syntax_Syntax.ppname);
                       FStar_Syntax_Syntax.index =
                         (uu___376_5798.FStar_Syntax_Syntax.index);
                       FStar_Syntax_Syntax.sort = uu____5799
                     }  in
                   let bvs1 = FStar_List.map s1 bvs  in
                   let new_env = push_bvs e0 (b2 :: bvs1)  in
                   let new_goal =
                     let uu___377_5807 = g.FStar_Tactics_Types.goal_ctx_uvar
                        in
                     let uu____5808 =
                       FStar_TypeChecker_Env.all_binders new_env  in
                     let uu____5815 =
                       let uu____5818 = FStar_Tactics_Types.goal_type g  in
                       FStar_Syntax_Subst.subst s uu____5818  in
                     {
                       FStar_Syntax_Syntax.ctx_uvar_head =
                         (uu___377_5807.FStar_Syntax_Syntax.ctx_uvar_head);
                       FStar_Syntax_Syntax.ctx_uvar_gamma =
                         (new_env.FStar_TypeChecker_Env.gamma);
                       FStar_Syntax_Syntax.ctx_uvar_binders = uu____5808;
                       FStar_Syntax_Syntax.ctx_uvar_typ = uu____5815;
                       FStar_Syntax_Syntax.ctx_uvar_reason =
                         (uu___377_5807.FStar_Syntax_Syntax.ctx_uvar_reason);
                       FStar_Syntax_Syntax.ctx_uvar_should_check =
                         (uu___377_5807.FStar_Syntax_Syntax.ctx_uvar_should_check);
                       FStar_Syntax_Syntax.ctx_uvar_range =
                         (uu___377_5807.FStar_Syntax_Syntax.ctx_uvar_range)
                     }  in
                   let uu___378_5819 = g  in
                   {
                     FStar_Tactics_Types.goal_main_env =
                       (uu___378_5819.FStar_Tactics_Types.goal_main_env);
                     FStar_Tactics_Types.goal_ctx_uvar = new_goal;
                     FStar_Tactics_Types.opts =
                       (uu___378_5819.FStar_Tactics_Types.opts);
                     FStar_Tactics_Types.is_guard =
                       (uu___378_5819.FStar_Tactics_Types.is_guard)
                   })
  
let (rewrite : FStar_Syntax_Syntax.binder -> unit tac) =
  fun h  ->
    let uu____5829 =
      let uu____5832 = cur_goal ()  in
      bind uu____5832
        (fun goal  ->
           let uu____5840 = h  in
           match uu____5840 with
           | (bv,uu____5844) ->
               mlog
                 (fun uu____5848  ->
                    let uu____5849 = FStar_Syntax_Print.bv_to_string bv  in
                    let uu____5850 =
                      FStar_Syntax_Print.term_to_string
                        bv.FStar_Syntax_Syntax.sort
                       in
                    FStar_Util.print2 "+++Rewrite %s : %s\n" uu____5849
                      uu____5850)
                 (fun uu____5853  ->
                    let uu____5854 =
                      let uu____5863 = FStar_Tactics_Types.goal_env goal  in
                      split_env bv uu____5863  in
                    match uu____5854 with
                    | FStar_Pervasives_Native.None  ->
                        fail "binder not found in environment"
                    | FStar_Pervasives_Native.Some (e0,bvs) ->
                        let uu____5884 =
                          destruct_eq bv.FStar_Syntax_Syntax.sort  in
                        (match uu____5884 with
                         | FStar_Pervasives_Native.Some (x,e) ->
                             let uu____5899 =
                               let uu____5900 = FStar_Syntax_Subst.compress x
                                  in
                               uu____5900.FStar_Syntax_Syntax.n  in
                             (match uu____5899 with
                              | FStar_Syntax_Syntax.Tm_name x1 ->
                                  let s = [FStar_Syntax_Syntax.NT (x1, e)]
                                     in
                                  let s1 bv1 =
                                    let uu___379_5917 = bv1  in
                                    let uu____5918 =
                                      FStar_Syntax_Subst.subst s
                                        bv1.FStar_Syntax_Syntax.sort
                                       in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___379_5917.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___379_5917.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = uu____5918
                                    }  in
                                  let bvs1 = FStar_List.map s1 bvs  in
                                  let new_env = push_bvs e0 (bv :: bvs1)  in
                                  let new_goal =
                                    let uu___380_5926 =
                                      goal.FStar_Tactics_Types.goal_ctx_uvar
                                       in
                                    let uu____5927 =
                                      FStar_TypeChecker_Env.all_binders
                                        new_env
                                       in
                                    let uu____5934 =
                                      let uu____5937 =
                                        FStar_Tactics_Types.goal_type goal
                                         in
                                      FStar_Syntax_Subst.subst s uu____5937
                                       in
                                    {
                                      FStar_Syntax_Syntax.ctx_uvar_head =
                                        (uu___380_5926.FStar_Syntax_Syntax.ctx_uvar_head);
                                      FStar_Syntax_Syntax.ctx_uvar_gamma =
                                        (new_env.FStar_TypeChecker_Env.gamma);
                                      FStar_Syntax_Syntax.ctx_uvar_binders =
                                        uu____5927;
                                      FStar_Syntax_Syntax.ctx_uvar_typ =
                                        uu____5934;
                                      FStar_Syntax_Syntax.ctx_uvar_reason =
                                        (uu___380_5926.FStar_Syntax_Syntax.ctx_uvar_reason);
                                      FStar_Syntax_Syntax.ctx_uvar_should_check
                                        =
                                        (uu___380_5926.FStar_Syntax_Syntax.ctx_uvar_should_check);
                                      FStar_Syntax_Syntax.ctx_uvar_range =
                                        (uu___380_5926.FStar_Syntax_Syntax.ctx_uvar_range)
                                    }  in
                                  replace_cur
                                    (let uu___381_5940 = goal  in
                                     {
                                       FStar_Tactics_Types.goal_main_env =
                                         (uu___381_5940.FStar_Tactics_Types.goal_main_env);
                                       FStar_Tactics_Types.goal_ctx_uvar =
                                         new_goal;
                                       FStar_Tactics_Types.opts =
                                         (uu___381_5940.FStar_Tactics_Types.opts);
                                       FStar_Tactics_Types.is_guard =
                                         (uu___381_5940.FStar_Tactics_Types.is_guard)
                                     })
                              | uu____5941 ->
                                  fail
                                    "Not an equality hypothesis with a variable on the LHS")
                         | uu____5942 -> fail "Not an equality hypothesis")))
       in
    FStar_All.pipe_left (wrap_err "rewrite") uu____5829
  
let (rename_to : FStar_Syntax_Syntax.binder -> Prims.string -> unit tac) =
  fun b  ->
    fun s  ->
      let uu____5967 =
        let uu____5970 = cur_goal ()  in
        bind uu____5970
          (fun goal  ->
             let uu____5981 = b  in
             match uu____5981 with
             | (bv,uu____5985) ->
                 let bv' =
                   let uu____5987 =
                     let uu___382_5988 = bv  in
                     let uu____5989 =
                       FStar_Ident.mk_ident
                         (s,
                           ((bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange))
                        in
                     {
                       FStar_Syntax_Syntax.ppname = uu____5989;
                       FStar_Syntax_Syntax.index =
                         (uu___382_5988.FStar_Syntax_Syntax.index);
                       FStar_Syntax_Syntax.sort =
                         (uu___382_5988.FStar_Syntax_Syntax.sort)
                     }  in
                   FStar_Syntax_Syntax.freshen_bv uu____5987  in
                 let s1 =
                   let uu____5993 =
                     let uu____5994 =
                       let uu____6001 = FStar_Syntax_Syntax.bv_to_name bv'
                          in
                       (bv, uu____6001)  in
                     FStar_Syntax_Syntax.NT uu____5994  in
                   [uu____5993]  in
                 let uu____6006 = subst_goal bv bv' s1 goal  in
                 (match uu____6006 with
                  | FStar_Pervasives_Native.None  ->
                      fail "binder not found in environment"
                  | FStar_Pervasives_Native.Some goal1 -> replace_cur goal1))
         in
      FStar_All.pipe_left (wrap_err "rename_to") uu____5967
  
let (binder_retype : FStar_Syntax_Syntax.binder -> unit tac) =
  fun b  ->
    let uu____6025 =
      let uu____6028 = cur_goal ()  in
      bind uu____6028
        (fun goal  ->
           let uu____6037 = b  in
           match uu____6037 with
           | (bv,uu____6041) ->
               let uu____6042 =
                 let uu____6051 = FStar_Tactics_Types.goal_env goal  in
                 split_env bv uu____6051  in
               (match uu____6042 with
                | FStar_Pervasives_Native.None  ->
                    fail "binder is not present in environment"
                | FStar_Pervasives_Native.Some (e0,bvs) ->
                    let uu____6072 = FStar_Syntax_Util.type_u ()  in
                    (match uu____6072 with
                     | (ty,u) ->
                         let uu____6081 = new_uvar "binder_retype" e0 ty  in
                         bind uu____6081
                           (fun uu____6099  ->
                              match uu____6099 with
                              | (t',u_t') ->
                                  let bv'' =
                                    let uu___383_6109 = bv  in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___383_6109.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___383_6109.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = t'
                                    }  in
                                  let s =
                                    let uu____6113 =
                                      let uu____6114 =
                                        let uu____6121 =
                                          FStar_Syntax_Syntax.bv_to_name bv''
                                           in
                                        (bv, uu____6121)  in
                                      FStar_Syntax_Syntax.NT uu____6114  in
                                    [uu____6113]  in
                                  let bvs1 =
                                    FStar_List.map
                                      (fun b1  ->
                                         let uu___384_6133 = b1  in
                                         let uu____6134 =
                                           FStar_Syntax_Subst.subst s
                                             b1.FStar_Syntax_Syntax.sort
                                            in
                                         {
                                           FStar_Syntax_Syntax.ppname =
                                             (uu___384_6133.FStar_Syntax_Syntax.ppname);
                                           FStar_Syntax_Syntax.index =
                                             (uu___384_6133.FStar_Syntax_Syntax.index);
                                           FStar_Syntax_Syntax.sort =
                                             uu____6134
                                         }) bvs
                                     in
                                  let env' = push_bvs e0 (bv'' :: bvs1)  in
                                  bind __dismiss
                                    (fun uu____6141  ->
                                       let new_goal =
                                         let uu____6143 =
                                           FStar_Tactics_Types.goal_with_env
                                             goal env'
                                            in
                                         let uu____6144 =
                                           let uu____6145 =
                                             FStar_Tactics_Types.goal_type
                                               goal
                                              in
                                           FStar_Syntax_Subst.subst s
                                             uu____6145
                                            in
                                         FStar_Tactics_Types.goal_with_type
                                           uu____6143 uu____6144
                                          in
                                       let uu____6146 = add_goals [new_goal]
                                          in
                                       bind uu____6146
                                         (fun uu____6151  ->
                                            let uu____6152 =
                                              FStar_Syntax_Util.mk_eq2
                                                (FStar_Syntax_Syntax.U_succ u)
                                                ty
                                                bv.FStar_Syntax_Syntax.sort
                                                t'
                                               in
                                            add_irrelevant_goal
                                              "binder_retype equation" e0
                                              uu____6152
                                              goal.FStar_Tactics_Types.opts))))))
       in
    FStar_All.pipe_left (wrap_err "binder_retype") uu____6025
  
let (norm_binder_type :
  FStar_Syntax_Embeddings.norm_step Prims.list ->
    FStar_Syntax_Syntax.binder -> unit tac)
  =
  fun s  ->
    fun b  ->
      let uu____6175 =
        let uu____6178 = cur_goal ()  in
        bind uu____6178
          (fun goal  ->
             let uu____6187 = b  in
             match uu____6187 with
             | (bv,uu____6191) ->
                 let uu____6192 =
                   let uu____6201 = FStar_Tactics_Types.goal_env goal  in
                   split_env bv uu____6201  in
                 (match uu____6192 with
                  | FStar_Pervasives_Native.None  ->
                      fail "binder is not present in environment"
                  | FStar_Pervasives_Native.Some (e0,bvs) ->
                      let steps =
                        let uu____6225 =
                          FStar_TypeChecker_Normalize.tr_norm_steps s  in
                        FStar_List.append
                          [FStar_TypeChecker_Normalize.Reify;
                          FStar_TypeChecker_Normalize.UnfoldTac] uu____6225
                         in
                      let sort' =
                        normalize steps e0 bv.FStar_Syntax_Syntax.sort  in
                      let bv' =
                        let uu___385_6230 = bv  in
                        {
                          FStar_Syntax_Syntax.ppname =
                            (uu___385_6230.FStar_Syntax_Syntax.ppname);
                          FStar_Syntax_Syntax.index =
                            (uu___385_6230.FStar_Syntax_Syntax.index);
                          FStar_Syntax_Syntax.sort = sort'
                        }  in
                      let env' = push_bvs e0 (bv' :: bvs)  in
                      let uu____6232 =
                        FStar_Tactics_Types.goal_with_env goal env'  in
                      replace_cur uu____6232))
         in
      FStar_All.pipe_left (wrap_err "norm_binder_type") uu____6175
  
let (revert : unit -> unit tac) =
  fun uu____6243  ->
    let uu____6246 = cur_goal ()  in
    bind uu____6246
      (fun goal  ->
         let uu____6252 =
           let uu____6259 = FStar_Tactics_Types.goal_env goal  in
           FStar_TypeChecker_Env.pop_bv uu____6259  in
         match uu____6252 with
         | FStar_Pervasives_Native.None  ->
             fail "Cannot revert; empty context"
         | FStar_Pervasives_Native.Some (x,env') ->
             let typ' =
               let uu____6275 =
                 let uu____6278 = FStar_Tactics_Types.goal_type goal  in
                 FStar_Syntax_Syntax.mk_Total uu____6278  in
               FStar_Syntax_Util.arrow [(x, FStar_Pervasives_Native.None)]
                 uu____6275
                in
             let uu____6287 = new_uvar "revert" env' typ'  in
             bind uu____6287
               (fun uu____6302  ->
                  match uu____6302 with
                  | (r,u_r) ->
                      let uu____6311 =
                        let uu____6314 =
                          let uu____6315 =
                            let uu____6316 =
                              FStar_Tactics_Types.goal_type goal  in
                            uu____6316.FStar_Syntax_Syntax.pos  in
                          let uu____6319 =
                            let uu____6324 =
                              let uu____6325 =
                                let uu____6332 =
                                  FStar_Syntax_Syntax.bv_to_name x  in
                                FStar_Syntax_Syntax.as_arg uu____6332  in
                              [uu____6325]  in
                            FStar_Syntax_Syntax.mk_Tm_app r uu____6324  in
                          uu____6319 FStar_Pervasives_Native.None uu____6315
                           in
                        set_solution goal uu____6314  in
                      bind uu____6311
                        (fun uu____6349  ->
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
      let uu____6361 = FStar_Syntax_Free.names t  in
      FStar_Util.set_mem bv uu____6361
  
let rec (clear : FStar_Syntax_Syntax.binder -> unit tac) =
  fun b  ->
    let bv = FStar_Pervasives_Native.fst b  in
    let uu____6374 = cur_goal ()  in
    bind uu____6374
      (fun goal  ->
         mlog
           (fun uu____6382  ->
              let uu____6383 = FStar_Syntax_Print.binder_to_string b  in
              let uu____6384 =
                let uu____6385 =
                  let uu____6386 =
                    let uu____6393 = FStar_Tactics_Types.goal_env goal  in
                    FStar_TypeChecker_Env.all_binders uu____6393  in
                  FStar_All.pipe_right uu____6386 FStar_List.length  in
                FStar_All.pipe_right uu____6385 FStar_Util.string_of_int  in
              FStar_Util.print2 "Clear of (%s), env has %s binders\n"
                uu____6383 uu____6384)
           (fun uu____6406  ->
              let uu____6407 =
                let uu____6416 = FStar_Tactics_Types.goal_env goal  in
                split_env bv uu____6416  in
              match uu____6407 with
              | FStar_Pervasives_Native.None  ->
                  fail "Cannot clear; binder not in environment"
              | FStar_Pervasives_Native.Some (e',bvs) ->
                  let rec check1 bvs1 =
                    match bvs1 with
                    | [] -> ret ()
                    | bv'::bvs2 ->
                        let uu____6455 =
                          free_in bv bv'.FStar_Syntax_Syntax.sort  in
                        if uu____6455
                        then
                          let uu____6458 =
                            let uu____6459 =
                              FStar_Syntax_Print.bv_to_string bv'  in
                            FStar_Util.format1
                              "Cannot clear; binder present in the type of %s"
                              uu____6459
                             in
                          fail uu____6458
                        else check1 bvs2
                     in
                  let uu____6461 =
                    let uu____6462 = FStar_Tactics_Types.goal_type goal  in
                    free_in bv uu____6462  in
                  if uu____6461
                  then fail "Cannot clear; binder present in goal"
                  else
                    (let uu____6466 = check1 bvs  in
                     bind uu____6466
                       (fun uu____6472  ->
                          let env' = push_bvs e' bvs  in
                          let uu____6474 =
                            let uu____6481 =
                              FStar_Tactics_Types.goal_type goal  in
                            new_uvar "clear.witness" env' uu____6481  in
                          bind uu____6474
                            (fun uu____6490  ->
                               match uu____6490 with
                               | (ut,uvar_ut) ->
                                   let uu____6499 = set_solution goal ut  in
                                   bind uu____6499
                                     (fun uu____6504  ->
                                        let uu____6505 =
                                          FStar_Tactics_Types.mk_goal env'
                                            uvar_ut
                                            goal.FStar_Tactics_Types.opts
                                            goal.FStar_Tactics_Types.is_guard
                                           in
                                        replace_cur uu____6505))))))
  
let (clear_top : unit -> unit tac) =
  fun uu____6512  ->
    let uu____6515 = cur_goal ()  in
    bind uu____6515
      (fun goal  ->
         let uu____6521 =
           let uu____6528 = FStar_Tactics_Types.goal_env goal  in
           FStar_TypeChecker_Env.pop_bv uu____6528  in
         match uu____6521 with
         | FStar_Pervasives_Native.None  ->
             fail "Cannot clear; empty context"
         | FStar_Pervasives_Native.Some (x,uu____6536) ->
             let uu____6541 = FStar_Syntax_Syntax.mk_binder x  in
             clear uu____6541)
  
let (prune : Prims.string -> unit tac) =
  fun s  ->
    let uu____6551 = cur_goal ()  in
    bind uu____6551
      (fun g  ->
         let ctx = FStar_Tactics_Types.goal_env g  in
         let ctx' =
           let uu____6561 = FStar_Ident.path_of_text s  in
           FStar_TypeChecker_Env.rem_proof_ns ctx uu____6561  in
         let g' = FStar_Tactics_Types.goal_with_env g ctx'  in
         bind __dismiss (fun uu____6564  -> add_goals [g']))
  
let (addns : Prims.string -> unit tac) =
  fun s  ->
    let uu____6574 = cur_goal ()  in
    bind uu____6574
      (fun g  ->
         let ctx = FStar_Tactics_Types.goal_env g  in
         let ctx' =
           let uu____6584 = FStar_Ident.path_of_text s  in
           FStar_TypeChecker_Env.add_proof_ns ctx uu____6584  in
         let g' = FStar_Tactics_Types.goal_with_env g ctx'  in
         bind __dismiss (fun uu____6587  -> add_goals [g']))
  
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
            let uu____6627 = FStar_Syntax_Subst.compress t  in
            uu____6627.FStar_Syntax_Syntax.n  in
          let uu____6630 =
            if d = FStar_Tactics_Types.TopDown
            then
              f env
                (let uu___389_6636 = t  in
                 {
                   FStar_Syntax_Syntax.n = tn;
                   FStar_Syntax_Syntax.pos =
                     (uu___389_6636.FStar_Syntax_Syntax.pos);
                   FStar_Syntax_Syntax.vars =
                     (uu___389_6636.FStar_Syntax_Syntax.vars)
                 })
            else ret t  in
          bind uu____6630
            (fun t1  ->
               let ff = tac_fold_env d f env  in
               let tn1 =
                 let uu____6652 =
                   let uu____6653 = FStar_Syntax_Subst.compress t1  in
                   uu____6653.FStar_Syntax_Syntax.n  in
                 match uu____6652 with
                 | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
                     let uu____6680 = ff hd1  in
                     bind uu____6680
                       (fun hd2  ->
                          let fa uu____6702 =
                            match uu____6702 with
                            | (a,q) ->
                                let uu____6715 = ff a  in
                                bind uu____6715 (fun a1  -> ret (a1, q))
                             in
                          let uu____6728 = mapM fa args  in
                          bind uu____6728
                            (fun args1  ->
                               ret (FStar_Syntax_Syntax.Tm_app (hd2, args1))))
                 | FStar_Syntax_Syntax.Tm_abs (bs,t2,k) ->
                     let uu____6794 = FStar_Syntax_Subst.open_term bs t2  in
                     (match uu____6794 with
                      | (bs1,t') ->
                          let uu____6803 =
                            let uu____6806 =
                              FStar_TypeChecker_Env.push_binders env bs1  in
                            tac_fold_env d f uu____6806 t'  in
                          bind uu____6803
                            (fun t''  ->
                               let uu____6810 =
                                 let uu____6811 =
                                   let uu____6828 =
                                     FStar_Syntax_Subst.close_binders bs1  in
                                   let uu____6835 =
                                     FStar_Syntax_Subst.close bs1 t''  in
                                   (uu____6828, uu____6835, k)  in
                                 FStar_Syntax_Syntax.Tm_abs uu____6811  in
                               ret uu____6810))
                 | FStar_Syntax_Syntax.Tm_arrow (bs,k) -> ret tn
                 | FStar_Syntax_Syntax.Tm_match (hd1,brs) ->
                     let uu____6904 = ff hd1  in
                     bind uu____6904
                       (fun hd2  ->
                          let ffb br =
                            let uu____6919 =
                              FStar_Syntax_Subst.open_branch br  in
                            match uu____6919 with
                            | (pat,w,e) ->
                                let bvs = FStar_Syntax_Syntax.pat_bvs pat  in
                                let ff1 =
                                  let uu____6951 =
                                    FStar_TypeChecker_Env.push_bvs env bvs
                                     in
                                  tac_fold_env d f uu____6951  in
                                let uu____6952 = ff1 e  in
                                bind uu____6952
                                  (fun e1  ->
                                     let br1 =
                                       FStar_Syntax_Subst.close_branch
                                         (pat, w, e1)
                                        in
                                     ret br1)
                             in
                          let uu____6967 = mapM ffb brs  in
                          bind uu____6967
                            (fun brs1  ->
                               ret (FStar_Syntax_Syntax.Tm_match (hd2, brs1))))
                 | FStar_Syntax_Syntax.Tm_let
                     ((false
                       ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inl bv;
                          FStar_Syntax_Syntax.lbunivs = uu____7011;
                          FStar_Syntax_Syntax.lbtyp = uu____7012;
                          FStar_Syntax_Syntax.lbeff = uu____7013;
                          FStar_Syntax_Syntax.lbdef = def;
                          FStar_Syntax_Syntax.lbattrs = uu____7015;
                          FStar_Syntax_Syntax.lbpos = uu____7016;_}::[]),e)
                     ->
                     let lb =
                       let uu____7041 =
                         let uu____7042 = FStar_Syntax_Subst.compress t1  in
                         uu____7042.FStar_Syntax_Syntax.n  in
                       match uu____7041 with
                       | FStar_Syntax_Syntax.Tm_let
                           ((false ,lb::[]),uu____7046) -> lb
                       | uu____7059 -> failwith "impossible"  in
                     let fflb lb1 =
                       let uu____7068 = ff lb1.FStar_Syntax_Syntax.lbdef  in
                       bind uu____7068
                         (fun def1  ->
                            ret
                              (let uu___386_7074 = lb1  in
                               {
                                 FStar_Syntax_Syntax.lbname =
                                   (uu___386_7074.FStar_Syntax_Syntax.lbname);
                                 FStar_Syntax_Syntax.lbunivs =
                                   (uu___386_7074.FStar_Syntax_Syntax.lbunivs);
                                 FStar_Syntax_Syntax.lbtyp =
                                   (uu___386_7074.FStar_Syntax_Syntax.lbtyp);
                                 FStar_Syntax_Syntax.lbeff =
                                   (uu___386_7074.FStar_Syntax_Syntax.lbeff);
                                 FStar_Syntax_Syntax.lbdef = def1;
                                 FStar_Syntax_Syntax.lbattrs =
                                   (uu___386_7074.FStar_Syntax_Syntax.lbattrs);
                                 FStar_Syntax_Syntax.lbpos =
                                   (uu___386_7074.FStar_Syntax_Syntax.lbpos)
                               }))
                        in
                     let uu____7075 = fflb lb  in
                     bind uu____7075
                       (fun lb1  ->
                          let uu____7085 =
                            let uu____7090 =
                              let uu____7091 =
                                FStar_Syntax_Syntax.mk_binder bv  in
                              [uu____7091]  in
                            FStar_Syntax_Subst.open_term uu____7090 e  in
                          match uu____7085 with
                          | (bs,e1) ->
                              let ff1 =
                                let uu____7115 =
                                  FStar_TypeChecker_Env.push_binders env bs
                                   in
                                tac_fold_env d f uu____7115  in
                              let uu____7116 = ff1 e1  in
                              bind uu____7116
                                (fun e2  ->
                                   let e3 = FStar_Syntax_Subst.close bs e2
                                      in
                                   ret
                                     (FStar_Syntax_Syntax.Tm_let
                                        ((false, [lb1]), e3))))
                 | FStar_Syntax_Syntax.Tm_let ((true ,lbs),e) ->
                     let fflb lb =
                       let uu____7157 = ff lb.FStar_Syntax_Syntax.lbdef  in
                       bind uu____7157
                         (fun def  ->
                            ret
                              (let uu___387_7163 = lb  in
                               {
                                 FStar_Syntax_Syntax.lbname =
                                   (uu___387_7163.FStar_Syntax_Syntax.lbname);
                                 FStar_Syntax_Syntax.lbunivs =
                                   (uu___387_7163.FStar_Syntax_Syntax.lbunivs);
                                 FStar_Syntax_Syntax.lbtyp =
                                   (uu___387_7163.FStar_Syntax_Syntax.lbtyp);
                                 FStar_Syntax_Syntax.lbeff =
                                   (uu___387_7163.FStar_Syntax_Syntax.lbeff);
                                 FStar_Syntax_Syntax.lbdef = def;
                                 FStar_Syntax_Syntax.lbattrs =
                                   (uu___387_7163.FStar_Syntax_Syntax.lbattrs);
                                 FStar_Syntax_Syntax.lbpos =
                                   (uu___387_7163.FStar_Syntax_Syntax.lbpos)
                               }))
                        in
                     let uu____7164 = FStar_Syntax_Subst.open_let_rec lbs e
                        in
                     (match uu____7164 with
                      | (lbs1,e1) ->
                          let uu____7179 = mapM fflb lbs1  in
                          bind uu____7179
                            (fun lbs2  ->
                               let uu____7191 = ff e1  in
                               bind uu____7191
                                 (fun e2  ->
                                    let uu____7199 =
                                      FStar_Syntax_Subst.close_let_rec lbs2
                                        e2
                                       in
                                    match uu____7199 with
                                    | (lbs3,e3) ->
                                        ret
                                          (FStar_Syntax_Syntax.Tm_let
                                             ((true, lbs3), e3)))))
                 | FStar_Syntax_Syntax.Tm_ascribed (t2,asc,eff) ->
                     let uu____7267 = ff t2  in
                     bind uu____7267
                       (fun t3  ->
                          ret
                            (FStar_Syntax_Syntax.Tm_ascribed (t3, asc, eff)))
                 | FStar_Syntax_Syntax.Tm_meta (t2,m) ->
                     let uu____7298 = ff t2  in
                     bind uu____7298
                       (fun t3  -> ret (FStar_Syntax_Syntax.Tm_meta (t3, m)))
                 | uu____7305 -> ret tn  in
               bind tn1
                 (fun tn2  ->
                    let t' =
                      let uu___388_7312 = t1  in
                      {
                        FStar_Syntax_Syntax.n = tn2;
                        FStar_Syntax_Syntax.pos =
                          (uu___388_7312.FStar_Syntax_Syntax.pos);
                        FStar_Syntax_Syntax.vars =
                          (uu___388_7312.FStar_Syntax_Syntax.vars)
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
            let uu____7349 = FStar_TypeChecker_TcTerm.tc_term env t  in
            match uu____7349 with
            | (t1,lcomp,g) ->
                let uu____7361 =
                  (let uu____7364 =
                     FStar_Syntax_Util.is_pure_or_ghost_lcomp lcomp  in
                   Prims.op_Negation uu____7364) ||
                    (let uu____7366 = FStar_TypeChecker_Rel.is_trivial g  in
                     Prims.op_Negation uu____7366)
                   in
                if uu____7361
                then ret t1
                else
                  (let rewrite_eq =
                     let typ = lcomp.FStar_Syntax_Syntax.res_typ  in
                     let uu____7374 = new_uvar "pointwise_rec" env typ  in
                     bind uu____7374
                       (fun uu____7390  ->
                          match uu____7390 with
                          | (ut,uvar_ut) ->
                              (log ps
                                 (fun uu____7403  ->
                                    let uu____7404 =
                                      FStar_Syntax_Print.term_to_string t1
                                       in
                                    let uu____7405 =
                                      FStar_Syntax_Print.term_to_string ut
                                       in
                                    FStar_Util.print2
                                      "Pointwise_rec: making equality\n\t%s ==\n\t%s\n"
                                      uu____7404 uu____7405);
                               (let uu____7406 =
                                  let uu____7409 =
                                    let uu____7410 =
                                      FStar_TypeChecker_TcTerm.universe_of
                                        env typ
                                       in
                                    FStar_Syntax_Util.mk_eq2 uu____7410 typ
                                      t1 ut
                                     in
                                  add_irrelevant_goal
                                    "pointwise_rec equation" env uu____7409
                                    opts
                                   in
                                bind uu____7406
                                  (fun uu____7413  ->
                                     let uu____7414 =
                                       bind tau
                                         (fun uu____7420  ->
                                            let ut1 =
                                              FStar_TypeChecker_Normalize.reduce_uvar_solutions
                                                env ut
                                               in
                                            log ps
                                              (fun uu____7426  ->
                                                 let uu____7427 =
                                                   FStar_Syntax_Print.term_to_string
                                                     t1
                                                    in
                                                 let uu____7428 =
                                                   FStar_Syntax_Print.term_to_string
                                                     ut1
                                                    in
                                                 FStar_Util.print2
                                                   "Pointwise_rec: succeeded rewriting\n\t%s to\n\t%s\n"
                                                   uu____7427 uu____7428);
                                            ret ut1)
                                        in
                                     focus uu____7414))))
                      in
                   let uu____7429 = trytac' rewrite_eq  in
                   bind uu____7429
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
          let uu____7627 = FStar_Syntax_Subst.compress t  in
          maybe_continue ctrl uu____7627
            (fun t1  ->
               let uu____7635 =
                 f env
                   (let uu___392_7644 = t1  in
                    {
                      FStar_Syntax_Syntax.n = (t1.FStar_Syntax_Syntax.n);
                      FStar_Syntax_Syntax.pos =
                        (uu___392_7644.FStar_Syntax_Syntax.pos);
                      FStar_Syntax_Syntax.vars =
                        (uu___392_7644.FStar_Syntax_Syntax.vars)
                    })
                  in
               bind uu____7635
                 (fun uu____7660  ->
                    match uu____7660 with
                    | (t2,ctrl1) ->
                        maybe_continue ctrl1 t2
                          (fun t3  ->
                             let uu____7683 =
                               let uu____7684 =
                                 FStar_Syntax_Subst.compress t3  in
                               uu____7684.FStar_Syntax_Syntax.n  in
                             match uu____7683 with
                             | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
                                 let uu____7717 =
                                   ctrl_tac_fold f env ctrl1 hd1  in
                                 bind uu____7717
                                   (fun uu____7742  ->
                                      match uu____7742 with
                                      | (hd2,ctrl2) ->
                                          let ctrl3 = keep_going ctrl2  in
                                          let uu____7758 =
                                            ctrl_tac_fold_args f env ctrl3
                                              args
                                             in
                                          bind uu____7758
                                            (fun uu____7785  ->
                                               match uu____7785 with
                                               | (args1,ctrl4) ->
                                                   ret
                                                     ((let uu___390_7815 = t3
                                                          in
                                                       {
                                                         FStar_Syntax_Syntax.n
                                                           =
                                                           (FStar_Syntax_Syntax.Tm_app
                                                              (hd2, args1));
                                                         FStar_Syntax_Syntax.pos
                                                           =
                                                           (uu___390_7815.FStar_Syntax_Syntax.pos);
                                                         FStar_Syntax_Syntax.vars
                                                           =
                                                           (uu___390_7815.FStar_Syntax_Syntax.vars)
                                                       }), ctrl4)))
                             | FStar_Syntax_Syntax.Tm_abs (bs,t4,k) ->
                                 let uu____7851 =
                                   FStar_Syntax_Subst.open_term bs t4  in
                                 (match uu____7851 with
                                  | (bs1,t') ->
                                      let uu____7866 =
                                        let uu____7873 =
                                          FStar_TypeChecker_Env.push_binders
                                            env bs1
                                           in
                                        ctrl_tac_fold f uu____7873 ctrl1 t'
                                         in
                                      bind uu____7866
                                        (fun uu____7891  ->
                                           match uu____7891 with
                                           | (t'',ctrl2) ->
                                               let uu____7906 =
                                                 let uu____7913 =
                                                   let uu___391_7916 = t4  in
                                                   let uu____7919 =
                                                     let uu____7920 =
                                                       let uu____7937 =
                                                         FStar_Syntax_Subst.close_binders
                                                           bs1
                                                          in
                                                       let uu____7944 =
                                                         FStar_Syntax_Subst.close
                                                           bs1 t''
                                                          in
                                                       (uu____7937,
                                                         uu____7944, k)
                                                        in
                                                     FStar_Syntax_Syntax.Tm_abs
                                                       uu____7920
                                                      in
                                                   {
                                                     FStar_Syntax_Syntax.n =
                                                       uu____7919;
                                                     FStar_Syntax_Syntax.pos
                                                       =
                                                       (uu___391_7916.FStar_Syntax_Syntax.pos);
                                                     FStar_Syntax_Syntax.vars
                                                       =
                                                       (uu___391_7916.FStar_Syntax_Syntax.vars)
                                                   }  in
                                                 (uu____7913, ctrl2)  in
                                               ret uu____7906))
                             | FStar_Syntax_Syntax.Tm_arrow (bs,k) ->
                                 ret (t3, ctrl1)
                             | uu____7991 -> ret (t3, ctrl1))))

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
              let uu____8034 = ctrl_tac_fold f env ctrl t  in
              bind uu____8034
                (fun uu____8058  ->
                   match uu____8058 with
                   | (t1,ctrl1) ->
                       let uu____8073 = ctrl_tac_fold_args f env ctrl1 ts1
                          in
                       bind uu____8073
                         (fun uu____8100  ->
                            match uu____8100 with
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
              let uu____8182 =
                let uu____8189 =
                  add_irrelevant_goal "dummy" env FStar_Syntax_Util.t_true
                    opts
                   in
                bind uu____8189
                  (fun uu____8198  ->
                     let uu____8199 = ctrl t1  in
                     bind uu____8199
                       (fun res  ->
                          let uu____8222 = trivial ()  in
                          bind uu____8222 (fun uu____8230  -> ret res)))
                 in
              bind uu____8182
                (fun uu____8246  ->
                   match uu____8246 with
                   | (should_rewrite,ctrl1) ->
                       if Prims.op_Negation should_rewrite
                       then ret (t1, ctrl1)
                       else
                         (let uu____8270 =
                            FStar_TypeChecker_TcTerm.tc_term env t1  in
                          match uu____8270 with
                          | (t2,lcomp,g) ->
                              let uu____8286 =
                                (let uu____8289 =
                                   FStar_Syntax_Util.is_pure_or_ghost_lcomp
                                     lcomp
                                    in
                                 Prims.op_Negation uu____8289) ||
                                  (let uu____8291 =
                                     FStar_TypeChecker_Rel.is_trivial g  in
                                   Prims.op_Negation uu____8291)
                                 in
                              if uu____8286
                              then ret (t2, globalStop)
                              else
                                (let typ = lcomp.FStar_Syntax_Syntax.res_typ
                                    in
                                 let uu____8304 =
                                   new_uvar "pointwise_rec" env typ  in
                                 bind uu____8304
                                   (fun uu____8324  ->
                                      match uu____8324 with
                                      | (ut,uvar_ut) ->
                                          (log ps
                                             (fun uu____8341  ->
                                                let uu____8342 =
                                                  FStar_Syntax_Print.term_to_string
                                                    t2
                                                   in
                                                let uu____8343 =
                                                  FStar_Syntax_Print.term_to_string
                                                    ut
                                                   in
                                                FStar_Util.print2
                                                  "Pointwise_rec: making equality\n\t%s ==\n\t%s\n"
                                                  uu____8342 uu____8343);
                                           (let uu____8344 =
                                              let uu____8347 =
                                                let uu____8348 =
                                                  FStar_TypeChecker_TcTerm.universe_of
                                                    env typ
                                                   in
                                                FStar_Syntax_Util.mk_eq2
                                                  uu____8348 typ t2 ut
                                                 in
                                              add_irrelevant_goal
                                                "rewrite_rec equation" env
                                                uu____8347 opts
                                               in
                                            bind uu____8344
                                              (fun uu____8355  ->
                                                 let uu____8356 =
                                                   bind rewriter
                                                     (fun uu____8370  ->
                                                        let ut1 =
                                                          FStar_TypeChecker_Normalize.reduce_uvar_solutions
                                                            env ut
                                                           in
                                                        log ps
                                                          (fun uu____8376  ->
                                                             let uu____8377 =
                                                               FStar_Syntax_Print.term_to_string
                                                                 t2
                                                                in
                                                             let uu____8378 =
                                                               FStar_Syntax_Print.term_to_string
                                                                 ut1
                                                                in
                                                             FStar_Util.print2
                                                               "rewrite_rec: succeeded rewriting\n\t%s to\n\t%s\n"
                                                               uu____8377
                                                               uu____8378);
                                                        ret (ut1, ctrl1))
                                                    in
                                                 focus uu____8356)))))))
  
let (topdown_rewrite :
  (FStar_Syntax_Syntax.term ->
     (Prims.bool,FStar_BigInt.t) FStar_Pervasives_Native.tuple2 tac)
    -> unit tac -> unit tac)
  =
  fun ctrl  ->
    fun rewriter  ->
      let uu____8419 =
        bind get
          (fun ps  ->
             let uu____8429 =
               match ps.FStar_Tactics_Types.goals with
               | g::gs -> (g, gs)
               | [] -> failwith "no goals"  in
             match uu____8429 with
             | (g,gs) ->
                 let gt1 = FStar_Tactics_Types.goal_type g  in
                 (log ps
                    (fun uu____8466  ->
                       let uu____8467 = FStar_Syntax_Print.term_to_string gt1
                          in
                       FStar_Util.print1 "Topdown_rewrite starting with %s\n"
                         uu____8467);
                  bind dismiss_all
                    (fun uu____8470  ->
                       let uu____8471 =
                         let uu____8478 = FStar_Tactics_Types.goal_env g  in
                         ctrl_tac_fold
                           (rewrite_rec ps ctrl rewriter
                              g.FStar_Tactics_Types.opts) uu____8478
                           keepGoing gt1
                          in
                       bind uu____8471
                         (fun uu____8490  ->
                            match uu____8490 with
                            | (gt',uu____8498) ->
                                (log ps
                                   (fun uu____8502  ->
                                      let uu____8503 =
                                        FStar_Syntax_Print.term_to_string gt'
                                         in
                                      FStar_Util.print1
                                        "Topdown_rewrite seems to have succeded with %s\n"
                                        uu____8503);
                                 (let uu____8504 = push_goals gs  in
                                  bind uu____8504
                                    (fun uu____8509  ->
                                       let uu____8510 =
                                         let uu____8513 =
                                           FStar_Tactics_Types.goal_with_type
                                             g gt'
                                            in
                                         [uu____8513]  in
                                       add_goals uu____8510)))))))
         in
      FStar_All.pipe_left (wrap_err "topdown_rewrite") uu____8419
  
let (pointwise : FStar_Tactics_Types.direction -> unit tac -> unit tac) =
  fun d  ->
    fun tau  ->
      let uu____8536 =
        bind get
          (fun ps  ->
             let uu____8546 =
               match ps.FStar_Tactics_Types.goals with
               | g::gs -> (g, gs)
               | [] -> failwith "no goals"  in
             match uu____8546 with
             | (g,gs) ->
                 let gt1 = FStar_Tactics_Types.goal_type g  in
                 (log ps
                    (fun uu____8583  ->
                       let uu____8584 = FStar_Syntax_Print.term_to_string gt1
                          in
                       FStar_Util.print1 "Pointwise starting with %s\n"
                         uu____8584);
                  bind dismiss_all
                    (fun uu____8587  ->
                       let uu____8588 =
                         let uu____8591 = FStar_Tactics_Types.goal_env g  in
                         tac_fold_env d
                           (pointwise_rec ps tau g.FStar_Tactics_Types.opts)
                           uu____8591 gt1
                          in
                       bind uu____8588
                         (fun gt'  ->
                            log ps
                              (fun uu____8599  ->
                                 let uu____8600 =
                                   FStar_Syntax_Print.term_to_string gt'  in
                                 FStar_Util.print1
                                   "Pointwise seems to have succeded with %s\n"
                                   uu____8600);
                            (let uu____8601 = push_goals gs  in
                             bind uu____8601
                               (fun uu____8606  ->
                                  let uu____8607 =
                                    let uu____8610 =
                                      FStar_Tactics_Types.goal_with_type g
                                        gt'
                                       in
                                    [uu____8610]  in
                                  add_goals uu____8607))))))
         in
      FStar_All.pipe_left (wrap_err "pointwise") uu____8536
  
let (trefl : unit -> unit tac) =
  fun uu____8621  ->
    let uu____8624 =
      let uu____8627 = cur_goal ()  in
      bind uu____8627
        (fun g  ->
           let uu____8645 =
             let uu____8650 = FStar_Tactics_Types.goal_type g  in
             FStar_Syntax_Util.un_squash uu____8650  in
           match uu____8645 with
           | FStar_Pervasives_Native.Some t ->
               let uu____8658 = FStar_Syntax_Util.head_and_args' t  in
               (match uu____8658 with
                | (hd1,args) ->
                    let uu____8691 =
                      let uu____8702 =
                        let uu____8703 = FStar_Syntax_Util.un_uinst hd1  in
                        uu____8703.FStar_Syntax_Syntax.n  in
                      (uu____8702, args)  in
                    (match uu____8691 with
                     | (FStar_Syntax_Syntax.Tm_fvar
                        fv,uu____8715::(l,uu____8717)::(r,uu____8719)::[])
                         when
                         FStar_Syntax_Syntax.fv_eq_lid fv
                           FStar_Parser_Const.eq2_lid
                         ->
                         let uu____8746 =
                           let uu____8749 = FStar_Tactics_Types.goal_env g
                              in
                           do_unify uu____8749 l r  in
                         bind uu____8746
                           (fun b  ->
                              if Prims.op_Negation b
                              then
                                let uu____8756 =
                                  let uu____8757 =
                                    FStar_Tactics_Types.goal_env g  in
                                  tts uu____8757 l  in
                                let uu____8758 =
                                  let uu____8759 =
                                    FStar_Tactics_Types.goal_env g  in
                                  tts uu____8759 r  in
                                fail2 "not a trivial equality (%s vs %s)"
                                  uu____8756 uu____8758
                              else solve' g FStar_Syntax_Util.exp_unit)
                     | (hd2,uu____8762) ->
                         let uu____8775 =
                           let uu____8776 = FStar_Tactics_Types.goal_env g
                              in
                           tts uu____8776 t  in
                         fail1 "trefl: not an equality (%s)" uu____8775))
           | FStar_Pervasives_Native.None  -> fail "not an irrelevant goal")
       in
    FStar_All.pipe_left (wrap_err "trefl") uu____8624
  
let (dup : unit -> unit tac) =
  fun uu____8789  ->
    let uu____8792 = cur_goal ()  in
    bind uu____8792
      (fun g  ->
         let uu____8798 =
           let uu____8805 = FStar_Tactics_Types.goal_env g  in
           let uu____8806 = FStar_Tactics_Types.goal_type g  in
           new_uvar "dup" uu____8805 uu____8806  in
         bind uu____8798
           (fun uu____8815  ->
              match uu____8815 with
              | (u,u_uvar) ->
                  let g' =
                    let uu___393_8825 = g  in
                    {
                      FStar_Tactics_Types.goal_main_env =
                        (uu___393_8825.FStar_Tactics_Types.goal_main_env);
                      FStar_Tactics_Types.goal_ctx_uvar = u_uvar;
                      FStar_Tactics_Types.opts =
                        (uu___393_8825.FStar_Tactics_Types.opts);
                      FStar_Tactics_Types.is_guard =
                        (uu___393_8825.FStar_Tactics_Types.is_guard)
                    }  in
                  bind __dismiss
                    (fun uu____8828  ->
                       let uu____8829 =
                         let uu____8832 = FStar_Tactics_Types.goal_env g  in
                         let uu____8833 =
                           let uu____8834 =
                             let uu____8835 = FStar_Tactics_Types.goal_env g
                                in
                             let uu____8836 = FStar_Tactics_Types.goal_type g
                                in
                             FStar_TypeChecker_TcTerm.universe_of uu____8835
                               uu____8836
                              in
                           let uu____8837 = FStar_Tactics_Types.goal_type g
                              in
                           let uu____8838 =
                             FStar_Tactics_Types.goal_witness g  in
                           FStar_Syntax_Util.mk_eq2 uu____8834 uu____8837 u
                             uu____8838
                            in
                         add_irrelevant_goal "dup equation" uu____8832
                           uu____8833 g.FStar_Tactics_Types.opts
                          in
                       bind uu____8829
                         (fun uu____8841  ->
                            let uu____8842 = add_goals [g']  in
                            bind uu____8842 (fun uu____8846  -> ret ())))))
  
let (flip : unit -> unit tac) =
  fun uu____8853  ->
    bind get
      (fun ps  ->
         match ps.FStar_Tactics_Types.goals with
         | g1::g2::gs ->
             set
               (let uu___394_8870 = ps  in
                {
                  FStar_Tactics_Types.main_context =
                    (uu___394_8870.FStar_Tactics_Types.main_context);
                  FStar_Tactics_Types.main_goal =
                    (uu___394_8870.FStar_Tactics_Types.main_goal);
                  FStar_Tactics_Types.all_implicits =
                    (uu___394_8870.FStar_Tactics_Types.all_implicits);
                  FStar_Tactics_Types.goals = (g2 :: g1 :: gs);
                  FStar_Tactics_Types.smt_goals =
                    (uu___394_8870.FStar_Tactics_Types.smt_goals);
                  FStar_Tactics_Types.depth =
                    (uu___394_8870.FStar_Tactics_Types.depth);
                  FStar_Tactics_Types.__dump =
                    (uu___394_8870.FStar_Tactics_Types.__dump);
                  FStar_Tactics_Types.psc =
                    (uu___394_8870.FStar_Tactics_Types.psc);
                  FStar_Tactics_Types.entry_range =
                    (uu___394_8870.FStar_Tactics_Types.entry_range);
                  FStar_Tactics_Types.guard_policy =
                    (uu___394_8870.FStar_Tactics_Types.guard_policy);
                  FStar_Tactics_Types.freshness =
                    (uu___394_8870.FStar_Tactics_Types.freshness);
                  FStar_Tactics_Types.tac_verb_dbg =
                    (uu___394_8870.FStar_Tactics_Types.tac_verb_dbg)
                })
         | uu____8871 -> fail "flip: less than 2 goals")
  
let (later : unit -> unit tac) =
  fun uu____8880  ->
    bind get
      (fun ps  ->
         match ps.FStar_Tactics_Types.goals with
         | [] -> ret ()
         | g::gs ->
             set
               (let uu___395_8893 = ps  in
                {
                  FStar_Tactics_Types.main_context =
                    (uu___395_8893.FStar_Tactics_Types.main_context);
                  FStar_Tactics_Types.main_goal =
                    (uu___395_8893.FStar_Tactics_Types.main_goal);
                  FStar_Tactics_Types.all_implicits =
                    (uu___395_8893.FStar_Tactics_Types.all_implicits);
                  FStar_Tactics_Types.goals = (FStar_List.append gs [g]);
                  FStar_Tactics_Types.smt_goals =
                    (uu___395_8893.FStar_Tactics_Types.smt_goals);
                  FStar_Tactics_Types.depth =
                    (uu___395_8893.FStar_Tactics_Types.depth);
                  FStar_Tactics_Types.__dump =
                    (uu___395_8893.FStar_Tactics_Types.__dump);
                  FStar_Tactics_Types.psc =
                    (uu___395_8893.FStar_Tactics_Types.psc);
                  FStar_Tactics_Types.entry_range =
                    (uu___395_8893.FStar_Tactics_Types.entry_range);
                  FStar_Tactics_Types.guard_policy =
                    (uu___395_8893.FStar_Tactics_Types.guard_policy);
                  FStar_Tactics_Types.freshness =
                    (uu___395_8893.FStar_Tactics_Types.freshness);
                  FStar_Tactics_Types.tac_verb_dbg =
                    (uu___395_8893.FStar_Tactics_Types.tac_verb_dbg)
                }))
  
let (qed : unit -> unit tac) =
  fun uu____8900  ->
    bind get
      (fun ps  ->
         match ps.FStar_Tactics_Types.goals with
         | [] -> ret ()
         | uu____8907 -> fail "Not done!")
  
let (cases :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 tac)
  =
  fun t  ->
    let uu____8927 =
      let uu____8934 = cur_goal ()  in
      bind uu____8934
        (fun g  ->
           let uu____8944 =
             let uu____8953 = FStar_Tactics_Types.goal_env g  in
             __tc uu____8953 t  in
           bind uu____8944
             (fun uu____8981  ->
                match uu____8981 with
                | (t1,typ,guard) ->
                    let uu____8997 = FStar_Syntax_Util.head_and_args typ  in
                    (match uu____8997 with
                     | (hd1,args) ->
                         let uu____9040 =
                           let uu____9053 =
                             let uu____9054 = FStar_Syntax_Util.un_uinst hd1
                                in
                             uu____9054.FStar_Syntax_Syntax.n  in
                           (uu____9053, args)  in
                         (match uu____9040 with
                          | (FStar_Syntax_Syntax.Tm_fvar
                             fv,(p,uu____9073)::(q,uu____9075)::[]) when
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
                                let uu____9113 =
                                  let uu____9114 =
                                    FStar_Tactics_Types.goal_env g  in
                                  FStar_TypeChecker_Env.push_bv uu____9114
                                    v_p
                                   in
                                FStar_Tactics_Types.goal_with_env g
                                  uu____9113
                                 in
                              let g2 =
                                let uu____9116 =
                                  let uu____9117 =
                                    FStar_Tactics_Types.goal_env g  in
                                  FStar_TypeChecker_Env.push_bv uu____9117
                                    v_q
                                   in
                                FStar_Tactics_Types.goal_with_env g
                                  uu____9116
                                 in
                              bind __dismiss
                                (fun uu____9124  ->
                                   let uu____9125 = add_goals [g1; g2]  in
                                   bind uu____9125
                                     (fun uu____9134  ->
                                        let uu____9135 =
                                          let uu____9140 =
                                            FStar_Syntax_Syntax.bv_to_name
                                              v_p
                                             in
                                          let uu____9141 =
                                            FStar_Syntax_Syntax.bv_to_name
                                              v_q
                                             in
                                          (uu____9140, uu____9141)  in
                                        ret uu____9135))
                          | uu____9146 ->
                              let uu____9159 =
                                let uu____9160 =
                                  FStar_Tactics_Types.goal_env g  in
                                tts uu____9160 typ  in
                              fail1 "Not a disjunction: %s" uu____9159))))
       in
    FStar_All.pipe_left (wrap_err "cases") uu____8927
  
let (set_options : Prims.string -> unit tac) =
  fun s  ->
    let uu____9190 =
      let uu____9193 = cur_goal ()  in
      bind uu____9193
        (fun g  ->
           FStar_Options.push ();
           (let uu____9206 = FStar_Util.smap_copy g.FStar_Tactics_Types.opts
               in
            FStar_Options.set uu____9206);
           (let res = FStar_Options.set_options FStar_Options.Set s  in
            let opts' = FStar_Options.peek ()  in
            FStar_Options.pop ();
            (match res with
             | FStar_Getopt.Success  ->
                 let g' =
                   let uu___396_9213 = g  in
                   {
                     FStar_Tactics_Types.goal_main_env =
                       (uu___396_9213.FStar_Tactics_Types.goal_main_env);
                     FStar_Tactics_Types.goal_ctx_uvar =
                       (uu___396_9213.FStar_Tactics_Types.goal_ctx_uvar);
                     FStar_Tactics_Types.opts = opts';
                     FStar_Tactics_Types.is_guard =
                       (uu___396_9213.FStar_Tactics_Types.is_guard)
                   }  in
                 replace_cur g'
             | FStar_Getopt.Error err ->
                 fail2 "Setting options `%s` failed: %s" s err
             | FStar_Getopt.Help  ->
                 fail1 "Setting options `%s` failed (got `Help`?)" s)))
       in
    FStar_All.pipe_left (wrap_err "set_options") uu____9190
  
let (top_env : unit -> env tac) =
  fun uu____9225  ->
    bind get
      (fun ps  -> FStar_All.pipe_left ret ps.FStar_Tactics_Types.main_context)
  
let (cur_env : unit -> env tac) =
  fun uu____9238  ->
    let uu____9241 = cur_goal ()  in
    bind uu____9241
      (fun g  ->
         let uu____9247 = FStar_Tactics_Types.goal_env g  in
         FStar_All.pipe_left ret uu____9247)
  
let (cur_goal' : unit -> FStar_Syntax_Syntax.term tac) =
  fun uu____9256  ->
    let uu____9259 = cur_goal ()  in
    bind uu____9259
      (fun g  ->
         let uu____9265 = FStar_Tactics_Types.goal_type g  in
         FStar_All.pipe_left ret uu____9265)
  
let (cur_witness : unit -> FStar_Syntax_Syntax.term tac) =
  fun uu____9274  ->
    let uu____9277 = cur_goal ()  in
    bind uu____9277
      (fun g  ->
         let uu____9283 = FStar_Tactics_Types.goal_witness g  in
         FStar_All.pipe_left ret uu____9283)
  
let (unquote :
  FStar_Reflection_Data.typ ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term tac)
  =
  fun ty  ->
    fun tm  ->
      let uu____9300 =
        mlog
          (fun uu____9305  ->
             let uu____9306 = FStar_Syntax_Print.term_to_string tm  in
             FStar_Util.print1 "unquote: tm = %s\n" uu____9306)
          (fun uu____9309  ->
             let uu____9310 = cur_goal ()  in
             bind uu____9310
               (fun goal  ->
                  let env =
                    let uu____9318 = FStar_Tactics_Types.goal_env goal  in
                    FStar_TypeChecker_Env.set_expected_typ uu____9318 ty  in
                  let uu____9319 = __tc env tm  in
                  bind uu____9319
                    (fun uu____9338  ->
                       match uu____9338 with
                       | (tm1,typ,guard) ->
                           mlog
                             (fun uu____9352  ->
                                let uu____9353 =
                                  FStar_Syntax_Print.term_to_string tm1  in
                                FStar_Util.print1 "unquote: tm' = %s\n"
                                  uu____9353)
                             (fun uu____9355  ->
                                mlog
                                  (fun uu____9358  ->
                                     let uu____9359 =
                                       FStar_Syntax_Print.term_to_string typ
                                        in
                                     FStar_Util.print1 "unquote: typ = %s\n"
                                       uu____9359)
                                  (fun uu____9362  ->
                                     let uu____9363 =
                                       proc_guard "unquote" env guard
                                         goal.FStar_Tactics_Types.opts
                                        in
                                     bind uu____9363
                                       (fun uu____9367  -> ret tm1))))))
         in
      FStar_All.pipe_left (wrap_err "unquote") uu____9300
  
let (uvar_env :
  env ->
    FStar_Reflection_Data.typ FStar_Pervasives_Native.option ->
      FStar_Syntax_Syntax.term tac)
  =
  fun env  ->
    fun ty  ->
      let uu____9390 =
        match ty with
        | FStar_Pervasives_Native.Some ty1 -> ret ty1
        | FStar_Pervasives_Native.None  ->
            let uu____9396 =
              let uu____9403 =
                let uu____9404 = FStar_Syntax_Util.type_u ()  in
                FStar_All.pipe_left FStar_Pervasives_Native.fst uu____9404
                 in
              new_uvar "uvar_env.2" env uu____9403  in
            bind uu____9396
              (fun uu____9420  ->
                 match uu____9420 with | (typ,uvar_typ) -> ret typ)
         in
      bind uu____9390
        (fun typ  ->
           let uu____9432 = new_uvar "uvar_env" env typ  in
           bind uu____9432
             (fun uu____9446  -> match uu____9446 with | (t,uvar_t) -> ret t))
  
let (unshelve : FStar_Syntax_Syntax.term -> unit tac) =
  fun t  ->
    let uu____9464 =
      bind get
        (fun ps  ->
           let env = ps.FStar_Tactics_Types.main_context  in
           let opts =
             match ps.FStar_Tactics_Types.goals with
             | g::uu____9483 -> g.FStar_Tactics_Types.opts
             | uu____9486 -> FStar_Options.peek ()  in
           let uu____9489 = FStar_Syntax_Util.head_and_args t  in
           match uu____9489 with
           | ({
                FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                  (ctx_uvar,uu____9507);
                FStar_Syntax_Syntax.pos = uu____9508;
                FStar_Syntax_Syntax.vars = uu____9509;_},uu____9510)
               ->
               let env1 =
                 let uu___397_9552 = env  in
                 {
                   FStar_TypeChecker_Env.solver =
                     (uu___397_9552.FStar_TypeChecker_Env.solver);
                   FStar_TypeChecker_Env.range =
                     (uu___397_9552.FStar_TypeChecker_Env.range);
                   FStar_TypeChecker_Env.curmodule =
                     (uu___397_9552.FStar_TypeChecker_Env.curmodule);
                   FStar_TypeChecker_Env.gamma =
                     (ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_gamma);
                   FStar_TypeChecker_Env.gamma_sig =
                     (uu___397_9552.FStar_TypeChecker_Env.gamma_sig);
                   FStar_TypeChecker_Env.gamma_cache =
                     (uu___397_9552.FStar_TypeChecker_Env.gamma_cache);
                   FStar_TypeChecker_Env.modules =
                     (uu___397_9552.FStar_TypeChecker_Env.modules);
                   FStar_TypeChecker_Env.expected_typ =
                     (uu___397_9552.FStar_TypeChecker_Env.expected_typ);
                   FStar_TypeChecker_Env.sigtab =
                     (uu___397_9552.FStar_TypeChecker_Env.sigtab);
                   FStar_TypeChecker_Env.is_pattern =
                     (uu___397_9552.FStar_TypeChecker_Env.is_pattern);
                   FStar_TypeChecker_Env.instantiate_imp =
                     (uu___397_9552.FStar_TypeChecker_Env.instantiate_imp);
                   FStar_TypeChecker_Env.effects =
                     (uu___397_9552.FStar_TypeChecker_Env.effects);
                   FStar_TypeChecker_Env.generalize =
                     (uu___397_9552.FStar_TypeChecker_Env.generalize);
                   FStar_TypeChecker_Env.letrecs =
                     (uu___397_9552.FStar_TypeChecker_Env.letrecs);
                   FStar_TypeChecker_Env.top_level =
                     (uu___397_9552.FStar_TypeChecker_Env.top_level);
                   FStar_TypeChecker_Env.check_uvars =
                     (uu___397_9552.FStar_TypeChecker_Env.check_uvars);
                   FStar_TypeChecker_Env.use_eq =
                     (uu___397_9552.FStar_TypeChecker_Env.use_eq);
                   FStar_TypeChecker_Env.is_iface =
                     (uu___397_9552.FStar_TypeChecker_Env.is_iface);
                   FStar_TypeChecker_Env.admit =
                     (uu___397_9552.FStar_TypeChecker_Env.admit);
                   FStar_TypeChecker_Env.lax =
                     (uu___397_9552.FStar_TypeChecker_Env.lax);
                   FStar_TypeChecker_Env.lax_universes =
                     (uu___397_9552.FStar_TypeChecker_Env.lax_universes);
                   FStar_TypeChecker_Env.failhard =
                     (uu___397_9552.FStar_TypeChecker_Env.failhard);
                   FStar_TypeChecker_Env.nosynth =
                     (uu___397_9552.FStar_TypeChecker_Env.nosynth);
                   FStar_TypeChecker_Env.uvar_subtyping =
                     (uu___397_9552.FStar_TypeChecker_Env.uvar_subtyping);
                   FStar_TypeChecker_Env.tc_term =
                     (uu___397_9552.FStar_TypeChecker_Env.tc_term);
                   FStar_TypeChecker_Env.type_of =
                     (uu___397_9552.FStar_TypeChecker_Env.type_of);
                   FStar_TypeChecker_Env.universe_of =
                     (uu___397_9552.FStar_TypeChecker_Env.universe_of);
                   FStar_TypeChecker_Env.check_type_of =
                     (uu___397_9552.FStar_TypeChecker_Env.check_type_of);
                   FStar_TypeChecker_Env.use_bv_sorts =
                     (uu___397_9552.FStar_TypeChecker_Env.use_bv_sorts);
                   FStar_TypeChecker_Env.qtbl_name_and_index =
                     (uu___397_9552.FStar_TypeChecker_Env.qtbl_name_and_index);
                   FStar_TypeChecker_Env.normalized_eff_names =
                     (uu___397_9552.FStar_TypeChecker_Env.normalized_eff_names);
                   FStar_TypeChecker_Env.proof_ns =
                     (uu___397_9552.FStar_TypeChecker_Env.proof_ns);
                   FStar_TypeChecker_Env.synth_hook =
                     (uu___397_9552.FStar_TypeChecker_Env.synth_hook);
                   FStar_TypeChecker_Env.splice =
                     (uu___397_9552.FStar_TypeChecker_Env.splice);
                   FStar_TypeChecker_Env.is_native_tactic =
                     (uu___397_9552.FStar_TypeChecker_Env.is_native_tactic);
                   FStar_TypeChecker_Env.identifier_info =
                     (uu___397_9552.FStar_TypeChecker_Env.identifier_info);
                   FStar_TypeChecker_Env.tc_hooks =
                     (uu___397_9552.FStar_TypeChecker_Env.tc_hooks);
                   FStar_TypeChecker_Env.dsenv =
                     (uu___397_9552.FStar_TypeChecker_Env.dsenv);
                   FStar_TypeChecker_Env.dep_graph =
                     (uu___397_9552.FStar_TypeChecker_Env.dep_graph)
                 }  in
               let g = FStar_Tactics_Types.mk_goal env1 ctx_uvar opts false
                  in
               let uu____9554 =
                 let uu____9557 = bnorm_goal g  in [uu____9557]  in
               add_goals uu____9554
           | uu____9558 -> fail "not a uvar")
       in
    FStar_All.pipe_left (wrap_err "unshelve") uu____9464
  
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
          (fun uu____9619  ->
             let uu____9620 = FStar_Options.unsafe_tactic_exec ()  in
             if uu____9620
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
        (fun uu____9641  ->
           let uu____9642 =
             FStar_Syntax_Syntax.gen_bv nm FStar_Pervasives_Native.None t  in
           ret uu____9642)
  
let (change : FStar_Reflection_Data.typ -> unit tac) =
  fun ty  ->
    let uu____9652 =
      mlog
        (fun uu____9657  ->
           let uu____9658 = FStar_Syntax_Print.term_to_string ty  in
           FStar_Util.print1 "change: ty = %s\n" uu____9658)
        (fun uu____9661  ->
           let uu____9662 = cur_goal ()  in
           bind uu____9662
             (fun g  ->
                let uu____9668 =
                  let uu____9677 = FStar_Tactics_Types.goal_env g  in
                  __tc uu____9677 ty  in
                bind uu____9668
                  (fun uu____9689  ->
                     match uu____9689 with
                     | (ty1,uu____9699,guard) ->
                         let uu____9701 =
                           let uu____9704 = FStar_Tactics_Types.goal_env g
                              in
                           proc_guard "change" uu____9704 guard
                             g.FStar_Tactics_Types.opts
                            in
                         bind uu____9701
                           (fun uu____9707  ->
                              let uu____9708 =
                                let uu____9711 =
                                  FStar_Tactics_Types.goal_env g  in
                                let uu____9712 =
                                  FStar_Tactics_Types.goal_type g  in
                                do_unify uu____9711 uu____9712 ty1  in
                              bind uu____9708
                                (fun bb  ->
                                   if bb
                                   then
                                     let uu____9718 =
                                       FStar_Tactics_Types.goal_with_type g
                                         ty1
                                        in
                                     replace_cur uu____9718
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
                                        let uu____9724 =
                                          FStar_Tactics_Types.goal_env g  in
                                        let uu____9725 =
                                          FStar_Tactics_Types.goal_type g  in
                                        normalize steps uu____9724 uu____9725
                                         in
                                      let nty =
                                        let uu____9727 =
                                          FStar_Tactics_Types.goal_env g  in
                                        normalize steps uu____9727 ty1  in
                                      let uu____9728 =
                                        let uu____9731 =
                                          FStar_Tactics_Types.goal_env g  in
                                        do_unify uu____9731 ng nty  in
                                      bind uu____9728
                                        (fun b  ->
                                           if b
                                           then
                                             let uu____9737 =
                                               FStar_Tactics_Types.goal_with_type
                                                 g ty1
                                                in
                                             replace_cur uu____9737
                                           else fail "not convertible")))))))
       in
    FStar_All.pipe_left (wrap_err "change") uu____9652
  
let rec last : 'a . 'a Prims.list -> 'a =
  fun l  ->
    match l with
    | [] -> failwith "last: empty list"
    | x::[] -> x
    | uu____9759::xs -> last xs
  
let rec init : 'a . 'a Prims.list -> 'a Prims.list =
  fun l  ->
    match l with
    | [] -> failwith "init: empty list"
    | x::[] -> []
    | x::xs -> let uu____9787 = init xs  in x :: uu____9787
  
let rec (inspect :
  FStar_Syntax_Syntax.term -> FStar_Reflection_Data.term_view tac) =
  fun t  ->
    let uu____9799 =
      let t1 = FStar_Syntax_Util.unascribe t  in
      let t2 = FStar_Syntax_Util.un_uinst t1  in
      match t2.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_meta (t3,uu____9807) -> inspect t3
      | FStar_Syntax_Syntax.Tm_name bv ->
          FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_Var bv)
      | FStar_Syntax_Syntax.Tm_bvar bv ->
          FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_BVar bv)
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_FVar fv)
      | FStar_Syntax_Syntax.Tm_app (hd1,[]) ->
          failwith "empty arguments on Tm_app"
      | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
          let uu____9864 = last args  in
          (match uu____9864 with
           | (a,q) ->
               let q' = FStar_Reflection_Basic.inspect_aqual q  in
               let uu____9886 =
                 let uu____9887 =
                   let uu____9892 =
                     let uu____9893 =
                       let uu____9898 = init args  in
                       FStar_Syntax_Syntax.mk_Tm_app hd1 uu____9898  in
                     uu____9893 FStar_Pervasives_Native.None
                       t2.FStar_Syntax_Syntax.pos
                      in
                   (uu____9892, (a, q'))  in
                 FStar_Reflection_Data.Tv_App uu____9887  in
               FStar_All.pipe_left ret uu____9886)
      | FStar_Syntax_Syntax.Tm_abs ([],uu____9909,uu____9910) ->
          failwith "empty arguments on Tm_abs"
      | FStar_Syntax_Syntax.Tm_abs (bs,t3,k) ->
          let uu____9954 = FStar_Syntax_Subst.open_term bs t3  in
          (match uu____9954 with
           | (bs1,t4) ->
               (match bs1 with
                | [] -> failwith "impossible"
                | b::bs2 ->
                    let uu____9987 =
                      let uu____9988 =
                        let uu____9993 = FStar_Syntax_Util.abs bs2 t4 k  in
                        (b, uu____9993)  in
                      FStar_Reflection_Data.Tv_Abs uu____9988  in
                    FStar_All.pipe_left ret uu____9987))
      | FStar_Syntax_Syntax.Tm_type uu____9996 ->
          FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_Type ())
      | FStar_Syntax_Syntax.Tm_arrow ([],k) ->
          failwith "empty binders on arrow"
      | FStar_Syntax_Syntax.Tm_arrow uu____10016 ->
          let uu____10029 = FStar_Syntax_Util.arrow_one t2  in
          (match uu____10029 with
           | FStar_Pervasives_Native.Some (b,c) ->
               FStar_All.pipe_left ret
                 (FStar_Reflection_Data.Tv_Arrow (b, c))
           | FStar_Pervasives_Native.None  -> failwith "impossible")
      | FStar_Syntax_Syntax.Tm_refine (bv,t3) ->
          let b = FStar_Syntax_Syntax.mk_binder bv  in
          let uu____10059 = FStar_Syntax_Subst.open_term [b] t3  in
          (match uu____10059 with
           | (b',t4) ->
               let b1 =
                 match b' with
                 | b'1::[] -> b'1
                 | uu____10098 -> failwith "impossible"  in
               FStar_All.pipe_left ret
                 (FStar_Reflection_Data.Tv_Refine
                    ((FStar_Pervasives_Native.fst b1), t4)))
      | FStar_Syntax_Syntax.Tm_constant c ->
          let uu____10106 =
            let uu____10107 = FStar_Reflection_Basic.inspect_const c  in
            FStar_Reflection_Data.Tv_Const uu____10107  in
          FStar_All.pipe_left ret uu____10106
      | FStar_Syntax_Syntax.Tm_uvar (ctx_u,s) ->
          let uu____10132 =
            let uu____10133 =
              let uu____10138 =
                let uu____10139 =
                  FStar_Syntax_Unionfind.uvar_id
                    ctx_u.FStar_Syntax_Syntax.ctx_uvar_head
                   in
                FStar_BigInt.of_int_fs uu____10139  in
              (uu____10138, (ctx_u, s))  in
            FStar_Reflection_Data.Tv_Uvar uu____10133  in
          FStar_All.pipe_left ret uu____10132
      | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),t21) ->
          if lb.FStar_Syntax_Syntax.lbunivs <> []
          then FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown
          else
            (match lb.FStar_Syntax_Syntax.lbname with
             | FStar_Util.Inr uu____10175 ->
                 FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown
             | FStar_Util.Inl bv ->
                 let b = FStar_Syntax_Syntax.mk_binder bv  in
                 let uu____10180 = FStar_Syntax_Subst.open_term [b] t21  in
                 (match uu____10180 with
                  | (bs,t22) ->
                      let b1 =
                        match bs with
                        | b1::[] -> b1
                        | uu____10219 ->
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
             | FStar_Util.Inr uu____10249 ->
                 FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown
             | FStar_Util.Inl bv ->
                 let uu____10253 = FStar_Syntax_Subst.open_let_rec [lb] t21
                    in
                 (match uu____10253 with
                  | (lbs,t22) ->
                      (match lbs with
                       | lb1::[] ->
                           (match lb1.FStar_Syntax_Syntax.lbname with
                            | FStar_Util.Inr uu____10273 ->
                                ret FStar_Reflection_Data.Tv_Unknown
                            | FStar_Util.Inl bv1 ->
                                FStar_All.pipe_left ret
                                  (FStar_Reflection_Data.Tv_Let
                                     (true, bv1,
                                       (lb1.FStar_Syntax_Syntax.lbdef), t22)))
                       | uu____10277 ->
                           failwith
                             "impossible: open_term returned different amount of binders")))
      | FStar_Syntax_Syntax.Tm_match (t3,brs) ->
          let rec inspect_pat p =
            match p.FStar_Syntax_Syntax.v with
            | FStar_Syntax_Syntax.Pat_constant c ->
                let uu____10331 = FStar_Reflection_Basic.inspect_const c  in
                FStar_Reflection_Data.Pat_Constant uu____10331
            | FStar_Syntax_Syntax.Pat_cons (fv,ps) ->
                let uu____10350 =
                  let uu____10357 =
                    FStar_List.map
                      (fun uu____10369  ->
                         match uu____10369 with
                         | (p1,uu____10377) -> inspect_pat p1) ps
                     in
                  (fv, uu____10357)  in
                FStar_Reflection_Data.Pat_Cons uu____10350
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
              (fun uu___338_10471  ->
                 match uu___338_10471 with
                 | (pat,uu____10493,t4) ->
                     let uu____10511 = inspect_pat pat  in (uu____10511, t4))
              brs1
             in
          FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_Match (t3, brs2))
      | FStar_Syntax_Syntax.Tm_unknown  ->
          FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown
      | uu____10520 ->
          ((let uu____10522 =
              let uu____10527 =
                let uu____10528 = FStar_Syntax_Print.tag_of_term t2  in
                let uu____10529 = FStar_Syntax_Print.term_to_string t2  in
                FStar_Util.format2
                  "inspect: outside of expected syntax (%s, %s)\n"
                  uu____10528 uu____10529
                 in
              (FStar_Errors.Warning_CantInspect, uu____10527)  in
            FStar_Errors.log_issue t2.FStar_Syntax_Syntax.pos uu____10522);
           FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown)
       in
    wrap_err "inspect" uu____9799
  
let (pack : FStar_Reflection_Data.term_view -> FStar_Syntax_Syntax.term tac)
  =
  fun tv  ->
    match tv with
    | FStar_Reflection_Data.Tv_Var bv ->
        let uu____10542 = FStar_Syntax_Syntax.bv_to_name bv  in
        FStar_All.pipe_left ret uu____10542
    | FStar_Reflection_Data.Tv_BVar bv ->
        let uu____10546 = FStar_Syntax_Syntax.bv_to_tm bv  in
        FStar_All.pipe_left ret uu____10546
    | FStar_Reflection_Data.Tv_FVar fv ->
        let uu____10550 = FStar_Syntax_Syntax.fv_to_tm fv  in
        FStar_All.pipe_left ret uu____10550
    | FStar_Reflection_Data.Tv_App (l,(r,q)) ->
        let q' = FStar_Reflection_Basic.pack_aqual q  in
        let uu____10557 = FStar_Syntax_Util.mk_app l [(r, q')]  in
        FStar_All.pipe_left ret uu____10557
    | FStar_Reflection_Data.Tv_Abs (b,t) ->
        let uu____10576 =
          FStar_Syntax_Util.abs [b] t FStar_Pervasives_Native.None  in
        FStar_All.pipe_left ret uu____10576
    | FStar_Reflection_Data.Tv_Arrow (b,c) ->
        let uu____10589 = FStar_Syntax_Util.arrow [b] c  in
        FStar_All.pipe_left ret uu____10589
    | FStar_Reflection_Data.Tv_Type () ->
        FStar_All.pipe_left ret FStar_Syntax_Util.ktype
    | FStar_Reflection_Data.Tv_Refine (bv,t) ->
        let uu____10604 = FStar_Syntax_Util.refine bv t  in
        FStar_All.pipe_left ret uu____10604
    | FStar_Reflection_Data.Tv_Const c ->
        let uu____10608 =
          let uu____10609 =
            let uu____10616 =
              let uu____10617 = FStar_Reflection_Basic.pack_const c  in
              FStar_Syntax_Syntax.Tm_constant uu____10617  in
            FStar_Syntax_Syntax.mk uu____10616  in
          uu____10609 FStar_Pervasives_Native.None FStar_Range.dummyRange  in
        FStar_All.pipe_left ret uu____10608
    | FStar_Reflection_Data.Tv_Uvar (_u,ctx_u_s) ->
        let uu____10625 =
          FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_uvar ctx_u_s)
            FStar_Pervasives_Native.None FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____10625
    | FStar_Reflection_Data.Tv_Let (false ,bv,t1,t2) ->
        let lb =
          FStar_Syntax_Util.mk_letbinding (FStar_Util.Inl bv) []
            bv.FStar_Syntax_Syntax.sort FStar_Parser_Const.effect_Tot_lid t1
            [] FStar_Range.dummyRange
           in
        let uu____10634 =
          let uu____10635 =
            let uu____10642 =
              let uu____10643 =
                let uu____10656 =
                  let uu____10659 =
                    let uu____10660 = FStar_Syntax_Syntax.mk_binder bv  in
                    [uu____10660]  in
                  FStar_Syntax_Subst.close uu____10659 t2  in
                ((false, [lb]), uu____10656)  in
              FStar_Syntax_Syntax.Tm_let uu____10643  in
            FStar_Syntax_Syntax.mk uu____10642  in
          uu____10635 FStar_Pervasives_Native.None FStar_Range.dummyRange  in
        FStar_All.pipe_left ret uu____10634
    | FStar_Reflection_Data.Tv_Let (true ,bv,t1,t2) ->
        let lb =
          FStar_Syntax_Util.mk_letbinding (FStar_Util.Inl bv) []
            bv.FStar_Syntax_Syntax.sort FStar_Parser_Const.effect_Tot_lid t1
            [] FStar_Range.dummyRange
           in
        let uu____10694 = FStar_Syntax_Subst.close_let_rec [lb] t2  in
        (match uu____10694 with
         | (lbs,body) ->
             let uu____10709 =
               FStar_Syntax_Syntax.mk
                 (FStar_Syntax_Syntax.Tm_let ((true, lbs), body))
                 FStar_Pervasives_Native.None FStar_Range.dummyRange
                in
             FStar_All.pipe_left ret uu____10709)
    | FStar_Reflection_Data.Tv_Match (t,brs) ->
        let wrap v1 =
          {
            FStar_Syntax_Syntax.v = v1;
            FStar_Syntax_Syntax.p = FStar_Range.dummyRange
          }  in
        let rec pack_pat p =
          match p with
          | FStar_Reflection_Data.Pat_Constant c ->
              let uu____10743 =
                let uu____10744 = FStar_Reflection_Basic.pack_const c  in
                FStar_Syntax_Syntax.Pat_constant uu____10744  in
              FStar_All.pipe_left wrap uu____10743
          | FStar_Reflection_Data.Pat_Cons (fv,ps) ->
              let uu____10751 =
                let uu____10752 =
                  let uu____10765 =
                    FStar_List.map
                      (fun p1  ->
                         let uu____10781 = pack_pat p1  in
                         (uu____10781, false)) ps
                     in
                  (fv, uu____10765)  in
                FStar_Syntax_Syntax.Pat_cons uu____10752  in
              FStar_All.pipe_left wrap uu____10751
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
            (fun uu___339_10827  ->
               match uu___339_10827 with
               | (pat,t1) ->
                   let uu____10844 = pack_pat pat  in
                   (uu____10844, FStar_Pervasives_Native.None, t1)) brs
           in
        let brs2 = FStar_List.map FStar_Syntax_Subst.close_branch brs1  in
        let uu____10892 =
          FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_match (t, brs2))
            FStar_Pervasives_Native.None FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____10892
    | FStar_Reflection_Data.Tv_AscribedT (e,t,tacopt) ->
        let uu____10920 =
          FStar_Syntax_Syntax.mk
            (FStar_Syntax_Syntax.Tm_ascribed
               (e, ((FStar_Util.Inl t), tacopt),
                 FStar_Pervasives_Native.None)) FStar_Pervasives_Native.None
            FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____10920
    | FStar_Reflection_Data.Tv_AscribedC (e,c,tacopt) ->
        let uu____10966 =
          FStar_Syntax_Syntax.mk
            (FStar_Syntax_Syntax.Tm_ascribed
               (e, ((FStar_Util.Inr c), tacopt),
                 FStar_Pervasives_Native.None)) FStar_Pervasives_Native.None
            FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____10966
    | FStar_Reflection_Data.Tv_Unknown  ->
        let uu____11005 =
          FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown
            FStar_Pervasives_Native.None FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____11005
  
let (goal_of_goal_ty :
  env ->
    FStar_Reflection_Data.typ ->
      (FStar_Tactics_Types.goal,FStar_TypeChecker_Env.guard_t)
        FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun typ  ->
      let uu____11026 =
        FStar_TypeChecker_Util.new_implicit_var "proofstate_of_goal_ty"
          typ.FStar_Syntax_Syntax.pos env typ
         in
      match uu____11026 with
      | (u,ctx_uvars,g_u) ->
          let uu____11058 = FStar_List.hd ctx_uvars  in
          (match uu____11058 with
           | (ctx_uvar,uu____11072) ->
               let g =
                 let uu____11074 = FStar_Options.peek ()  in
                 FStar_Tactics_Types.mk_goal env ctx_uvar uu____11074 false
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
        let uu____11094 = goal_of_goal_ty env typ  in
        match uu____11094 with
        | (g,g_u) ->
            let ps =
              let uu____11106 =
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
                FStar_Tactics_Types.tac_verb_dbg = uu____11106
              }  in
            let uu____11111 = FStar_Tactics_Types.goal_witness g  in
            (ps, uu____11111)
  