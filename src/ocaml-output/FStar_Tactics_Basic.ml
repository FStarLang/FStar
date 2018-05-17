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
                                                                   let uu____4069
                                                                    =
                                                                    uopt &&
                                                                    (uvar_free
                                                                    goal_u.FStar_Syntax_Syntax.ctx_uvar_head
                                                                    ps)  in
                                                                   if
                                                                    uu____4069
                                                                   then
                                                                    ret ()
                                                                   else
                                                                    (let uu____4073
                                                                    =
                                                                    let uu____4076
                                                                    =
                                                                    bnorm_goal
                                                                    (let uu___371_4079
                                                                    = goal
                                                                     in
                                                                    {
                                                                    FStar_Tactics_Types.goal_main_env
                                                                    =
                                                                    (uu___371_4079.FStar_Tactics_Types.goal_main_env);
                                                                    FStar_Tactics_Types.goal_ctx_uvar
                                                                    = goal_u;
                                                                    FStar_Tactics_Types.opts
                                                                    =
                                                                    (uu___371_4079.FStar_Tactics_Types.opts);
                                                                    FStar_Tactics_Types.is_guard
                                                                    = false
                                                                    })  in
                                                                    [uu____4076]
                                                                     in
                                                                    add_goals
                                                                    uu____4073))
                                                          | t -> ret ()))))))))
  
let try_unif : 'a . 'a tac -> 'a tac -> 'a tac =
  fun t  ->
    fun t'  -> mk_tac (fun ps  -> try run t ps with | NoUnif  -> run t' ps)
  
let (apply : Prims.bool -> FStar_Syntax_Syntax.term -> unit tac) =
  fun uopt  ->
    fun tm  ->
      let uu____4134 =
        mlog
          (fun uu____4139  ->
             let uu____4140 = FStar_Syntax_Print.term_to_string tm  in
             FStar_Util.print1 "apply: tm = %s\n" uu____4140)
          (fun uu____4143  ->
             let uu____4144 = cur_goal ()  in
             bind uu____4144
               (fun goal  ->
                  let uu____4150 =
                    let uu____4159 = FStar_Tactics_Types.goal_env goal  in
                    __tc uu____4159 tm  in
                  bind uu____4150
                    (fun uu____4173  ->
                       match uu____4173 with
                       | (tm1,typ,guard) ->
                           let typ1 =
                             let uu____4186 =
                               FStar_Tactics_Types.goal_env goal  in
                             bnorm uu____4186 typ  in
                           let uu____4187 =
                             let uu____4190 =
                               let uu____4193 = __apply uopt tm1 typ1  in
                               bind uu____4193
                                 (fun uu____4198  ->
                                    let uu____4199 =
                                      FStar_Tactics_Types.goal_env goal  in
                                    proc_guard "apply guard" uu____4199 guard
                                      goal.FStar_Tactics_Types.opts)
                                in
                             focus uu____4190  in
                           let uu____4200 =
                             let uu____4203 =
                               let uu____4204 =
                                 FStar_Tactics_Types.goal_env goal  in
                               tts uu____4204 tm1  in
                             let uu____4205 =
                               let uu____4206 =
                                 FStar_Tactics_Types.goal_env goal  in
                               tts uu____4206 typ1  in
                             let uu____4207 =
                               let uu____4208 =
                                 FStar_Tactics_Types.goal_env goal  in
                               let uu____4209 =
                                 FStar_Tactics_Types.goal_type goal  in
                               tts uu____4208 uu____4209  in
                             fail3
                               "Cannot instantiate %s (of type %s) to match goal (%s)"
                               uu____4203 uu____4205 uu____4207
                              in
                           try_unif uu____4187 uu____4200)))
         in
      FStar_All.pipe_left (wrap_err "apply") uu____4134
  
let (lemma_or_sq :
  FStar_Syntax_Syntax.comp ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun c  ->
    let ct = FStar_Syntax_Util.comp_to_comp_typ_nouniv c  in
    let uu____4232 =
      FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
        FStar_Parser_Const.effect_Lemma_lid
       in
    if uu____4232
    then
      let uu____4239 =
        match ct.FStar_Syntax_Syntax.effect_args with
        | pre::post::uu____4254 ->
            ((FStar_Pervasives_Native.fst pre),
              (FStar_Pervasives_Native.fst post))
        | uu____4293 -> failwith "apply_lemma: impossible: not a lemma"  in
      match uu____4239 with
      | (pre,post) ->
          let post1 =
            let uu____4323 =
              let uu____4332 =
                FStar_Syntax_Syntax.as_arg FStar_Syntax_Util.exp_unit  in
              [uu____4332]  in
            FStar_Syntax_Util.mk_app post uu____4323  in
          FStar_Pervasives_Native.Some (pre, post1)
    else
      (let uu____4356 =
         FStar_Syntax_Util.is_pure_effect ct.FStar_Syntax_Syntax.effect_name
          in
       if uu____4356
       then
         let uu____4363 =
           FStar_Syntax_Util.un_squash ct.FStar_Syntax_Syntax.result_typ  in
         FStar_Util.map_opt uu____4363
           (fun post  -> (FStar_Syntax_Util.t_true, post))
       else FStar_Pervasives_Native.None)
  
let (apply_lemma : FStar_Syntax_Syntax.term -> unit tac) =
  fun tm  ->
    let uu____4396 =
      let uu____4399 =
        mlog
          (fun uu____4404  ->
             let uu____4405 = FStar_Syntax_Print.term_to_string tm  in
             FStar_Util.print1 "apply_lemma: tm = %s\n" uu____4405)
          (fun uu____4409  ->
             let is_unit_t t =
               let uu____4416 =
                 let uu____4417 = FStar_Syntax_Subst.compress t  in
                 uu____4417.FStar_Syntax_Syntax.n  in
               match uu____4416 with
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.unit_lid
                   -> true
               | uu____4421 -> false  in
             let uu____4422 = cur_goal ()  in
             bind uu____4422
               (fun goal  ->
                  let uu____4428 =
                    let uu____4437 = FStar_Tactics_Types.goal_env goal  in
                    __tc uu____4437 tm  in
                  bind uu____4428
                    (fun uu____4452  ->
                       match uu____4452 with
                       | (tm1,t,guard) ->
                           let uu____4464 =
                             FStar_Syntax_Util.arrow_formals_comp t  in
                           (match uu____4464 with
                            | (bs,comp) ->
                                let uu____4491 = lemma_or_sq comp  in
                                (match uu____4491 with
                                 | FStar_Pervasives_Native.None  ->
                                     fail "not a lemma or squashed function"
                                 | FStar_Pervasives_Native.Some (pre,post) ->
                                     let uu____4510 =
                                       FStar_List.fold_left
                                         (fun uu____4552  ->
                                            fun uu____4553  ->
                                              match (uu____4552, uu____4553)
                                              with
                                              | ((uvs,guard1,subst1),(b,aq))
                                                  ->
                                                  let b_t =
                                                    FStar_Syntax_Subst.subst
                                                      subst1
                                                      b.FStar_Syntax_Syntax.sort
                                                     in
                                                  let uu____4644 =
                                                    is_unit_t b_t  in
                                                  if uu____4644
                                                  then
                                                    (((FStar_Syntax_Util.exp_unit,
                                                        aq) :: uvs), guard1,
                                                      ((FStar_Syntax_Syntax.NT
                                                          (b,
                                                            FStar_Syntax_Util.exp_unit))
                                                      :: subst1))
                                                  else
                                                    (let uu____4674 =
                                                       let uu____4687 =
                                                         let uu____4688 =
                                                           FStar_Tactics_Types.goal_type
                                                             goal
                                                            in
                                                         uu____4688.FStar_Syntax_Syntax.pos
                                                          in
                                                       let uu____4691 =
                                                         FStar_Tactics_Types.goal_env
                                                           goal
                                                          in
                                                       FStar_TypeChecker_Util.new_implicit_var
                                                         "apply_lemma"
                                                         uu____4687
                                                         uu____4691 b_t
                                                        in
                                                     match uu____4674 with
                                                     | (u,uu____4707,g_u) ->
                                                         let uu____4721 =
                                                           FStar_TypeChecker_Rel.conj_guard
                                                             guard1 g_u
                                                            in
                                                         (((u, aq) :: uvs),
                                                           uu____4721,
                                                           ((FStar_Syntax_Syntax.NT
                                                               (b, u)) ::
                                                           subst1))))
                                         ([], guard, []) bs
                                        in
                                     (match uu____4510 with
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
                                          let uu____4782 =
                                            let uu____4785 =
                                              FStar_Tactics_Types.goal_env
                                                goal
                                               in
                                            let uu____4786 =
                                              FStar_Syntax_Util.mk_squash
                                                FStar_Syntax_Syntax.U_zero
                                                post1
                                               in
                                            let uu____4787 =
                                              FStar_Tactics_Types.goal_type
                                                goal
                                               in
                                            do_unify uu____4785 uu____4786
                                              uu____4787
                                             in
                                          bind uu____4782
                                            (fun b  ->
                                               if Prims.op_Negation b
                                               then
                                                 let uu____4795 =
                                                   let uu____4796 =
                                                     FStar_Tactics_Types.goal_env
                                                       goal
                                                      in
                                                   tts uu____4796 tm1  in
                                                 let uu____4797 =
                                                   let uu____4798 =
                                                     FStar_Tactics_Types.goal_env
                                                       goal
                                                      in
                                                   let uu____4799 =
                                                     FStar_Syntax_Util.mk_squash
                                                       FStar_Syntax_Syntax.U_zero
                                                       post1
                                                      in
                                                   tts uu____4798 uu____4799
                                                    in
                                                 let uu____4800 =
                                                   let uu____4801 =
                                                     FStar_Tactics_Types.goal_env
                                                       goal
                                                      in
                                                   let uu____4802 =
                                                     FStar_Tactics_Types.goal_type
                                                       goal
                                                      in
                                                   tts uu____4801 uu____4802
                                                    in
                                                 fail3
                                                   "Cannot instantiate lemma %s (with postcondition: %s) to match goal (%s)"
                                                   uu____4795 uu____4797
                                                   uu____4800
                                               else
                                                 (let uu____4804 =
                                                    add_implicits
                                                      implicits.FStar_TypeChecker_Env.implicits
                                                     in
                                                  bind uu____4804
                                                    (fun uu____4809  ->
                                                       let uu____4810 =
                                                         solve' goal
                                                           FStar_Syntax_Util.exp_unit
                                                          in
                                                       bind uu____4810
                                                         (fun uu____4818  ->
                                                            let is_free_uvar
                                                              uv t1 =
                                                              let free_uvars
                                                                =
                                                                let uu____4843
                                                                  =
                                                                  let uu____4846
                                                                    =
                                                                    FStar_Syntax_Free.uvars
                                                                    t1  in
                                                                  FStar_Util.set_elements
                                                                    uu____4846
                                                                   in
                                                                FStar_List.map
                                                                  (fun x  ->
                                                                    x.FStar_Syntax_Syntax.ctx_uvar_head)
                                                                  uu____4843
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
                                                                   let uu____4881
                                                                    =
                                                                    FStar_Tactics_Types.goal_type
                                                                    g'  in
                                                                   is_free_uvar
                                                                    uv
                                                                    uu____4881)
                                                                goals
                                                               in
                                                            let checkone t1
                                                              goals =
                                                              let uu____4897
                                                                =
                                                                FStar_Syntax_Util.head_and_args
                                                                  t1
                                                                 in
                                                              match uu____4897
                                                              with
                                                              | (hd1,uu____4913)
                                                                  ->
                                                                  (match 
                                                                    hd1.FStar_Syntax_Syntax.n
                                                                   with
                                                                   | 
                                                                   FStar_Syntax_Syntax.Tm_uvar
                                                                    (uv,uu____4935)
                                                                    ->
                                                                    appears
                                                                    uv.FStar_Syntax_Syntax.ctx_uvar_head
                                                                    goals
                                                                   | 
                                                                   uu____4952
                                                                    -> false)
                                                               in
                                                            let uu____4953 =
                                                              FStar_All.pipe_right
                                                                implicits.FStar_TypeChecker_Env.implicits
                                                                (mapM
                                                                   (fun
                                                                    uu____5016
                                                                     ->
                                                                    match uu____5016
                                                                    with
                                                                    | 
                                                                    (_msg,term,ctx_uvar,_range)
                                                                    ->
                                                                    let uu____5039
                                                                    =
                                                                    FStar_Syntax_Util.head_and_args
                                                                    term  in
                                                                    (match uu____5039
                                                                    with
                                                                    | 
                                                                    (hd1,uu____5065)
                                                                    ->
                                                                    let uu____5086
                                                                    =
                                                                    let uu____5087
                                                                    =
                                                                    FStar_Syntax_Subst.compress
                                                                    hd1  in
                                                                    uu____5087.FStar_Syntax_Syntax.n
                                                                     in
                                                                    (match uu____5086
                                                                    with
                                                                    | 
                                                                    FStar_Syntax_Syntax.Tm_uvar
                                                                    (ctx_uvar1,uu____5101)
                                                                    ->
                                                                    let goal1
                                                                    =
                                                                    bnorm_goal
                                                                    (let uu___374_5121
                                                                    = goal
                                                                     in
                                                                    {
                                                                    FStar_Tactics_Types.goal_main_env
                                                                    =
                                                                    (uu___374_5121.FStar_Tactics_Types.goal_main_env);
                                                                    FStar_Tactics_Types.goal_ctx_uvar
                                                                    =
                                                                    ctx_uvar1;
                                                                    FStar_Tactics_Types.opts
                                                                    =
                                                                    (uu___374_5121.FStar_Tactics_Types.opts);
                                                                    FStar_Tactics_Types.is_guard
                                                                    =
                                                                    (uu___374_5121.FStar_Tactics_Types.is_guard)
                                                                    })  in
                                                                    ret
                                                                    ([goal1],
                                                                    [])
                                                                    | 
                                                                    uu____5134
                                                                    ->
                                                                    let env =
                                                                    let uu___375_5136
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    goal  in
                                                                    {
                                                                    FStar_TypeChecker_Env.solver
                                                                    =
                                                                    (uu___375_5136.FStar_TypeChecker_Env.solver);
                                                                    FStar_TypeChecker_Env.range
                                                                    =
                                                                    (uu___375_5136.FStar_TypeChecker_Env.range);
                                                                    FStar_TypeChecker_Env.curmodule
                                                                    =
                                                                    (uu___375_5136.FStar_TypeChecker_Env.curmodule);
                                                                    FStar_TypeChecker_Env.gamma
                                                                    =
                                                                    (ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_gamma);
                                                                    FStar_TypeChecker_Env.gamma_sig
                                                                    =
                                                                    (uu___375_5136.FStar_TypeChecker_Env.gamma_sig);
                                                                    FStar_TypeChecker_Env.gamma_cache
                                                                    =
                                                                    (uu___375_5136.FStar_TypeChecker_Env.gamma_cache);
                                                                    FStar_TypeChecker_Env.modules
                                                                    =
                                                                    (uu___375_5136.FStar_TypeChecker_Env.modules);
                                                                    FStar_TypeChecker_Env.expected_typ
                                                                    =
                                                                    (uu___375_5136.FStar_TypeChecker_Env.expected_typ);
                                                                    FStar_TypeChecker_Env.sigtab
                                                                    =
                                                                    (uu___375_5136.FStar_TypeChecker_Env.sigtab);
                                                                    FStar_TypeChecker_Env.is_pattern
                                                                    =
                                                                    (uu___375_5136.FStar_TypeChecker_Env.is_pattern);
                                                                    FStar_TypeChecker_Env.instantiate_imp
                                                                    =
                                                                    (uu___375_5136.FStar_TypeChecker_Env.instantiate_imp);
                                                                    FStar_TypeChecker_Env.effects
                                                                    =
                                                                    (uu___375_5136.FStar_TypeChecker_Env.effects);
                                                                    FStar_TypeChecker_Env.generalize
                                                                    =
                                                                    (uu___375_5136.FStar_TypeChecker_Env.generalize);
                                                                    FStar_TypeChecker_Env.letrecs
                                                                    =
                                                                    (uu___375_5136.FStar_TypeChecker_Env.letrecs);
                                                                    FStar_TypeChecker_Env.top_level
                                                                    =
                                                                    (uu___375_5136.FStar_TypeChecker_Env.top_level);
                                                                    FStar_TypeChecker_Env.check_uvars
                                                                    =
                                                                    (uu___375_5136.FStar_TypeChecker_Env.check_uvars);
                                                                    FStar_TypeChecker_Env.use_eq
                                                                    =
                                                                    (uu___375_5136.FStar_TypeChecker_Env.use_eq);
                                                                    FStar_TypeChecker_Env.is_iface
                                                                    =
                                                                    (uu___375_5136.FStar_TypeChecker_Env.is_iface);
                                                                    FStar_TypeChecker_Env.admit
                                                                    =
                                                                    (uu___375_5136.FStar_TypeChecker_Env.admit);
                                                                    FStar_TypeChecker_Env.lax
                                                                    =
                                                                    (uu___375_5136.FStar_TypeChecker_Env.lax);
                                                                    FStar_TypeChecker_Env.lax_universes
                                                                    =
                                                                    (uu___375_5136.FStar_TypeChecker_Env.lax_universes);
                                                                    FStar_TypeChecker_Env.failhard
                                                                    =
                                                                    (uu___375_5136.FStar_TypeChecker_Env.failhard);
                                                                    FStar_TypeChecker_Env.nosynth
                                                                    =
                                                                    (uu___375_5136.FStar_TypeChecker_Env.nosynth);
                                                                    FStar_TypeChecker_Env.uvar_subtyping
                                                                    =
                                                                    (uu___375_5136.FStar_TypeChecker_Env.uvar_subtyping);
                                                                    FStar_TypeChecker_Env.tc_term
                                                                    =
                                                                    (uu___375_5136.FStar_TypeChecker_Env.tc_term);
                                                                    FStar_TypeChecker_Env.type_of
                                                                    =
                                                                    (uu___375_5136.FStar_TypeChecker_Env.type_of);
                                                                    FStar_TypeChecker_Env.universe_of
                                                                    =
                                                                    (uu___375_5136.FStar_TypeChecker_Env.universe_of);
                                                                    FStar_TypeChecker_Env.check_type_of
                                                                    =
                                                                    (uu___375_5136.FStar_TypeChecker_Env.check_type_of);
                                                                    FStar_TypeChecker_Env.use_bv_sorts
                                                                    =
                                                                    (uu___375_5136.FStar_TypeChecker_Env.use_bv_sorts);
                                                                    FStar_TypeChecker_Env.qtbl_name_and_index
                                                                    =
                                                                    (uu___375_5136.FStar_TypeChecker_Env.qtbl_name_and_index);
                                                                    FStar_TypeChecker_Env.normalized_eff_names
                                                                    =
                                                                    (uu___375_5136.FStar_TypeChecker_Env.normalized_eff_names);
                                                                    FStar_TypeChecker_Env.proof_ns
                                                                    =
                                                                    (uu___375_5136.FStar_TypeChecker_Env.proof_ns);
                                                                    FStar_TypeChecker_Env.synth_hook
                                                                    =
                                                                    (uu___375_5136.FStar_TypeChecker_Env.synth_hook);
                                                                    FStar_TypeChecker_Env.splice
                                                                    =
                                                                    (uu___375_5136.FStar_TypeChecker_Env.splice);
                                                                    FStar_TypeChecker_Env.is_native_tactic
                                                                    =
                                                                    (uu___375_5136.FStar_TypeChecker_Env.is_native_tactic);
                                                                    FStar_TypeChecker_Env.identifier_info
                                                                    =
                                                                    (uu___375_5136.FStar_TypeChecker_Env.identifier_info);
                                                                    FStar_TypeChecker_Env.tc_hooks
                                                                    =
                                                                    (uu___375_5136.FStar_TypeChecker_Env.tc_hooks);
                                                                    FStar_TypeChecker_Env.dsenv
                                                                    =
                                                                    (uu___375_5136.FStar_TypeChecker_Env.dsenv);
                                                                    FStar_TypeChecker_Env.dep_graph
                                                                    =
                                                                    (uu___375_5136.FStar_TypeChecker_Env.dep_graph)
                                                                    }  in
                                                                    let g_typ
                                                                    =
                                                                    let uu____5138
                                                                    =
                                                                    FStar_Options.__temp_fast_implicits
                                                                    ()  in
                                                                    if
                                                                    uu____5138
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
                                                                    let uu____5141
                                                                    =
                                                                    let uu____5148
                                                                    =
                                                                    FStar_TypeChecker_Env.set_expected_typ
                                                                    env
                                                                    ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_typ
                                                                     in
                                                                    env.FStar_TypeChecker_Env.type_of
                                                                    uu____5148
                                                                    term1  in
                                                                    match uu____5141
                                                                    with
                                                                    | 
                                                                    (uu____5149,uu____5150,g_typ)
                                                                    -> g_typ)
                                                                     in
                                                                    let uu____5152
                                                                    =
                                                                    let uu____5157
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    goal  in
                                                                    goal_from_guard
                                                                    "apply_lemma solved arg"
                                                                    uu____5157
                                                                    g_typ
                                                                    goal.FStar_Tactics_Types.opts
                                                                     in
                                                                    bind
                                                                    uu____5152
                                                                    (fun
                                                                    uu___337_5169
                                                                     ->
                                                                    match uu___337_5169
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
                                                            bind uu____4953
                                                              (fun goals_  ->
                                                                 let sub_goals
                                                                   =
                                                                   let uu____5237
                                                                    =
                                                                    FStar_List.map
                                                                    FStar_Pervasives_Native.fst
                                                                    goals_
                                                                     in
                                                                   FStar_List.flatten
                                                                    uu____5237
                                                                    in
                                                                 let smt_goals
                                                                   =
                                                                   let uu____5259
                                                                    =
                                                                    FStar_List.map
                                                                    FStar_Pervasives_Native.snd
                                                                    goals_
                                                                     in
                                                                   FStar_List.flatten
                                                                    uu____5259
                                                                    in
                                                                 let rec filter'
                                                                   f xs =
                                                                   match xs
                                                                   with
                                                                   | 
                                                                   [] -> []
                                                                   | 
                                                                   x::xs1 ->
                                                                    let uu____5320
                                                                    = f x xs1
                                                                     in
                                                                    if
                                                                    uu____5320
                                                                    then
                                                                    let uu____5323
                                                                    =
                                                                    filter' f
                                                                    xs1  in x
                                                                    ::
                                                                    uu____5323
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
                                                                    let uu____5337
                                                                    =
                                                                    let uu____5338
                                                                    =
                                                                    FStar_Tactics_Types.goal_witness
                                                                    g  in
                                                                    checkone
                                                                    uu____5338
                                                                    goals  in
                                                                    Prims.op_Negation
                                                                    uu____5337)
                                                                    sub_goals
                                                                    in
                                                                 let uu____5339
                                                                   =
                                                                   let uu____5342
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    goal  in
                                                                   proc_guard
                                                                    "apply_lemma guard"
                                                                    uu____5342
                                                                    guard
                                                                    goal.FStar_Tactics_Types.opts
                                                                    in
                                                                 bind
                                                                   uu____5339
                                                                   (fun
                                                                    uu____5345
                                                                     ->
                                                                    let uu____5346
                                                                    =
                                                                    let uu____5349
                                                                    =
                                                                    let uu____5350
                                                                    =
                                                                    let uu____5351
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    goal  in
                                                                    let uu____5352
                                                                    =
                                                                    FStar_Syntax_Util.mk_squash
                                                                    FStar_Syntax_Syntax.U_zero
                                                                    pre1  in
                                                                    istrivial
                                                                    uu____5351
                                                                    uu____5352
                                                                     in
                                                                    Prims.op_Negation
                                                                    uu____5350
                                                                     in
                                                                    if
                                                                    uu____5349
                                                                    then
                                                                    let uu____5355
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    goal  in
                                                                    add_irrelevant_goal
                                                                    "apply_lemma precondition"
                                                                    uu____5355
                                                                    pre1
                                                                    goal.FStar_Tactics_Types.opts
                                                                    else
                                                                    ret ()
                                                                     in
                                                                    bind
                                                                    uu____5346
                                                                    (fun
                                                                    uu____5359
                                                                     ->
                                                                    let uu____5360
                                                                    =
                                                                    add_smt_goals
                                                                    smt_goals
                                                                     in
                                                                    bind
                                                                    uu____5360
                                                                    (fun
                                                                    uu____5364
                                                                     ->
                                                                    add_goals
                                                                    sub_goals1))))))))))))))
         in
      focus uu____4399  in
    FStar_All.pipe_left (wrap_err "apply_lemma") uu____4396
  
let (destruct_eq' :
  FStar_Reflection_Data.typ ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun typ  ->
    let uu____5386 = FStar_Syntax_Util.destruct_typ_as_formula typ  in
    match uu____5386 with
    | FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn
        (l,uu____5396::(e1,uu____5398)::(e2,uu____5400)::[])) when
        FStar_Ident.lid_equals l FStar_Parser_Const.eq2_lid ->
        FStar_Pervasives_Native.Some (e1, e2)
    | uu____5443 -> FStar_Pervasives_Native.None
  
let (destruct_eq :
  FStar_Reflection_Data.typ ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun typ  ->
    let uu____5467 = destruct_eq' typ  in
    match uu____5467 with
    | FStar_Pervasives_Native.Some t -> FStar_Pervasives_Native.Some t
    | FStar_Pervasives_Native.None  ->
        let uu____5497 = FStar_Syntax_Util.un_squash typ  in
        (match uu____5497 with
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
        let uu____5559 = FStar_TypeChecker_Env.pop_bv e1  in
        match uu____5559 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (bv',e') ->
            if FStar_Syntax_Syntax.bv_eq bvar bv'
            then FStar_Pervasives_Native.Some (e', [])
            else
              (let uu____5607 = aux e'  in
               FStar_Util.map_opt uu____5607
                 (fun uu____5631  ->
                    match uu____5631 with | (e'',bvs) -> (e'', (bv' :: bvs))))
         in
      let uu____5652 = aux e  in
      FStar_Util.map_opt uu____5652
        (fun uu____5676  ->
           match uu____5676 with | (e',bvs) -> (e', (FStar_List.rev bvs)))
  
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
          let uu____5743 =
            let uu____5752 = FStar_Tactics_Types.goal_env g  in
            split_env b1 uu____5752  in
          FStar_Util.map_opt uu____5743
            (fun uu____5767  ->
               match uu____5767 with
               | (e0,bvs) ->
                   let s1 bv =
                     let uu___376_5786 = bv  in
                     let uu____5787 =
                       FStar_Syntax_Subst.subst s bv.FStar_Syntax_Syntax.sort
                        in
                     {
                       FStar_Syntax_Syntax.ppname =
                         (uu___376_5786.FStar_Syntax_Syntax.ppname);
                       FStar_Syntax_Syntax.index =
                         (uu___376_5786.FStar_Syntax_Syntax.index);
                       FStar_Syntax_Syntax.sort = uu____5787
                     }  in
                   let bvs1 = FStar_List.map s1 bvs  in
                   let new_env = push_bvs e0 (b2 :: bvs1)  in
                   let new_goal =
                     let uu___377_5795 = g.FStar_Tactics_Types.goal_ctx_uvar
                        in
                     let uu____5796 =
                       FStar_TypeChecker_Env.all_binders new_env  in
                     let uu____5803 =
                       let uu____5806 = FStar_Tactics_Types.goal_type g  in
                       FStar_Syntax_Subst.subst s uu____5806  in
                     {
                       FStar_Syntax_Syntax.ctx_uvar_head =
                         (uu___377_5795.FStar_Syntax_Syntax.ctx_uvar_head);
                       FStar_Syntax_Syntax.ctx_uvar_gamma =
                         (new_env.FStar_TypeChecker_Env.gamma);
                       FStar_Syntax_Syntax.ctx_uvar_binders = uu____5796;
                       FStar_Syntax_Syntax.ctx_uvar_typ = uu____5803;
                       FStar_Syntax_Syntax.ctx_uvar_reason =
                         (uu___377_5795.FStar_Syntax_Syntax.ctx_uvar_reason);
                       FStar_Syntax_Syntax.ctx_uvar_should_check =
                         (uu___377_5795.FStar_Syntax_Syntax.ctx_uvar_should_check);
                       FStar_Syntax_Syntax.ctx_uvar_range =
                         (uu___377_5795.FStar_Syntax_Syntax.ctx_uvar_range)
                     }  in
                   let uu___378_5807 = g  in
                   {
                     FStar_Tactics_Types.goal_main_env =
                       (uu___378_5807.FStar_Tactics_Types.goal_main_env);
                     FStar_Tactics_Types.goal_ctx_uvar = new_goal;
                     FStar_Tactics_Types.opts =
                       (uu___378_5807.FStar_Tactics_Types.opts);
                     FStar_Tactics_Types.is_guard =
                       (uu___378_5807.FStar_Tactics_Types.is_guard)
                   })
  
let (rewrite : FStar_Syntax_Syntax.binder -> unit tac) =
  fun h  ->
    let uu____5817 =
      let uu____5820 = cur_goal ()  in
      bind uu____5820
        (fun goal  ->
           let uu____5828 = h  in
           match uu____5828 with
           | (bv,uu____5832) ->
               mlog
                 (fun uu____5836  ->
                    let uu____5837 = FStar_Syntax_Print.bv_to_string bv  in
                    let uu____5838 =
                      FStar_Syntax_Print.term_to_string
                        bv.FStar_Syntax_Syntax.sort
                       in
                    FStar_Util.print2 "+++Rewrite %s : %s\n" uu____5837
                      uu____5838)
                 (fun uu____5841  ->
                    let uu____5842 =
                      let uu____5851 = FStar_Tactics_Types.goal_env goal  in
                      split_env bv uu____5851  in
                    match uu____5842 with
                    | FStar_Pervasives_Native.None  ->
                        fail "binder not found in environment"
                    | FStar_Pervasives_Native.Some (e0,bvs) ->
                        let uu____5872 =
                          destruct_eq bv.FStar_Syntax_Syntax.sort  in
                        (match uu____5872 with
                         | FStar_Pervasives_Native.Some (x,e) ->
                             let uu____5887 =
                               let uu____5888 = FStar_Syntax_Subst.compress x
                                  in
                               uu____5888.FStar_Syntax_Syntax.n  in
                             (match uu____5887 with
                              | FStar_Syntax_Syntax.Tm_name x1 ->
                                  let s = [FStar_Syntax_Syntax.NT (x1, e)]
                                     in
                                  let s1 bv1 =
                                    let uu___379_5905 = bv1  in
                                    let uu____5906 =
                                      FStar_Syntax_Subst.subst s
                                        bv1.FStar_Syntax_Syntax.sort
                                       in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___379_5905.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___379_5905.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = uu____5906
                                    }  in
                                  let bvs1 = FStar_List.map s1 bvs  in
                                  let new_env = push_bvs e0 (bv :: bvs1)  in
                                  let new_goal =
                                    let uu___380_5914 =
                                      goal.FStar_Tactics_Types.goal_ctx_uvar
                                       in
                                    let uu____5915 =
                                      FStar_TypeChecker_Env.all_binders
                                        new_env
                                       in
                                    let uu____5922 =
                                      let uu____5925 =
                                        FStar_Tactics_Types.goal_type goal
                                         in
                                      FStar_Syntax_Subst.subst s uu____5925
                                       in
                                    {
                                      FStar_Syntax_Syntax.ctx_uvar_head =
                                        (uu___380_5914.FStar_Syntax_Syntax.ctx_uvar_head);
                                      FStar_Syntax_Syntax.ctx_uvar_gamma =
                                        (new_env.FStar_TypeChecker_Env.gamma);
                                      FStar_Syntax_Syntax.ctx_uvar_binders =
                                        uu____5915;
                                      FStar_Syntax_Syntax.ctx_uvar_typ =
                                        uu____5922;
                                      FStar_Syntax_Syntax.ctx_uvar_reason =
                                        (uu___380_5914.FStar_Syntax_Syntax.ctx_uvar_reason);
                                      FStar_Syntax_Syntax.ctx_uvar_should_check
                                        =
                                        (uu___380_5914.FStar_Syntax_Syntax.ctx_uvar_should_check);
                                      FStar_Syntax_Syntax.ctx_uvar_range =
                                        (uu___380_5914.FStar_Syntax_Syntax.ctx_uvar_range)
                                    }  in
                                  replace_cur
                                    (let uu___381_5928 = goal  in
                                     {
                                       FStar_Tactics_Types.goal_main_env =
                                         (uu___381_5928.FStar_Tactics_Types.goal_main_env);
                                       FStar_Tactics_Types.goal_ctx_uvar =
                                         new_goal;
                                       FStar_Tactics_Types.opts =
                                         (uu___381_5928.FStar_Tactics_Types.opts);
                                       FStar_Tactics_Types.is_guard =
                                         (uu___381_5928.FStar_Tactics_Types.is_guard)
                                     })
                              | uu____5929 ->
                                  fail
                                    "Not an equality hypothesis with a variable on the LHS")
                         | uu____5930 -> fail "Not an equality hypothesis")))
       in
    FStar_All.pipe_left (wrap_err "rewrite") uu____5817
  
let (rename_to : FStar_Syntax_Syntax.binder -> Prims.string -> unit tac) =
  fun b  ->
    fun s  ->
      let uu____5955 =
        let uu____5958 = cur_goal ()  in
        bind uu____5958
          (fun goal  ->
             let uu____5969 = b  in
             match uu____5969 with
             | (bv,uu____5973) ->
                 let bv' =
                   let uu____5975 =
                     let uu___382_5976 = bv  in
                     let uu____5977 =
                       FStar_Ident.mk_ident
                         (s,
                           ((bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange))
                        in
                     {
                       FStar_Syntax_Syntax.ppname = uu____5977;
                       FStar_Syntax_Syntax.index =
                         (uu___382_5976.FStar_Syntax_Syntax.index);
                       FStar_Syntax_Syntax.sort =
                         (uu___382_5976.FStar_Syntax_Syntax.sort)
                     }  in
                   FStar_Syntax_Syntax.freshen_bv uu____5975  in
                 let s1 =
                   let uu____5981 =
                     let uu____5982 =
                       let uu____5989 = FStar_Syntax_Syntax.bv_to_name bv'
                          in
                       (bv, uu____5989)  in
                     FStar_Syntax_Syntax.NT uu____5982  in
                   [uu____5981]  in
                 let uu____5994 = subst_goal bv bv' s1 goal  in
                 (match uu____5994 with
                  | FStar_Pervasives_Native.None  ->
                      fail "binder not found in environment"
                  | FStar_Pervasives_Native.Some goal1 -> replace_cur goal1))
         in
      FStar_All.pipe_left (wrap_err "rename_to") uu____5955
  
let (binder_retype : FStar_Syntax_Syntax.binder -> unit tac) =
  fun b  ->
    let uu____6013 =
      let uu____6016 = cur_goal ()  in
      bind uu____6016
        (fun goal  ->
           let uu____6025 = b  in
           match uu____6025 with
           | (bv,uu____6029) ->
               let uu____6030 =
                 let uu____6039 = FStar_Tactics_Types.goal_env goal  in
                 split_env bv uu____6039  in
               (match uu____6030 with
                | FStar_Pervasives_Native.None  ->
                    fail "binder is not present in environment"
                | FStar_Pervasives_Native.Some (e0,bvs) ->
                    let uu____6060 = FStar_Syntax_Util.type_u ()  in
                    (match uu____6060 with
                     | (ty,u) ->
                         let uu____6069 = new_uvar "binder_retype" e0 ty  in
                         bind uu____6069
                           (fun uu____6087  ->
                              match uu____6087 with
                              | (t',u_t') ->
                                  let bv'' =
                                    let uu___383_6097 = bv  in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___383_6097.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___383_6097.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = t'
                                    }  in
                                  let s =
                                    let uu____6101 =
                                      let uu____6102 =
                                        let uu____6109 =
                                          FStar_Syntax_Syntax.bv_to_name bv''
                                           in
                                        (bv, uu____6109)  in
                                      FStar_Syntax_Syntax.NT uu____6102  in
                                    [uu____6101]  in
                                  let bvs1 =
                                    FStar_List.map
                                      (fun b1  ->
                                         let uu___384_6121 = b1  in
                                         let uu____6122 =
                                           FStar_Syntax_Subst.subst s
                                             b1.FStar_Syntax_Syntax.sort
                                            in
                                         {
                                           FStar_Syntax_Syntax.ppname =
                                             (uu___384_6121.FStar_Syntax_Syntax.ppname);
                                           FStar_Syntax_Syntax.index =
                                             (uu___384_6121.FStar_Syntax_Syntax.index);
                                           FStar_Syntax_Syntax.sort =
                                             uu____6122
                                         }) bvs
                                     in
                                  let env' = push_bvs e0 (bv'' :: bvs1)  in
                                  bind __dismiss
                                    (fun uu____6129  ->
                                       let new_goal =
                                         let uu____6131 =
                                           FStar_Tactics_Types.goal_with_env
                                             goal env'
                                            in
                                         let uu____6132 =
                                           let uu____6133 =
                                             FStar_Tactics_Types.goal_type
                                               goal
                                              in
                                           FStar_Syntax_Subst.subst s
                                             uu____6133
                                            in
                                         FStar_Tactics_Types.goal_with_type
                                           uu____6131 uu____6132
                                          in
                                       let uu____6134 = add_goals [new_goal]
                                          in
                                       bind uu____6134
                                         (fun uu____6139  ->
                                            let uu____6140 =
                                              FStar_Syntax_Util.mk_eq2
                                                (FStar_Syntax_Syntax.U_succ u)
                                                ty
                                                bv.FStar_Syntax_Syntax.sort
                                                t'
                                               in
                                            add_irrelevant_goal
                                              "binder_retype equation" e0
                                              uu____6140
                                              goal.FStar_Tactics_Types.opts))))))
       in
    FStar_All.pipe_left (wrap_err "binder_retype") uu____6013
  
let (norm_binder_type :
  FStar_Syntax_Embeddings.norm_step Prims.list ->
    FStar_Syntax_Syntax.binder -> unit tac)
  =
  fun s  ->
    fun b  ->
      let uu____6163 =
        let uu____6166 = cur_goal ()  in
        bind uu____6166
          (fun goal  ->
             let uu____6175 = b  in
             match uu____6175 with
             | (bv,uu____6179) ->
                 let uu____6180 =
                   let uu____6189 = FStar_Tactics_Types.goal_env goal  in
                   split_env bv uu____6189  in
                 (match uu____6180 with
                  | FStar_Pervasives_Native.None  ->
                      fail "binder is not present in environment"
                  | FStar_Pervasives_Native.Some (e0,bvs) ->
                      let steps =
                        let uu____6213 =
                          FStar_TypeChecker_Normalize.tr_norm_steps s  in
                        FStar_List.append
                          [FStar_TypeChecker_Normalize.Reify;
                          FStar_TypeChecker_Normalize.UnfoldTac] uu____6213
                         in
                      let sort' =
                        normalize steps e0 bv.FStar_Syntax_Syntax.sort  in
                      let bv' =
                        let uu___385_6218 = bv  in
                        {
                          FStar_Syntax_Syntax.ppname =
                            (uu___385_6218.FStar_Syntax_Syntax.ppname);
                          FStar_Syntax_Syntax.index =
                            (uu___385_6218.FStar_Syntax_Syntax.index);
                          FStar_Syntax_Syntax.sort = sort'
                        }  in
                      let env' = push_bvs e0 (bv' :: bvs)  in
                      let uu____6220 =
                        FStar_Tactics_Types.goal_with_env goal env'  in
                      replace_cur uu____6220))
         in
      FStar_All.pipe_left (wrap_err "norm_binder_type") uu____6163
  
let (revert : unit -> unit tac) =
  fun uu____6231  ->
    let uu____6234 = cur_goal ()  in
    bind uu____6234
      (fun goal  ->
         let uu____6240 =
           let uu____6247 = FStar_Tactics_Types.goal_env goal  in
           FStar_TypeChecker_Env.pop_bv uu____6247  in
         match uu____6240 with
         | FStar_Pervasives_Native.None  ->
             fail "Cannot revert; empty context"
         | FStar_Pervasives_Native.Some (x,env') ->
             let typ' =
               let uu____6263 =
                 let uu____6266 = FStar_Tactics_Types.goal_type goal  in
                 FStar_Syntax_Syntax.mk_Total uu____6266  in
               FStar_Syntax_Util.arrow [(x, FStar_Pervasives_Native.None)]
                 uu____6263
                in
             let uu____6275 = new_uvar "revert" env' typ'  in
             bind uu____6275
               (fun uu____6290  ->
                  match uu____6290 with
                  | (r,u_r) ->
                      let uu____6299 =
                        let uu____6302 =
                          let uu____6303 =
                            let uu____6304 =
                              FStar_Tactics_Types.goal_type goal  in
                            uu____6304.FStar_Syntax_Syntax.pos  in
                          let uu____6307 =
                            let uu____6312 =
                              let uu____6313 =
                                let uu____6320 =
                                  FStar_Syntax_Syntax.bv_to_name x  in
                                FStar_Syntax_Syntax.as_arg uu____6320  in
                              [uu____6313]  in
                            FStar_Syntax_Syntax.mk_Tm_app r uu____6312  in
                          uu____6307 FStar_Pervasives_Native.None uu____6303
                           in
                        set_solution goal uu____6302  in
                      bind uu____6299
                        (fun uu____6337  ->
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
      let uu____6349 = FStar_Syntax_Free.names t  in
      FStar_Util.set_mem bv uu____6349
  
let rec (clear : FStar_Syntax_Syntax.binder -> unit tac) =
  fun b  ->
    let bv = FStar_Pervasives_Native.fst b  in
    let uu____6362 = cur_goal ()  in
    bind uu____6362
      (fun goal  ->
         mlog
           (fun uu____6370  ->
              let uu____6371 = FStar_Syntax_Print.binder_to_string b  in
              let uu____6372 =
                let uu____6373 =
                  let uu____6374 =
                    let uu____6381 = FStar_Tactics_Types.goal_env goal  in
                    FStar_TypeChecker_Env.all_binders uu____6381  in
                  FStar_All.pipe_right uu____6374 FStar_List.length  in
                FStar_All.pipe_right uu____6373 FStar_Util.string_of_int  in
              FStar_Util.print2 "Clear of (%s), env has %s binders\n"
                uu____6371 uu____6372)
           (fun uu____6394  ->
              let uu____6395 =
                let uu____6404 = FStar_Tactics_Types.goal_env goal  in
                split_env bv uu____6404  in
              match uu____6395 with
              | FStar_Pervasives_Native.None  ->
                  fail "Cannot clear; binder not in environment"
              | FStar_Pervasives_Native.Some (e',bvs) ->
                  let rec check1 bvs1 =
                    match bvs1 with
                    | [] -> ret ()
                    | bv'::bvs2 ->
                        let uu____6443 =
                          free_in bv bv'.FStar_Syntax_Syntax.sort  in
                        if uu____6443
                        then
                          let uu____6446 =
                            let uu____6447 =
                              FStar_Syntax_Print.bv_to_string bv'  in
                            FStar_Util.format1
                              "Cannot clear; binder present in the type of %s"
                              uu____6447
                             in
                          fail uu____6446
                        else check1 bvs2
                     in
                  let uu____6449 =
                    let uu____6450 = FStar_Tactics_Types.goal_type goal  in
                    free_in bv uu____6450  in
                  if uu____6449
                  then fail "Cannot clear; binder present in goal"
                  else
                    (let uu____6454 = check1 bvs  in
                     bind uu____6454
                       (fun uu____6460  ->
                          let env' = push_bvs e' bvs  in
                          let uu____6462 =
                            let uu____6469 =
                              FStar_Tactics_Types.goal_type goal  in
                            new_uvar "clear.witness" env' uu____6469  in
                          bind uu____6462
                            (fun uu____6478  ->
                               match uu____6478 with
                               | (ut,uvar_ut) ->
                                   let uu____6487 = set_solution goal ut  in
                                   bind uu____6487
                                     (fun uu____6492  ->
                                        let uu____6493 =
                                          FStar_Tactics_Types.mk_goal env'
                                            uvar_ut
                                            goal.FStar_Tactics_Types.opts
                                            goal.FStar_Tactics_Types.is_guard
                                           in
                                        replace_cur uu____6493))))))
  
let (clear_top : unit -> unit tac) =
  fun uu____6500  ->
    let uu____6503 = cur_goal ()  in
    bind uu____6503
      (fun goal  ->
         let uu____6509 =
           let uu____6516 = FStar_Tactics_Types.goal_env goal  in
           FStar_TypeChecker_Env.pop_bv uu____6516  in
         match uu____6509 with
         | FStar_Pervasives_Native.None  ->
             fail "Cannot clear; empty context"
         | FStar_Pervasives_Native.Some (x,uu____6524) ->
             let uu____6529 = FStar_Syntax_Syntax.mk_binder x  in
             clear uu____6529)
  
let (prune : Prims.string -> unit tac) =
  fun s  ->
    let uu____6539 = cur_goal ()  in
    bind uu____6539
      (fun g  ->
         let ctx = FStar_Tactics_Types.goal_env g  in
         let ctx' =
           let uu____6549 = FStar_Ident.path_of_text s  in
           FStar_TypeChecker_Env.rem_proof_ns ctx uu____6549  in
         let g' = FStar_Tactics_Types.goal_with_env g ctx'  in
         bind __dismiss (fun uu____6552  -> add_goals [g']))
  
let (addns : Prims.string -> unit tac) =
  fun s  ->
    let uu____6562 = cur_goal ()  in
    bind uu____6562
      (fun g  ->
         let ctx = FStar_Tactics_Types.goal_env g  in
         let ctx' =
           let uu____6572 = FStar_Ident.path_of_text s  in
           FStar_TypeChecker_Env.add_proof_ns ctx uu____6572  in
         let g' = FStar_Tactics_Types.goal_with_env g ctx'  in
         bind __dismiss (fun uu____6575  -> add_goals [g']))
  
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
            let uu____6615 = FStar_Syntax_Subst.compress t  in
            uu____6615.FStar_Syntax_Syntax.n  in
          let uu____6618 =
            if d = FStar_Tactics_Types.TopDown
            then
              f env
                (let uu___389_6624 = t  in
                 {
                   FStar_Syntax_Syntax.n = tn;
                   FStar_Syntax_Syntax.pos =
                     (uu___389_6624.FStar_Syntax_Syntax.pos);
                   FStar_Syntax_Syntax.vars =
                     (uu___389_6624.FStar_Syntax_Syntax.vars)
                 })
            else ret t  in
          bind uu____6618
            (fun t1  ->
               let ff = tac_fold_env d f env  in
               let tn1 =
                 let uu____6640 =
                   let uu____6641 = FStar_Syntax_Subst.compress t1  in
                   uu____6641.FStar_Syntax_Syntax.n  in
                 match uu____6640 with
                 | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
                     let uu____6668 = ff hd1  in
                     bind uu____6668
                       (fun hd2  ->
                          let fa uu____6690 =
                            match uu____6690 with
                            | (a,q) ->
                                let uu____6703 = ff a  in
                                bind uu____6703 (fun a1  -> ret (a1, q))
                             in
                          let uu____6716 = mapM fa args  in
                          bind uu____6716
                            (fun args1  ->
                               ret (FStar_Syntax_Syntax.Tm_app (hd2, args1))))
                 | FStar_Syntax_Syntax.Tm_abs (bs,t2,k) ->
                     let uu____6782 = FStar_Syntax_Subst.open_term bs t2  in
                     (match uu____6782 with
                      | (bs1,t') ->
                          let uu____6791 =
                            let uu____6794 =
                              FStar_TypeChecker_Env.push_binders env bs1  in
                            tac_fold_env d f uu____6794 t'  in
                          bind uu____6791
                            (fun t''  ->
                               let uu____6798 =
                                 let uu____6799 =
                                   let uu____6816 =
                                     FStar_Syntax_Subst.close_binders bs1  in
                                   let uu____6823 =
                                     FStar_Syntax_Subst.close bs1 t''  in
                                   (uu____6816, uu____6823, k)  in
                                 FStar_Syntax_Syntax.Tm_abs uu____6799  in
                               ret uu____6798))
                 | FStar_Syntax_Syntax.Tm_arrow (bs,k) -> ret tn
                 | FStar_Syntax_Syntax.Tm_match (hd1,brs) ->
                     let uu____6892 = ff hd1  in
                     bind uu____6892
                       (fun hd2  ->
                          let ffb br =
                            let uu____6907 =
                              FStar_Syntax_Subst.open_branch br  in
                            match uu____6907 with
                            | (pat,w,e) ->
                                let bvs = FStar_Syntax_Syntax.pat_bvs pat  in
                                let ff1 =
                                  let uu____6939 =
                                    FStar_TypeChecker_Env.push_bvs env bvs
                                     in
                                  tac_fold_env d f uu____6939  in
                                let uu____6940 = ff1 e  in
                                bind uu____6940
                                  (fun e1  ->
                                     let br1 =
                                       FStar_Syntax_Subst.close_branch
                                         (pat, w, e1)
                                        in
                                     ret br1)
                             in
                          let uu____6955 = mapM ffb brs  in
                          bind uu____6955
                            (fun brs1  ->
                               ret (FStar_Syntax_Syntax.Tm_match (hd2, brs1))))
                 | FStar_Syntax_Syntax.Tm_let
                     ((false
                       ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inl bv;
                          FStar_Syntax_Syntax.lbunivs = uu____6999;
                          FStar_Syntax_Syntax.lbtyp = uu____7000;
                          FStar_Syntax_Syntax.lbeff = uu____7001;
                          FStar_Syntax_Syntax.lbdef = def;
                          FStar_Syntax_Syntax.lbattrs = uu____7003;
                          FStar_Syntax_Syntax.lbpos = uu____7004;_}::[]),e)
                     ->
                     let lb =
                       let uu____7029 =
                         let uu____7030 = FStar_Syntax_Subst.compress t1  in
                         uu____7030.FStar_Syntax_Syntax.n  in
                       match uu____7029 with
                       | FStar_Syntax_Syntax.Tm_let
                           ((false ,lb::[]),uu____7034) -> lb
                       | uu____7047 -> failwith "impossible"  in
                     let fflb lb1 =
                       let uu____7056 = ff lb1.FStar_Syntax_Syntax.lbdef  in
                       bind uu____7056
                         (fun def1  ->
                            ret
                              (let uu___386_7062 = lb1  in
                               {
                                 FStar_Syntax_Syntax.lbname =
                                   (uu___386_7062.FStar_Syntax_Syntax.lbname);
                                 FStar_Syntax_Syntax.lbunivs =
                                   (uu___386_7062.FStar_Syntax_Syntax.lbunivs);
                                 FStar_Syntax_Syntax.lbtyp =
                                   (uu___386_7062.FStar_Syntax_Syntax.lbtyp);
                                 FStar_Syntax_Syntax.lbeff =
                                   (uu___386_7062.FStar_Syntax_Syntax.lbeff);
                                 FStar_Syntax_Syntax.lbdef = def1;
                                 FStar_Syntax_Syntax.lbattrs =
                                   (uu___386_7062.FStar_Syntax_Syntax.lbattrs);
                                 FStar_Syntax_Syntax.lbpos =
                                   (uu___386_7062.FStar_Syntax_Syntax.lbpos)
                               }))
                        in
                     let uu____7063 = fflb lb  in
                     bind uu____7063
                       (fun lb1  ->
                          let uu____7073 =
                            let uu____7078 =
                              let uu____7079 =
                                FStar_Syntax_Syntax.mk_binder bv  in
                              [uu____7079]  in
                            FStar_Syntax_Subst.open_term uu____7078 e  in
                          match uu____7073 with
                          | (bs,e1) ->
                              let ff1 =
                                let uu____7103 =
                                  FStar_TypeChecker_Env.push_binders env bs
                                   in
                                tac_fold_env d f uu____7103  in
                              let uu____7104 = ff1 e1  in
                              bind uu____7104
                                (fun e2  ->
                                   let e3 = FStar_Syntax_Subst.close bs e2
                                      in
                                   ret
                                     (FStar_Syntax_Syntax.Tm_let
                                        ((false, [lb1]), e3))))
                 | FStar_Syntax_Syntax.Tm_let ((true ,lbs),e) ->
                     let fflb lb =
                       let uu____7145 = ff lb.FStar_Syntax_Syntax.lbdef  in
                       bind uu____7145
                         (fun def  ->
                            ret
                              (let uu___387_7151 = lb  in
                               {
                                 FStar_Syntax_Syntax.lbname =
                                   (uu___387_7151.FStar_Syntax_Syntax.lbname);
                                 FStar_Syntax_Syntax.lbunivs =
                                   (uu___387_7151.FStar_Syntax_Syntax.lbunivs);
                                 FStar_Syntax_Syntax.lbtyp =
                                   (uu___387_7151.FStar_Syntax_Syntax.lbtyp);
                                 FStar_Syntax_Syntax.lbeff =
                                   (uu___387_7151.FStar_Syntax_Syntax.lbeff);
                                 FStar_Syntax_Syntax.lbdef = def;
                                 FStar_Syntax_Syntax.lbattrs =
                                   (uu___387_7151.FStar_Syntax_Syntax.lbattrs);
                                 FStar_Syntax_Syntax.lbpos =
                                   (uu___387_7151.FStar_Syntax_Syntax.lbpos)
                               }))
                        in
                     let uu____7152 = FStar_Syntax_Subst.open_let_rec lbs e
                        in
                     (match uu____7152 with
                      | (lbs1,e1) ->
                          let uu____7167 = mapM fflb lbs1  in
                          bind uu____7167
                            (fun lbs2  ->
                               let uu____7179 = ff e1  in
                               bind uu____7179
                                 (fun e2  ->
                                    let uu____7187 =
                                      FStar_Syntax_Subst.close_let_rec lbs2
                                        e2
                                       in
                                    match uu____7187 with
                                    | (lbs3,e3) ->
                                        ret
                                          (FStar_Syntax_Syntax.Tm_let
                                             ((true, lbs3), e3)))))
                 | FStar_Syntax_Syntax.Tm_ascribed (t2,asc,eff) ->
                     let uu____7255 = ff t2  in
                     bind uu____7255
                       (fun t3  ->
                          ret
                            (FStar_Syntax_Syntax.Tm_ascribed (t3, asc, eff)))
                 | FStar_Syntax_Syntax.Tm_meta (t2,m) ->
                     let uu____7286 = ff t2  in
                     bind uu____7286
                       (fun t3  -> ret (FStar_Syntax_Syntax.Tm_meta (t3, m)))
                 | uu____7293 -> ret tn  in
               bind tn1
                 (fun tn2  ->
                    let t' =
                      let uu___388_7300 = t1  in
                      {
                        FStar_Syntax_Syntax.n = tn2;
                        FStar_Syntax_Syntax.pos =
                          (uu___388_7300.FStar_Syntax_Syntax.pos);
                        FStar_Syntax_Syntax.vars =
                          (uu___388_7300.FStar_Syntax_Syntax.vars)
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
            let uu____7337 = FStar_TypeChecker_TcTerm.tc_term env t  in
            match uu____7337 with
            | (t1,lcomp,g) ->
                let uu____7349 =
                  (let uu____7352 =
                     FStar_Syntax_Util.is_pure_or_ghost_lcomp lcomp  in
                   Prims.op_Negation uu____7352) ||
                    (let uu____7354 = FStar_TypeChecker_Rel.is_trivial g  in
                     Prims.op_Negation uu____7354)
                   in
                if uu____7349
                then ret t1
                else
                  (let rewrite_eq =
                     let typ = lcomp.FStar_Syntax_Syntax.res_typ  in
                     let uu____7362 = new_uvar "pointwise_rec" env typ  in
                     bind uu____7362
                       (fun uu____7378  ->
                          match uu____7378 with
                          | (ut,uvar_ut) ->
                              (log ps
                                 (fun uu____7391  ->
                                    let uu____7392 =
                                      FStar_Syntax_Print.term_to_string t1
                                       in
                                    let uu____7393 =
                                      FStar_Syntax_Print.term_to_string ut
                                       in
                                    FStar_Util.print2
                                      "Pointwise_rec: making equality\n\t%s ==\n\t%s\n"
                                      uu____7392 uu____7393);
                               (let uu____7394 =
                                  let uu____7397 =
                                    let uu____7398 =
                                      FStar_TypeChecker_TcTerm.universe_of
                                        env typ
                                       in
                                    FStar_Syntax_Util.mk_eq2 uu____7398 typ
                                      t1 ut
                                     in
                                  add_irrelevant_goal
                                    "pointwise_rec equation" env uu____7397
                                    opts
                                   in
                                bind uu____7394
                                  (fun uu____7401  ->
                                     let uu____7402 =
                                       bind tau
                                         (fun uu____7408  ->
                                            let ut1 =
                                              FStar_TypeChecker_Normalize.reduce_uvar_solutions
                                                env ut
                                               in
                                            log ps
                                              (fun uu____7414  ->
                                                 let uu____7415 =
                                                   FStar_Syntax_Print.term_to_string
                                                     t1
                                                    in
                                                 let uu____7416 =
                                                   FStar_Syntax_Print.term_to_string
                                                     ut1
                                                    in
                                                 FStar_Util.print2
                                                   "Pointwise_rec: succeeded rewriting\n\t%s to\n\t%s\n"
                                                   uu____7415 uu____7416);
                                            ret ut1)
                                        in
                                     focus uu____7402))))
                      in
                   let uu____7417 = trytac' rewrite_eq  in
                   bind uu____7417
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
          let uu____7615 = FStar_Syntax_Subst.compress t  in
          maybe_continue ctrl uu____7615
            (fun t1  ->
               let uu____7623 =
                 f env
                   (let uu___392_7632 = t1  in
                    {
                      FStar_Syntax_Syntax.n = (t1.FStar_Syntax_Syntax.n);
                      FStar_Syntax_Syntax.pos =
                        (uu___392_7632.FStar_Syntax_Syntax.pos);
                      FStar_Syntax_Syntax.vars =
                        (uu___392_7632.FStar_Syntax_Syntax.vars)
                    })
                  in
               bind uu____7623
                 (fun uu____7648  ->
                    match uu____7648 with
                    | (t2,ctrl1) ->
                        maybe_continue ctrl1 t2
                          (fun t3  ->
                             let uu____7671 =
                               let uu____7672 =
                                 FStar_Syntax_Subst.compress t3  in
                               uu____7672.FStar_Syntax_Syntax.n  in
                             match uu____7671 with
                             | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
                                 let uu____7705 =
                                   ctrl_tac_fold f env ctrl1 hd1  in
                                 bind uu____7705
                                   (fun uu____7730  ->
                                      match uu____7730 with
                                      | (hd2,ctrl2) ->
                                          let ctrl3 = keep_going ctrl2  in
                                          let uu____7746 =
                                            ctrl_tac_fold_args f env ctrl3
                                              args
                                             in
                                          bind uu____7746
                                            (fun uu____7773  ->
                                               match uu____7773 with
                                               | (args1,ctrl4) ->
                                                   ret
                                                     ((let uu___390_7803 = t3
                                                          in
                                                       {
                                                         FStar_Syntax_Syntax.n
                                                           =
                                                           (FStar_Syntax_Syntax.Tm_app
                                                              (hd2, args1));
                                                         FStar_Syntax_Syntax.pos
                                                           =
                                                           (uu___390_7803.FStar_Syntax_Syntax.pos);
                                                         FStar_Syntax_Syntax.vars
                                                           =
                                                           (uu___390_7803.FStar_Syntax_Syntax.vars)
                                                       }), ctrl4)))
                             | FStar_Syntax_Syntax.Tm_abs (bs,t4,k) ->
                                 let uu____7839 =
                                   FStar_Syntax_Subst.open_term bs t4  in
                                 (match uu____7839 with
                                  | (bs1,t') ->
                                      let uu____7854 =
                                        let uu____7861 =
                                          FStar_TypeChecker_Env.push_binders
                                            env bs1
                                           in
                                        ctrl_tac_fold f uu____7861 ctrl1 t'
                                         in
                                      bind uu____7854
                                        (fun uu____7879  ->
                                           match uu____7879 with
                                           | (t'',ctrl2) ->
                                               let uu____7894 =
                                                 let uu____7901 =
                                                   let uu___391_7904 = t4  in
                                                   let uu____7907 =
                                                     let uu____7908 =
                                                       let uu____7925 =
                                                         FStar_Syntax_Subst.close_binders
                                                           bs1
                                                          in
                                                       let uu____7932 =
                                                         FStar_Syntax_Subst.close
                                                           bs1 t''
                                                          in
                                                       (uu____7925,
                                                         uu____7932, k)
                                                        in
                                                     FStar_Syntax_Syntax.Tm_abs
                                                       uu____7908
                                                      in
                                                   {
                                                     FStar_Syntax_Syntax.n =
                                                       uu____7907;
                                                     FStar_Syntax_Syntax.pos
                                                       =
                                                       (uu___391_7904.FStar_Syntax_Syntax.pos);
                                                     FStar_Syntax_Syntax.vars
                                                       =
                                                       (uu___391_7904.FStar_Syntax_Syntax.vars)
                                                   }  in
                                                 (uu____7901, ctrl2)  in
                                               ret uu____7894))
                             | FStar_Syntax_Syntax.Tm_arrow (bs,k) ->
                                 ret (t3, ctrl1)
                             | uu____7979 -> ret (t3, ctrl1))))

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
              let uu____8022 = ctrl_tac_fold f env ctrl t  in
              bind uu____8022
                (fun uu____8046  ->
                   match uu____8046 with
                   | (t1,ctrl1) ->
                       let uu____8061 = ctrl_tac_fold_args f env ctrl1 ts1
                          in
                       bind uu____8061
                         (fun uu____8088  ->
                            match uu____8088 with
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
              let uu____8170 =
                let uu____8177 =
                  add_irrelevant_goal "dummy" env FStar_Syntax_Util.t_true
                    opts
                   in
                bind uu____8177
                  (fun uu____8186  ->
                     let uu____8187 = ctrl t1  in
                     bind uu____8187
                       (fun res  ->
                          let uu____8210 = trivial ()  in
                          bind uu____8210 (fun uu____8218  -> ret res)))
                 in
              bind uu____8170
                (fun uu____8234  ->
                   match uu____8234 with
                   | (should_rewrite,ctrl1) ->
                       if Prims.op_Negation should_rewrite
                       then ret (t1, ctrl1)
                       else
                         (let uu____8258 =
                            FStar_TypeChecker_TcTerm.tc_term env t1  in
                          match uu____8258 with
                          | (t2,lcomp,g) ->
                              let uu____8274 =
                                (let uu____8277 =
                                   FStar_Syntax_Util.is_pure_or_ghost_lcomp
                                     lcomp
                                    in
                                 Prims.op_Negation uu____8277) ||
                                  (let uu____8279 =
                                     FStar_TypeChecker_Rel.is_trivial g  in
                                   Prims.op_Negation uu____8279)
                                 in
                              if uu____8274
                              then ret (t2, globalStop)
                              else
                                (let typ = lcomp.FStar_Syntax_Syntax.res_typ
                                    in
                                 let uu____8292 =
                                   new_uvar "pointwise_rec" env typ  in
                                 bind uu____8292
                                   (fun uu____8312  ->
                                      match uu____8312 with
                                      | (ut,uvar_ut) ->
                                          (log ps
                                             (fun uu____8329  ->
                                                let uu____8330 =
                                                  FStar_Syntax_Print.term_to_string
                                                    t2
                                                   in
                                                let uu____8331 =
                                                  FStar_Syntax_Print.term_to_string
                                                    ut
                                                   in
                                                FStar_Util.print2
                                                  "Pointwise_rec: making equality\n\t%s ==\n\t%s\n"
                                                  uu____8330 uu____8331);
                                           (let uu____8332 =
                                              let uu____8335 =
                                                let uu____8336 =
                                                  FStar_TypeChecker_TcTerm.universe_of
                                                    env typ
                                                   in
                                                FStar_Syntax_Util.mk_eq2
                                                  uu____8336 typ t2 ut
                                                 in
                                              add_irrelevant_goal
                                                "rewrite_rec equation" env
                                                uu____8335 opts
                                               in
                                            bind uu____8332
                                              (fun uu____8343  ->
                                                 let uu____8344 =
                                                   bind rewriter
                                                     (fun uu____8358  ->
                                                        let ut1 =
                                                          FStar_TypeChecker_Normalize.reduce_uvar_solutions
                                                            env ut
                                                           in
                                                        log ps
                                                          (fun uu____8364  ->
                                                             let uu____8365 =
                                                               FStar_Syntax_Print.term_to_string
                                                                 t2
                                                                in
                                                             let uu____8366 =
                                                               FStar_Syntax_Print.term_to_string
                                                                 ut1
                                                                in
                                                             FStar_Util.print2
                                                               "rewrite_rec: succeeded rewriting\n\t%s to\n\t%s\n"
                                                               uu____8365
                                                               uu____8366);
                                                        ret (ut1, ctrl1))
                                                    in
                                                 focus uu____8344)))))))
  
let (topdown_rewrite :
  (FStar_Syntax_Syntax.term ->
     (Prims.bool,FStar_BigInt.t) FStar_Pervasives_Native.tuple2 tac)
    -> unit tac -> unit tac)
  =
  fun ctrl  ->
    fun rewriter  ->
      let uu____8407 =
        bind get
          (fun ps  ->
             let uu____8417 =
               match ps.FStar_Tactics_Types.goals with
               | g::gs -> (g, gs)
               | [] -> failwith "no goals"  in
             match uu____8417 with
             | (g,gs) ->
                 let gt1 = FStar_Tactics_Types.goal_type g  in
                 (log ps
                    (fun uu____8454  ->
                       let uu____8455 = FStar_Syntax_Print.term_to_string gt1
                          in
                       FStar_Util.print1 "Topdown_rewrite starting with %s\n"
                         uu____8455);
                  bind dismiss_all
                    (fun uu____8458  ->
                       let uu____8459 =
                         let uu____8466 = FStar_Tactics_Types.goal_env g  in
                         ctrl_tac_fold
                           (rewrite_rec ps ctrl rewriter
                              g.FStar_Tactics_Types.opts) uu____8466
                           keepGoing gt1
                          in
                       bind uu____8459
                         (fun uu____8478  ->
                            match uu____8478 with
                            | (gt',uu____8486) ->
                                (log ps
                                   (fun uu____8490  ->
                                      let uu____8491 =
                                        FStar_Syntax_Print.term_to_string gt'
                                         in
                                      FStar_Util.print1
                                        "Topdown_rewrite seems to have succeded with %s\n"
                                        uu____8491);
                                 (let uu____8492 = push_goals gs  in
                                  bind uu____8492
                                    (fun uu____8497  ->
                                       let uu____8498 =
                                         let uu____8501 =
                                           FStar_Tactics_Types.goal_with_type
                                             g gt'
                                            in
                                         [uu____8501]  in
                                       add_goals uu____8498)))))))
         in
      FStar_All.pipe_left (wrap_err "topdown_rewrite") uu____8407
  
let (pointwise : FStar_Tactics_Types.direction -> unit tac -> unit tac) =
  fun d  ->
    fun tau  ->
      let uu____8524 =
        bind get
          (fun ps  ->
             let uu____8534 =
               match ps.FStar_Tactics_Types.goals with
               | g::gs -> (g, gs)
               | [] -> failwith "no goals"  in
             match uu____8534 with
             | (g,gs) ->
                 let gt1 = FStar_Tactics_Types.goal_type g  in
                 (log ps
                    (fun uu____8571  ->
                       let uu____8572 = FStar_Syntax_Print.term_to_string gt1
                          in
                       FStar_Util.print1 "Pointwise starting with %s\n"
                         uu____8572);
                  bind dismiss_all
                    (fun uu____8575  ->
                       let uu____8576 =
                         let uu____8579 = FStar_Tactics_Types.goal_env g  in
                         tac_fold_env d
                           (pointwise_rec ps tau g.FStar_Tactics_Types.opts)
                           uu____8579 gt1
                          in
                       bind uu____8576
                         (fun gt'  ->
                            log ps
                              (fun uu____8587  ->
                                 let uu____8588 =
                                   FStar_Syntax_Print.term_to_string gt'  in
                                 FStar_Util.print1
                                   "Pointwise seems to have succeded with %s\n"
                                   uu____8588);
                            (let uu____8589 = push_goals gs  in
                             bind uu____8589
                               (fun uu____8594  ->
                                  let uu____8595 =
                                    let uu____8598 =
                                      FStar_Tactics_Types.goal_with_type g
                                        gt'
                                       in
                                    [uu____8598]  in
                                  add_goals uu____8595))))))
         in
      FStar_All.pipe_left (wrap_err "pointwise") uu____8524
  
let (trefl : unit -> unit tac) =
  fun uu____8609  ->
    let uu____8612 =
      let uu____8615 = cur_goal ()  in
      bind uu____8615
        (fun g  ->
           let uu____8633 =
             let uu____8638 = FStar_Tactics_Types.goal_type g  in
             FStar_Syntax_Util.un_squash uu____8638  in
           match uu____8633 with
           | FStar_Pervasives_Native.Some t ->
               let uu____8646 = FStar_Syntax_Util.head_and_args' t  in
               (match uu____8646 with
                | (hd1,args) ->
                    let uu____8679 =
                      let uu____8690 =
                        let uu____8691 = FStar_Syntax_Util.un_uinst hd1  in
                        uu____8691.FStar_Syntax_Syntax.n  in
                      (uu____8690, args)  in
                    (match uu____8679 with
                     | (FStar_Syntax_Syntax.Tm_fvar
                        fv,uu____8703::(l,uu____8705)::(r,uu____8707)::[])
                         when
                         FStar_Syntax_Syntax.fv_eq_lid fv
                           FStar_Parser_Const.eq2_lid
                         ->
                         let uu____8734 =
                           let uu____8737 = FStar_Tactics_Types.goal_env g
                              in
                           do_unify uu____8737 l r  in
                         bind uu____8734
                           (fun b  ->
                              if Prims.op_Negation b
                              then
                                let uu____8744 =
                                  let uu____8745 =
                                    FStar_Tactics_Types.goal_env g  in
                                  tts uu____8745 l  in
                                let uu____8746 =
                                  let uu____8747 =
                                    FStar_Tactics_Types.goal_env g  in
                                  tts uu____8747 r  in
                                fail2 "not a trivial equality (%s vs %s)"
                                  uu____8744 uu____8746
                              else solve' g FStar_Syntax_Util.exp_unit)
                     | (hd2,uu____8750) ->
                         let uu____8763 =
                           let uu____8764 = FStar_Tactics_Types.goal_env g
                              in
                           tts uu____8764 t  in
                         fail1 "trefl: not an equality (%s)" uu____8763))
           | FStar_Pervasives_Native.None  -> fail "not an irrelevant goal")
       in
    FStar_All.pipe_left (wrap_err "trefl") uu____8612
  
let (dup : unit -> unit tac) =
  fun uu____8777  ->
    let uu____8780 = cur_goal ()  in
    bind uu____8780
      (fun g  ->
         let uu____8786 =
           let uu____8793 = FStar_Tactics_Types.goal_env g  in
           let uu____8794 = FStar_Tactics_Types.goal_type g  in
           new_uvar "dup" uu____8793 uu____8794  in
         bind uu____8786
           (fun uu____8803  ->
              match uu____8803 with
              | (u,u_uvar) ->
                  let g' =
                    let uu___393_8813 = g  in
                    {
                      FStar_Tactics_Types.goal_main_env =
                        (uu___393_8813.FStar_Tactics_Types.goal_main_env);
                      FStar_Tactics_Types.goal_ctx_uvar = u_uvar;
                      FStar_Tactics_Types.opts =
                        (uu___393_8813.FStar_Tactics_Types.opts);
                      FStar_Tactics_Types.is_guard =
                        (uu___393_8813.FStar_Tactics_Types.is_guard)
                    }  in
                  bind __dismiss
                    (fun uu____8816  ->
                       let uu____8817 =
                         let uu____8820 = FStar_Tactics_Types.goal_env g  in
                         let uu____8821 =
                           let uu____8822 =
                             let uu____8823 = FStar_Tactics_Types.goal_env g
                                in
                             let uu____8824 = FStar_Tactics_Types.goal_type g
                                in
                             FStar_TypeChecker_TcTerm.universe_of uu____8823
                               uu____8824
                              in
                           let uu____8825 = FStar_Tactics_Types.goal_type g
                              in
                           let uu____8826 =
                             FStar_Tactics_Types.goal_witness g  in
                           FStar_Syntax_Util.mk_eq2 uu____8822 uu____8825 u
                             uu____8826
                            in
                         add_irrelevant_goal "dup equation" uu____8820
                           uu____8821 g.FStar_Tactics_Types.opts
                          in
                       bind uu____8817
                         (fun uu____8829  ->
                            let uu____8830 = add_goals [g']  in
                            bind uu____8830 (fun uu____8834  -> ret ())))))
  
let (flip : unit -> unit tac) =
  fun uu____8841  ->
    bind get
      (fun ps  ->
         match ps.FStar_Tactics_Types.goals with
         | g1::g2::gs ->
             set
               (let uu___394_8858 = ps  in
                {
                  FStar_Tactics_Types.main_context =
                    (uu___394_8858.FStar_Tactics_Types.main_context);
                  FStar_Tactics_Types.main_goal =
                    (uu___394_8858.FStar_Tactics_Types.main_goal);
                  FStar_Tactics_Types.all_implicits =
                    (uu___394_8858.FStar_Tactics_Types.all_implicits);
                  FStar_Tactics_Types.goals = (g2 :: g1 :: gs);
                  FStar_Tactics_Types.smt_goals =
                    (uu___394_8858.FStar_Tactics_Types.smt_goals);
                  FStar_Tactics_Types.depth =
                    (uu___394_8858.FStar_Tactics_Types.depth);
                  FStar_Tactics_Types.__dump =
                    (uu___394_8858.FStar_Tactics_Types.__dump);
                  FStar_Tactics_Types.psc =
                    (uu___394_8858.FStar_Tactics_Types.psc);
                  FStar_Tactics_Types.entry_range =
                    (uu___394_8858.FStar_Tactics_Types.entry_range);
                  FStar_Tactics_Types.guard_policy =
                    (uu___394_8858.FStar_Tactics_Types.guard_policy);
                  FStar_Tactics_Types.freshness =
                    (uu___394_8858.FStar_Tactics_Types.freshness);
                  FStar_Tactics_Types.tac_verb_dbg =
                    (uu___394_8858.FStar_Tactics_Types.tac_verb_dbg)
                })
         | uu____8859 -> fail "flip: less than 2 goals")
  
let (later : unit -> unit tac) =
  fun uu____8868  ->
    bind get
      (fun ps  ->
         match ps.FStar_Tactics_Types.goals with
         | [] -> ret ()
         | g::gs ->
             set
               (let uu___395_8881 = ps  in
                {
                  FStar_Tactics_Types.main_context =
                    (uu___395_8881.FStar_Tactics_Types.main_context);
                  FStar_Tactics_Types.main_goal =
                    (uu___395_8881.FStar_Tactics_Types.main_goal);
                  FStar_Tactics_Types.all_implicits =
                    (uu___395_8881.FStar_Tactics_Types.all_implicits);
                  FStar_Tactics_Types.goals = (FStar_List.append gs [g]);
                  FStar_Tactics_Types.smt_goals =
                    (uu___395_8881.FStar_Tactics_Types.smt_goals);
                  FStar_Tactics_Types.depth =
                    (uu___395_8881.FStar_Tactics_Types.depth);
                  FStar_Tactics_Types.__dump =
                    (uu___395_8881.FStar_Tactics_Types.__dump);
                  FStar_Tactics_Types.psc =
                    (uu___395_8881.FStar_Tactics_Types.psc);
                  FStar_Tactics_Types.entry_range =
                    (uu___395_8881.FStar_Tactics_Types.entry_range);
                  FStar_Tactics_Types.guard_policy =
                    (uu___395_8881.FStar_Tactics_Types.guard_policy);
                  FStar_Tactics_Types.freshness =
                    (uu___395_8881.FStar_Tactics_Types.freshness);
                  FStar_Tactics_Types.tac_verb_dbg =
                    (uu___395_8881.FStar_Tactics_Types.tac_verb_dbg)
                }))
  
let (qed : unit -> unit tac) =
  fun uu____8888  ->
    bind get
      (fun ps  ->
         match ps.FStar_Tactics_Types.goals with
         | [] -> ret ()
         | uu____8895 -> fail "Not done!")
  
let (cases :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 tac)
  =
  fun t  ->
    let uu____8915 =
      let uu____8922 = cur_goal ()  in
      bind uu____8922
        (fun g  ->
           let uu____8932 =
             let uu____8941 = FStar_Tactics_Types.goal_env g  in
             __tc uu____8941 t  in
           bind uu____8932
             (fun uu____8969  ->
                match uu____8969 with
                | (t1,typ,guard) ->
                    let uu____8985 = FStar_Syntax_Util.head_and_args typ  in
                    (match uu____8985 with
                     | (hd1,args) ->
                         let uu____9028 =
                           let uu____9041 =
                             let uu____9042 = FStar_Syntax_Util.un_uinst hd1
                                in
                             uu____9042.FStar_Syntax_Syntax.n  in
                           (uu____9041, args)  in
                         (match uu____9028 with
                          | (FStar_Syntax_Syntax.Tm_fvar
                             fv,(p,uu____9061)::(q,uu____9063)::[]) when
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
                                let uu____9101 =
                                  let uu____9102 =
                                    FStar_Tactics_Types.goal_env g  in
                                  FStar_TypeChecker_Env.push_bv uu____9102
                                    v_p
                                   in
                                FStar_Tactics_Types.goal_with_env g
                                  uu____9101
                                 in
                              let g2 =
                                let uu____9104 =
                                  let uu____9105 =
                                    FStar_Tactics_Types.goal_env g  in
                                  FStar_TypeChecker_Env.push_bv uu____9105
                                    v_q
                                   in
                                FStar_Tactics_Types.goal_with_env g
                                  uu____9104
                                 in
                              bind __dismiss
                                (fun uu____9112  ->
                                   let uu____9113 = add_goals [g1; g2]  in
                                   bind uu____9113
                                     (fun uu____9122  ->
                                        let uu____9123 =
                                          let uu____9128 =
                                            FStar_Syntax_Syntax.bv_to_name
                                              v_p
                                             in
                                          let uu____9129 =
                                            FStar_Syntax_Syntax.bv_to_name
                                              v_q
                                             in
                                          (uu____9128, uu____9129)  in
                                        ret uu____9123))
                          | uu____9134 ->
                              let uu____9147 =
                                let uu____9148 =
                                  FStar_Tactics_Types.goal_env g  in
                                tts uu____9148 typ  in
                              fail1 "Not a disjunction: %s" uu____9147))))
       in
    FStar_All.pipe_left (wrap_err "cases") uu____8915
  
let (set_options : Prims.string -> unit tac) =
  fun s  ->
    let uu____9178 =
      let uu____9181 = cur_goal ()  in
      bind uu____9181
        (fun g  ->
           FStar_Options.push ();
           (let uu____9194 = FStar_Util.smap_copy g.FStar_Tactics_Types.opts
               in
            FStar_Options.set uu____9194);
           (let res = FStar_Options.set_options FStar_Options.Set s  in
            let opts' = FStar_Options.peek ()  in
            FStar_Options.pop ();
            (match res with
             | FStar_Getopt.Success  ->
                 let g' =
                   let uu___396_9201 = g  in
                   {
                     FStar_Tactics_Types.goal_main_env =
                       (uu___396_9201.FStar_Tactics_Types.goal_main_env);
                     FStar_Tactics_Types.goal_ctx_uvar =
                       (uu___396_9201.FStar_Tactics_Types.goal_ctx_uvar);
                     FStar_Tactics_Types.opts = opts';
                     FStar_Tactics_Types.is_guard =
                       (uu___396_9201.FStar_Tactics_Types.is_guard)
                   }  in
                 replace_cur g'
             | FStar_Getopt.Error err ->
                 fail2 "Setting options `%s` failed: %s" s err
             | FStar_Getopt.Help  ->
                 fail1 "Setting options `%s` failed (got `Help`?)" s)))
       in
    FStar_All.pipe_left (wrap_err "set_options") uu____9178
  
let (top_env : unit -> env tac) =
  fun uu____9213  ->
    bind get
      (fun ps  -> FStar_All.pipe_left ret ps.FStar_Tactics_Types.main_context)
  
let (cur_env : unit -> env tac) =
  fun uu____9226  ->
    let uu____9229 = cur_goal ()  in
    bind uu____9229
      (fun g  ->
         let uu____9235 = FStar_Tactics_Types.goal_env g  in
         FStar_All.pipe_left ret uu____9235)
  
let (cur_goal' : unit -> FStar_Syntax_Syntax.term tac) =
  fun uu____9244  ->
    let uu____9247 = cur_goal ()  in
    bind uu____9247
      (fun g  ->
         let uu____9253 = FStar_Tactics_Types.goal_type g  in
         FStar_All.pipe_left ret uu____9253)
  
let (cur_witness : unit -> FStar_Syntax_Syntax.term tac) =
  fun uu____9262  ->
    let uu____9265 = cur_goal ()  in
    bind uu____9265
      (fun g  ->
         let uu____9271 = FStar_Tactics_Types.goal_witness g  in
         FStar_All.pipe_left ret uu____9271)
  
let (unquote :
  FStar_Reflection_Data.typ ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term tac)
  =
  fun ty  ->
    fun tm  ->
      let uu____9288 =
        mlog
          (fun uu____9293  ->
             let uu____9294 = FStar_Syntax_Print.term_to_string tm  in
             FStar_Util.print1 "unquote: tm = %s\n" uu____9294)
          (fun uu____9297  ->
             let uu____9298 = cur_goal ()  in
             bind uu____9298
               (fun goal  ->
                  let env =
                    let uu____9306 = FStar_Tactics_Types.goal_env goal  in
                    FStar_TypeChecker_Env.set_expected_typ uu____9306 ty  in
                  let uu____9307 = __tc env tm  in
                  bind uu____9307
                    (fun uu____9326  ->
                       match uu____9326 with
                       | (tm1,typ,guard) ->
                           mlog
                             (fun uu____9340  ->
                                let uu____9341 =
                                  FStar_Syntax_Print.term_to_string tm1  in
                                FStar_Util.print1 "unquote: tm' = %s\n"
                                  uu____9341)
                             (fun uu____9343  ->
                                mlog
                                  (fun uu____9346  ->
                                     let uu____9347 =
                                       FStar_Syntax_Print.term_to_string typ
                                        in
                                     FStar_Util.print1 "unquote: typ = %s\n"
                                       uu____9347)
                                  (fun uu____9350  ->
                                     let uu____9351 =
                                       proc_guard "unquote" env guard
                                         goal.FStar_Tactics_Types.opts
                                        in
                                     bind uu____9351
                                       (fun uu____9355  -> ret tm1))))))
         in
      FStar_All.pipe_left (wrap_err "unquote") uu____9288
  
let (uvar_env :
  env ->
    FStar_Reflection_Data.typ FStar_Pervasives_Native.option ->
      FStar_Syntax_Syntax.term tac)
  =
  fun env  ->
    fun ty  ->
      let uu____9378 =
        match ty with
        | FStar_Pervasives_Native.Some ty1 -> ret ty1
        | FStar_Pervasives_Native.None  ->
            let uu____9384 =
              let uu____9391 =
                let uu____9392 = FStar_Syntax_Util.type_u ()  in
                FStar_All.pipe_left FStar_Pervasives_Native.fst uu____9392
                 in
              new_uvar "uvar_env.2" env uu____9391  in
            bind uu____9384
              (fun uu____9408  ->
                 match uu____9408 with | (typ,uvar_typ) -> ret typ)
         in
      bind uu____9378
        (fun typ  ->
           let uu____9420 = new_uvar "uvar_env" env typ  in
           bind uu____9420
             (fun uu____9434  -> match uu____9434 with | (t,uvar_t) -> ret t))
  
let (unshelve : FStar_Syntax_Syntax.term -> unit tac) =
  fun t  ->
    let uu____9452 =
      bind get
        (fun ps  ->
           let env = ps.FStar_Tactics_Types.main_context  in
           let opts =
             match ps.FStar_Tactics_Types.goals with
             | g::uu____9471 -> g.FStar_Tactics_Types.opts
             | uu____9474 -> FStar_Options.peek ()  in
           let uu____9477 = FStar_Syntax_Util.head_and_args t  in
           match uu____9477 with
           | ({
                FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                  (ctx_uvar,uu____9495);
                FStar_Syntax_Syntax.pos = uu____9496;
                FStar_Syntax_Syntax.vars = uu____9497;_},uu____9498)
               ->
               let env1 =
                 let uu___397_9536 = env  in
                 {
                   FStar_TypeChecker_Env.solver =
                     (uu___397_9536.FStar_TypeChecker_Env.solver);
                   FStar_TypeChecker_Env.range =
                     (uu___397_9536.FStar_TypeChecker_Env.range);
                   FStar_TypeChecker_Env.curmodule =
                     (uu___397_9536.FStar_TypeChecker_Env.curmodule);
                   FStar_TypeChecker_Env.gamma =
                     (ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_gamma);
                   FStar_TypeChecker_Env.gamma_sig =
                     (uu___397_9536.FStar_TypeChecker_Env.gamma_sig);
                   FStar_TypeChecker_Env.gamma_cache =
                     (uu___397_9536.FStar_TypeChecker_Env.gamma_cache);
                   FStar_TypeChecker_Env.modules =
                     (uu___397_9536.FStar_TypeChecker_Env.modules);
                   FStar_TypeChecker_Env.expected_typ =
                     (uu___397_9536.FStar_TypeChecker_Env.expected_typ);
                   FStar_TypeChecker_Env.sigtab =
                     (uu___397_9536.FStar_TypeChecker_Env.sigtab);
                   FStar_TypeChecker_Env.is_pattern =
                     (uu___397_9536.FStar_TypeChecker_Env.is_pattern);
                   FStar_TypeChecker_Env.instantiate_imp =
                     (uu___397_9536.FStar_TypeChecker_Env.instantiate_imp);
                   FStar_TypeChecker_Env.effects =
                     (uu___397_9536.FStar_TypeChecker_Env.effects);
                   FStar_TypeChecker_Env.generalize =
                     (uu___397_9536.FStar_TypeChecker_Env.generalize);
                   FStar_TypeChecker_Env.letrecs =
                     (uu___397_9536.FStar_TypeChecker_Env.letrecs);
                   FStar_TypeChecker_Env.top_level =
                     (uu___397_9536.FStar_TypeChecker_Env.top_level);
                   FStar_TypeChecker_Env.check_uvars =
                     (uu___397_9536.FStar_TypeChecker_Env.check_uvars);
                   FStar_TypeChecker_Env.use_eq =
                     (uu___397_9536.FStar_TypeChecker_Env.use_eq);
                   FStar_TypeChecker_Env.is_iface =
                     (uu___397_9536.FStar_TypeChecker_Env.is_iface);
                   FStar_TypeChecker_Env.admit =
                     (uu___397_9536.FStar_TypeChecker_Env.admit);
                   FStar_TypeChecker_Env.lax =
                     (uu___397_9536.FStar_TypeChecker_Env.lax);
                   FStar_TypeChecker_Env.lax_universes =
                     (uu___397_9536.FStar_TypeChecker_Env.lax_universes);
                   FStar_TypeChecker_Env.failhard =
                     (uu___397_9536.FStar_TypeChecker_Env.failhard);
                   FStar_TypeChecker_Env.nosynth =
                     (uu___397_9536.FStar_TypeChecker_Env.nosynth);
                   FStar_TypeChecker_Env.uvar_subtyping =
                     (uu___397_9536.FStar_TypeChecker_Env.uvar_subtyping);
                   FStar_TypeChecker_Env.tc_term =
                     (uu___397_9536.FStar_TypeChecker_Env.tc_term);
                   FStar_TypeChecker_Env.type_of =
                     (uu___397_9536.FStar_TypeChecker_Env.type_of);
                   FStar_TypeChecker_Env.universe_of =
                     (uu___397_9536.FStar_TypeChecker_Env.universe_of);
                   FStar_TypeChecker_Env.check_type_of =
                     (uu___397_9536.FStar_TypeChecker_Env.check_type_of);
                   FStar_TypeChecker_Env.use_bv_sorts =
                     (uu___397_9536.FStar_TypeChecker_Env.use_bv_sorts);
                   FStar_TypeChecker_Env.qtbl_name_and_index =
                     (uu___397_9536.FStar_TypeChecker_Env.qtbl_name_and_index);
                   FStar_TypeChecker_Env.normalized_eff_names =
                     (uu___397_9536.FStar_TypeChecker_Env.normalized_eff_names);
                   FStar_TypeChecker_Env.proof_ns =
                     (uu___397_9536.FStar_TypeChecker_Env.proof_ns);
                   FStar_TypeChecker_Env.synth_hook =
                     (uu___397_9536.FStar_TypeChecker_Env.synth_hook);
                   FStar_TypeChecker_Env.splice =
                     (uu___397_9536.FStar_TypeChecker_Env.splice);
                   FStar_TypeChecker_Env.is_native_tactic =
                     (uu___397_9536.FStar_TypeChecker_Env.is_native_tactic);
                   FStar_TypeChecker_Env.identifier_info =
                     (uu___397_9536.FStar_TypeChecker_Env.identifier_info);
                   FStar_TypeChecker_Env.tc_hooks =
                     (uu___397_9536.FStar_TypeChecker_Env.tc_hooks);
                   FStar_TypeChecker_Env.dsenv =
                     (uu___397_9536.FStar_TypeChecker_Env.dsenv);
                   FStar_TypeChecker_Env.dep_graph =
                     (uu___397_9536.FStar_TypeChecker_Env.dep_graph)
                 }  in
               let g = FStar_Tactics_Types.mk_goal env1 ctx_uvar opts false
                  in
               let uu____9538 =
                 let uu____9541 = bnorm_goal g  in [uu____9541]  in
               add_goals uu____9538
           | uu____9542 -> fail "not a uvar")
       in
    FStar_All.pipe_left (wrap_err "unshelve") uu____9452
  
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
          (fun uu____9603  ->
             let uu____9604 = FStar_Options.unsafe_tactic_exec ()  in
             if uu____9604
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
        (fun uu____9625  ->
           let uu____9626 =
             FStar_Syntax_Syntax.gen_bv nm FStar_Pervasives_Native.None t  in
           ret uu____9626)
  
let (change : FStar_Reflection_Data.typ -> unit tac) =
  fun ty  ->
    let uu____9636 =
      mlog
        (fun uu____9641  ->
           let uu____9642 = FStar_Syntax_Print.term_to_string ty  in
           FStar_Util.print1 "change: ty = %s\n" uu____9642)
        (fun uu____9645  ->
           let uu____9646 = cur_goal ()  in
           bind uu____9646
             (fun g  ->
                let uu____9652 =
                  let uu____9661 = FStar_Tactics_Types.goal_env g  in
                  __tc uu____9661 ty  in
                bind uu____9652
                  (fun uu____9673  ->
                     match uu____9673 with
                     | (ty1,uu____9683,guard) ->
                         let uu____9685 =
                           let uu____9688 = FStar_Tactics_Types.goal_env g
                              in
                           proc_guard "change" uu____9688 guard
                             g.FStar_Tactics_Types.opts
                            in
                         bind uu____9685
                           (fun uu____9691  ->
                              let uu____9692 =
                                let uu____9695 =
                                  FStar_Tactics_Types.goal_env g  in
                                let uu____9696 =
                                  FStar_Tactics_Types.goal_type g  in
                                do_unify uu____9695 uu____9696 ty1  in
                              bind uu____9692
                                (fun bb  ->
                                   if bb
                                   then
                                     let uu____9702 =
                                       FStar_Tactics_Types.goal_with_type g
                                         ty1
                                        in
                                     replace_cur uu____9702
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
                                        let uu____9708 =
                                          FStar_Tactics_Types.goal_env g  in
                                        let uu____9709 =
                                          FStar_Tactics_Types.goal_type g  in
                                        normalize steps uu____9708 uu____9709
                                         in
                                      let nty =
                                        let uu____9711 =
                                          FStar_Tactics_Types.goal_env g  in
                                        normalize steps uu____9711 ty1  in
                                      let uu____9712 =
                                        let uu____9715 =
                                          FStar_Tactics_Types.goal_env g  in
                                        do_unify uu____9715 ng nty  in
                                      bind uu____9712
                                        (fun b  ->
                                           if b
                                           then
                                             let uu____9721 =
                                               FStar_Tactics_Types.goal_with_type
                                                 g ty1
                                                in
                                             replace_cur uu____9721
                                           else fail "not convertible")))))))
       in
    FStar_All.pipe_left (wrap_err "change") uu____9636
  
let rec last : 'a . 'a Prims.list -> 'a =
  fun l  ->
    match l with
    | [] -> failwith "last: empty list"
    | x::[] -> x
    | uu____9743::xs -> last xs
  
let rec init : 'a . 'a Prims.list -> 'a Prims.list =
  fun l  ->
    match l with
    | [] -> failwith "init: empty list"
    | x::[] -> []
    | x::xs -> let uu____9771 = init xs  in x :: uu____9771
  
let rec (inspect :
  FStar_Syntax_Syntax.term -> FStar_Reflection_Data.term_view tac) =
  fun t  ->
    let uu____9783 =
      let t1 = FStar_Syntax_Util.unascribe t  in
      let t2 = FStar_Syntax_Util.un_uinst t1  in
      match t2.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_meta (t3,uu____9791) -> inspect t3
      | FStar_Syntax_Syntax.Tm_name bv ->
          FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_Var bv)
      | FStar_Syntax_Syntax.Tm_bvar bv ->
          FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_BVar bv)
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_FVar fv)
      | FStar_Syntax_Syntax.Tm_app (hd1,[]) ->
          failwith "empty arguments on Tm_app"
      | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
          let uu____9848 = last args  in
          (match uu____9848 with
           | (a,q) ->
               let q' = FStar_Reflection_Basic.inspect_aqual q  in
               let uu____9870 =
                 let uu____9871 =
                   let uu____9876 =
                     let uu____9877 =
                       let uu____9882 = init args  in
                       FStar_Syntax_Syntax.mk_Tm_app hd1 uu____9882  in
                     uu____9877 FStar_Pervasives_Native.None
                       t2.FStar_Syntax_Syntax.pos
                      in
                   (uu____9876, (a, q'))  in
                 FStar_Reflection_Data.Tv_App uu____9871  in
               FStar_All.pipe_left ret uu____9870)
      | FStar_Syntax_Syntax.Tm_abs ([],uu____9893,uu____9894) ->
          failwith "empty arguments on Tm_abs"
      | FStar_Syntax_Syntax.Tm_abs (bs,t3,k) ->
          let uu____9938 = FStar_Syntax_Subst.open_term bs t3  in
          (match uu____9938 with
           | (bs1,t4) ->
               (match bs1 with
                | [] -> failwith "impossible"
                | b::bs2 ->
                    let uu____9971 =
                      let uu____9972 =
                        let uu____9977 = FStar_Syntax_Util.abs bs2 t4 k  in
                        (b, uu____9977)  in
                      FStar_Reflection_Data.Tv_Abs uu____9972  in
                    FStar_All.pipe_left ret uu____9971))
      | FStar_Syntax_Syntax.Tm_type uu____9980 ->
          FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_Type ())
      | FStar_Syntax_Syntax.Tm_arrow ([],k) ->
          failwith "empty binders on arrow"
      | FStar_Syntax_Syntax.Tm_arrow uu____10000 ->
          let uu____10013 = FStar_Syntax_Util.arrow_one t2  in
          (match uu____10013 with
           | FStar_Pervasives_Native.Some (b,c) ->
               FStar_All.pipe_left ret
                 (FStar_Reflection_Data.Tv_Arrow (b, c))
           | FStar_Pervasives_Native.None  -> failwith "impossible")
      | FStar_Syntax_Syntax.Tm_refine (bv,t3) ->
          let b = FStar_Syntax_Syntax.mk_binder bv  in
          let uu____10043 = FStar_Syntax_Subst.open_term [b] t3  in
          (match uu____10043 with
           | (b',t4) ->
               let b1 =
                 match b' with
                 | b'1::[] -> b'1
                 | uu____10082 -> failwith "impossible"  in
               FStar_All.pipe_left ret
                 (FStar_Reflection_Data.Tv_Refine
                    ((FStar_Pervasives_Native.fst b1), t4)))
      | FStar_Syntax_Syntax.Tm_constant c ->
          let uu____10090 =
            let uu____10091 = FStar_Reflection_Basic.inspect_const c  in
            FStar_Reflection_Data.Tv_Const uu____10091  in
          FStar_All.pipe_left ret uu____10090
      | FStar_Syntax_Syntax.Tm_uvar (ctx_u,s) ->
          let uu____10112 =
            let uu____10113 =
              let uu____10118 =
                let uu____10119 =
                  FStar_Syntax_Unionfind.uvar_id
                    ctx_u.FStar_Syntax_Syntax.ctx_uvar_head
                   in
                FStar_BigInt.of_int_fs uu____10119  in
              (uu____10118, (ctx_u, s))  in
            FStar_Reflection_Data.Tv_Uvar uu____10113  in
          FStar_All.pipe_left ret uu____10112
      | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),t21) ->
          if lb.FStar_Syntax_Syntax.lbunivs <> []
          then FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown
          else
            (match lb.FStar_Syntax_Syntax.lbname with
             | FStar_Util.Inr uu____10153 ->
                 FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown
             | FStar_Util.Inl bv ->
                 let b = FStar_Syntax_Syntax.mk_binder bv  in
                 let uu____10158 = FStar_Syntax_Subst.open_term [b] t21  in
                 (match uu____10158 with
                  | (bs,t22) ->
                      let b1 =
                        match bs with
                        | b1::[] -> b1
                        | uu____10197 ->
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
             | FStar_Util.Inr uu____10227 ->
                 FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown
             | FStar_Util.Inl bv ->
                 let uu____10231 = FStar_Syntax_Subst.open_let_rec [lb] t21
                    in
                 (match uu____10231 with
                  | (lbs,t22) ->
                      (match lbs with
                       | lb1::[] ->
                           (match lb1.FStar_Syntax_Syntax.lbname with
                            | FStar_Util.Inr uu____10251 ->
                                ret FStar_Reflection_Data.Tv_Unknown
                            | FStar_Util.Inl bv1 ->
                                FStar_All.pipe_left ret
                                  (FStar_Reflection_Data.Tv_Let
                                     (true, bv1,
                                       (lb1.FStar_Syntax_Syntax.lbdef), t22)))
                       | uu____10255 ->
                           failwith
                             "impossible: open_term returned different amount of binders")))
      | FStar_Syntax_Syntax.Tm_match (t3,brs) ->
          let rec inspect_pat p =
            match p.FStar_Syntax_Syntax.v with
            | FStar_Syntax_Syntax.Pat_constant c ->
                let uu____10309 = FStar_Reflection_Basic.inspect_const c  in
                FStar_Reflection_Data.Pat_Constant uu____10309
            | FStar_Syntax_Syntax.Pat_cons (fv,ps) ->
                let uu____10328 =
                  let uu____10335 =
                    FStar_List.map
                      (fun uu____10347  ->
                         match uu____10347 with
                         | (p1,uu____10355) -> inspect_pat p1) ps
                     in
                  (fv, uu____10335)  in
                FStar_Reflection_Data.Pat_Cons uu____10328
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
              (fun uu___338_10449  ->
                 match uu___338_10449 with
                 | (pat,uu____10471,t4) ->
                     let uu____10489 = inspect_pat pat  in (uu____10489, t4))
              brs1
             in
          FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_Match (t3, brs2))
      | FStar_Syntax_Syntax.Tm_unknown  ->
          FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown
      | uu____10498 ->
          ((let uu____10500 =
              let uu____10505 =
                let uu____10506 = FStar_Syntax_Print.tag_of_term t2  in
                let uu____10507 = FStar_Syntax_Print.term_to_string t2  in
                FStar_Util.format2
                  "inspect: outside of expected syntax (%s, %s)\n"
                  uu____10506 uu____10507
                 in
              (FStar_Errors.Warning_CantInspect, uu____10505)  in
            FStar_Errors.log_issue t2.FStar_Syntax_Syntax.pos uu____10500);
           FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown)
       in
    wrap_err "inspect" uu____9783
  
let (pack : FStar_Reflection_Data.term_view -> FStar_Syntax_Syntax.term tac)
  =
  fun tv  ->
    match tv with
    | FStar_Reflection_Data.Tv_Var bv ->
        let uu____10520 = FStar_Syntax_Syntax.bv_to_name bv  in
        FStar_All.pipe_left ret uu____10520
    | FStar_Reflection_Data.Tv_BVar bv ->
        let uu____10524 = FStar_Syntax_Syntax.bv_to_tm bv  in
        FStar_All.pipe_left ret uu____10524
    | FStar_Reflection_Data.Tv_FVar fv ->
        let uu____10528 = FStar_Syntax_Syntax.fv_to_tm fv  in
        FStar_All.pipe_left ret uu____10528
    | FStar_Reflection_Data.Tv_App (l,(r,q)) ->
        let q' = FStar_Reflection_Basic.pack_aqual q  in
        let uu____10535 = FStar_Syntax_Util.mk_app l [(r, q')]  in
        FStar_All.pipe_left ret uu____10535
    | FStar_Reflection_Data.Tv_Abs (b,t) ->
        let uu____10554 =
          FStar_Syntax_Util.abs [b] t FStar_Pervasives_Native.None  in
        FStar_All.pipe_left ret uu____10554
    | FStar_Reflection_Data.Tv_Arrow (b,c) ->
        let uu____10567 = FStar_Syntax_Util.arrow [b] c  in
        FStar_All.pipe_left ret uu____10567
    | FStar_Reflection_Data.Tv_Type () ->
        FStar_All.pipe_left ret FStar_Syntax_Util.ktype
    | FStar_Reflection_Data.Tv_Refine (bv,t) ->
        let uu____10582 = FStar_Syntax_Util.refine bv t  in
        FStar_All.pipe_left ret uu____10582
    | FStar_Reflection_Data.Tv_Const c ->
        let uu____10586 =
          let uu____10587 =
            let uu____10594 =
              let uu____10595 = FStar_Reflection_Basic.pack_const c  in
              FStar_Syntax_Syntax.Tm_constant uu____10595  in
            FStar_Syntax_Syntax.mk uu____10594  in
          uu____10587 FStar_Pervasives_Native.None FStar_Range.dummyRange  in
        FStar_All.pipe_left ret uu____10586
    | FStar_Reflection_Data.Tv_Uvar (_u,ctx_u_s) ->
        let uu____10603 =
          FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_uvar ctx_u_s)
            FStar_Pervasives_Native.None FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____10603
    | FStar_Reflection_Data.Tv_Let (false ,bv,t1,t2) ->
        let lb =
          FStar_Syntax_Util.mk_letbinding (FStar_Util.Inl bv) []
            bv.FStar_Syntax_Syntax.sort FStar_Parser_Const.effect_Tot_lid t1
            [] FStar_Range.dummyRange
           in
        let uu____10612 =
          let uu____10613 =
            let uu____10620 =
              let uu____10621 =
                let uu____10634 =
                  let uu____10637 =
                    let uu____10638 = FStar_Syntax_Syntax.mk_binder bv  in
                    [uu____10638]  in
                  FStar_Syntax_Subst.close uu____10637 t2  in
                ((false, [lb]), uu____10634)  in
              FStar_Syntax_Syntax.Tm_let uu____10621  in
            FStar_Syntax_Syntax.mk uu____10620  in
          uu____10613 FStar_Pervasives_Native.None FStar_Range.dummyRange  in
        FStar_All.pipe_left ret uu____10612
    | FStar_Reflection_Data.Tv_Let (true ,bv,t1,t2) ->
        let lb =
          FStar_Syntax_Util.mk_letbinding (FStar_Util.Inl bv) []
            bv.FStar_Syntax_Syntax.sort FStar_Parser_Const.effect_Tot_lid t1
            [] FStar_Range.dummyRange
           in
        let uu____10672 = FStar_Syntax_Subst.close_let_rec [lb] t2  in
        (match uu____10672 with
         | (lbs,body) ->
             let uu____10687 =
               FStar_Syntax_Syntax.mk
                 (FStar_Syntax_Syntax.Tm_let ((true, lbs), body))
                 FStar_Pervasives_Native.None FStar_Range.dummyRange
                in
             FStar_All.pipe_left ret uu____10687)
    | FStar_Reflection_Data.Tv_Match (t,brs) ->
        let wrap v1 =
          {
            FStar_Syntax_Syntax.v = v1;
            FStar_Syntax_Syntax.p = FStar_Range.dummyRange
          }  in
        let rec pack_pat p =
          match p with
          | FStar_Reflection_Data.Pat_Constant c ->
              let uu____10721 =
                let uu____10722 = FStar_Reflection_Basic.pack_const c  in
                FStar_Syntax_Syntax.Pat_constant uu____10722  in
              FStar_All.pipe_left wrap uu____10721
          | FStar_Reflection_Data.Pat_Cons (fv,ps) ->
              let uu____10729 =
                let uu____10730 =
                  let uu____10743 =
                    FStar_List.map
                      (fun p1  ->
                         let uu____10759 = pack_pat p1  in
                         (uu____10759, false)) ps
                     in
                  (fv, uu____10743)  in
                FStar_Syntax_Syntax.Pat_cons uu____10730  in
              FStar_All.pipe_left wrap uu____10729
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
            (fun uu___339_10805  ->
               match uu___339_10805 with
               | (pat,t1) ->
                   let uu____10822 = pack_pat pat  in
                   (uu____10822, FStar_Pervasives_Native.None, t1)) brs
           in
        let brs2 = FStar_List.map FStar_Syntax_Subst.close_branch brs1  in
        let uu____10870 =
          FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_match (t, brs2))
            FStar_Pervasives_Native.None FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____10870
    | FStar_Reflection_Data.Tv_AscribedT (e,t,tacopt) ->
        let uu____10898 =
          FStar_Syntax_Syntax.mk
            (FStar_Syntax_Syntax.Tm_ascribed
               (e, ((FStar_Util.Inl t), tacopt),
                 FStar_Pervasives_Native.None)) FStar_Pervasives_Native.None
            FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____10898
    | FStar_Reflection_Data.Tv_AscribedC (e,c,tacopt) ->
        let uu____10944 =
          FStar_Syntax_Syntax.mk
            (FStar_Syntax_Syntax.Tm_ascribed
               (e, ((FStar_Util.Inr c), tacopt),
                 FStar_Pervasives_Native.None)) FStar_Pervasives_Native.None
            FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____10944
    | FStar_Reflection_Data.Tv_Unknown  ->
        let uu____10983 =
          FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown
            FStar_Pervasives_Native.None FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____10983
  
let (goal_of_goal_ty :
  env ->
    FStar_Reflection_Data.typ ->
      (FStar_Tactics_Types.goal,FStar_TypeChecker_Env.guard_t)
        FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun typ  ->
      let uu____11004 =
        FStar_TypeChecker_Util.new_implicit_var "proofstate_of_goal_ty"
          typ.FStar_Syntax_Syntax.pos env typ
         in
      match uu____11004 with
      | (u,ctx_uvars,g_u) ->
          let uu____11036 = FStar_List.hd ctx_uvars  in
          (match uu____11036 with
           | (ctx_uvar,uu____11050) ->
               let g =
                 let uu____11052 = FStar_Options.peek ()  in
                 FStar_Tactics_Types.mk_goal env ctx_uvar uu____11052 false
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
        let uu____11072 = goal_of_goal_ty env typ  in
        match uu____11072 with
        | (g,g_u) ->
            let ps =
              let uu____11084 =
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
                FStar_Tactics_Types.tac_verb_dbg = uu____11084
              }  in
            let uu____11089 = FStar_Tactics_Types.goal_witness g  in
            (ps, uu____11089)
  