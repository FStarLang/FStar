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
                 let uu___346_1020 = ps  in
                 {
                   FStar_Tactics_Types.main_context =
                     (uu___346_1020.FStar_Tactics_Types.main_context);
                   FStar_Tactics_Types.main_goal =
                     (uu___346_1020.FStar_Tactics_Types.main_goal);
                   FStar_Tactics_Types.all_implicits =
                     (uu___346_1020.FStar_Tactics_Types.all_implicits);
                   FStar_Tactics_Types.goals =
                     (uu___346_1020.FStar_Tactics_Types.goals);
                   FStar_Tactics_Types.smt_goals =
                     (uu___346_1020.FStar_Tactics_Types.smt_goals);
                   FStar_Tactics_Types.depth =
                     (uu___346_1020.FStar_Tactics_Types.depth);
                   FStar_Tactics_Types.__dump =
                     (uu___346_1020.FStar_Tactics_Types.__dump);
                   FStar_Tactics_Types.psc =
                     (uu___346_1020.FStar_Tactics_Types.psc);
                   FStar_Tactics_Types.entry_range =
                     (uu___346_1020.FStar_Tactics_Types.entry_range);
                   FStar_Tactics_Types.guard_policy =
                     (uu___346_1020.FStar_Tactics_Types.guard_policy);
                   FStar_Tactics_Types.freshness =
                     (q.FStar_Tactics_Types.freshness);
                   FStar_Tactics_Types.tac_verb_dbg =
                     (uu___346_1020.FStar_Tactics_Types.tac_verb_dbg)
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
         let uu___351_1308 = ps  in
         let uu____1309 =
           FStar_List.filter
             (fun g  ->
                let uu____1315 = check_goal_solved g  in
                FStar_Option.isNone uu____1315) ps.FStar_Tactics_Types.goals
            in
         {
           FStar_Tactics_Types.main_context =
             (uu___351_1308.FStar_Tactics_Types.main_context);
           FStar_Tactics_Types.main_goal =
             (uu___351_1308.FStar_Tactics_Types.main_goal);
           FStar_Tactics_Types.all_implicits =
             (uu___351_1308.FStar_Tactics_Types.all_implicits);
           FStar_Tactics_Types.goals = uu____1309;
           FStar_Tactics_Types.smt_goals =
             (uu___351_1308.FStar_Tactics_Types.smt_goals);
           FStar_Tactics_Types.depth =
             (uu___351_1308.FStar_Tactics_Types.depth);
           FStar_Tactics_Types.__dump =
             (uu___351_1308.FStar_Tactics_Types.__dump);
           FStar_Tactics_Types.psc = (uu___351_1308.FStar_Tactics_Types.psc);
           FStar_Tactics_Types.entry_range =
             (uu___351_1308.FStar_Tactics_Types.entry_range);
           FStar_Tactics_Types.guard_policy =
             (uu___351_1308.FStar_Tactics_Types.guard_policy);
           FStar_Tactics_Types.freshness =
             (uu___351_1308.FStar_Tactics_Types.freshness);
           FStar_Tactics_Types.tac_verb_dbg =
             (uu___351_1308.FStar_Tactics_Types.tac_verb_dbg)
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
         let uu___352_1363 = p  in
         let uu____1364 = FStar_List.tl p.FStar_Tactics_Types.goals  in
         {
           FStar_Tactics_Types.main_context =
             (uu___352_1363.FStar_Tactics_Types.main_context);
           FStar_Tactics_Types.main_goal =
             (uu___352_1363.FStar_Tactics_Types.main_goal);
           FStar_Tactics_Types.all_implicits =
             (uu___352_1363.FStar_Tactics_Types.all_implicits);
           FStar_Tactics_Types.goals = uu____1364;
           FStar_Tactics_Types.smt_goals =
             (uu___352_1363.FStar_Tactics_Types.smt_goals);
           FStar_Tactics_Types.depth =
             (uu___352_1363.FStar_Tactics_Types.depth);
           FStar_Tactics_Types.__dump =
             (uu___352_1363.FStar_Tactics_Types.__dump);
           FStar_Tactics_Types.psc = (uu___352_1363.FStar_Tactics_Types.psc);
           FStar_Tactics_Types.entry_range =
             (uu___352_1363.FStar_Tactics_Types.entry_range);
           FStar_Tactics_Types.guard_policy =
             (uu___352_1363.FStar_Tactics_Types.guard_policy);
           FStar_Tactics_Types.freshness =
             (uu___352_1363.FStar_Tactics_Types.freshness);
           FStar_Tactics_Types.tac_verb_dbg =
             (uu___352_1363.FStar_Tactics_Types.tac_verb_dbg)
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
         (let uu___353_1454 = p  in
          {
            FStar_Tactics_Types.main_context =
              (uu___353_1454.FStar_Tactics_Types.main_context);
            FStar_Tactics_Types.main_goal =
              (uu___353_1454.FStar_Tactics_Types.main_goal);
            FStar_Tactics_Types.all_implicits =
              (uu___353_1454.FStar_Tactics_Types.all_implicits);
            FStar_Tactics_Types.goals = [];
            FStar_Tactics_Types.smt_goals =
              (uu___353_1454.FStar_Tactics_Types.smt_goals);
            FStar_Tactics_Types.depth =
              (uu___353_1454.FStar_Tactics_Types.depth);
            FStar_Tactics_Types.__dump =
              (uu___353_1454.FStar_Tactics_Types.__dump);
            FStar_Tactics_Types.psc = (uu___353_1454.FStar_Tactics_Types.psc);
            FStar_Tactics_Types.entry_range =
              (uu___353_1454.FStar_Tactics_Types.entry_range);
            FStar_Tactics_Types.guard_policy =
              (uu___353_1454.FStar_Tactics_Types.guard_policy);
            FStar_Tactics_Types.freshness =
              (uu___353_1454.FStar_Tactics_Types.freshness);
            FStar_Tactics_Types.tac_verb_dbg =
              (uu___353_1454.FStar_Tactics_Types.tac_verb_dbg)
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
           (let uu___354_1621 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___354_1621.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___354_1621.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___354_1621.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (FStar_List.append gs p.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (uu___354_1621.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___354_1621.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___354_1621.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___354_1621.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___354_1621.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___354_1621.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___354_1621.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___354_1621.FStar_Tactics_Types.tac_verb_dbg)
            }))
  
let (add_smt_goals : FStar_Tactics_Types.goal Prims.list -> unit tac) =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___355_1641 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___355_1641.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___355_1641.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___355_1641.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___355_1641.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (FStar_List.append gs p.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___355_1641.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___355_1641.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___355_1641.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___355_1641.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___355_1641.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___355_1641.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___355_1641.FStar_Tactics_Types.tac_verb_dbg)
            }))
  
let (push_goals : FStar_Tactics_Types.goal Prims.list -> unit tac) =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___356_1661 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___356_1661.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___356_1661.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___356_1661.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (FStar_List.append p.FStar_Tactics_Types.goals gs);
              FStar_Tactics_Types.smt_goals =
                (uu___356_1661.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___356_1661.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___356_1661.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___356_1661.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___356_1661.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___356_1661.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___356_1661.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___356_1661.FStar_Tactics_Types.tac_verb_dbg)
            }))
  
let (push_smt_goals : FStar_Tactics_Types.goal Prims.list -> unit tac) =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___357_1681 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___357_1681.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___357_1681.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___357_1681.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___357_1681.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (FStar_List.append p.FStar_Tactics_Types.smt_goals gs);
              FStar_Tactics_Types.depth =
                (uu___357_1681.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___357_1681.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___357_1681.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___357_1681.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___357_1681.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___357_1681.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___357_1681.FStar_Tactics_Types.tac_verb_dbg)
            }))
  
let (replace_cur : FStar_Tactics_Types.goal -> unit tac) =
  fun g  -> bind __dismiss (fun uu____1692  -> add_goals [g]) 
let (add_implicits : implicits -> unit tac) =
  fun i  ->
    bind get
      (fun p  ->
         set
           (let uu___358_1706 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___358_1706.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___358_1706.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (FStar_List.append i p.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___358_1706.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (uu___358_1706.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___358_1706.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___358_1706.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___358_1706.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___358_1706.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___358_1706.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___358_1706.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___358_1706.FStar_Tactics_Types.tac_verb_dbg)
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
           let uu___359_1936 = ps  in
           {
             FStar_Tactics_Types.main_context =
               (uu___359_1936.FStar_Tactics_Types.main_context);
             FStar_Tactics_Types.main_goal =
               (uu___359_1936.FStar_Tactics_Types.main_goal);
             FStar_Tactics_Types.all_implicits =
               (uu___359_1936.FStar_Tactics_Types.all_implicits);
             FStar_Tactics_Types.goals =
               (uu___359_1936.FStar_Tactics_Types.goals);
             FStar_Tactics_Types.smt_goals =
               (uu___359_1936.FStar_Tactics_Types.smt_goals);
             FStar_Tactics_Types.depth =
               (uu___359_1936.FStar_Tactics_Types.depth);
             FStar_Tactics_Types.__dump =
               (uu___359_1936.FStar_Tactics_Types.__dump);
             FStar_Tactics_Types.psc =
               (uu___359_1936.FStar_Tactics_Types.psc);
             FStar_Tactics_Types.entry_range =
               (uu___359_1936.FStar_Tactics_Types.entry_range);
             FStar_Tactics_Types.guard_policy =
               (uu___359_1936.FStar_Tactics_Types.guard_policy);
             FStar_Tactics_Types.freshness = (n1 + (Prims.parse_int "1"));
             FStar_Tactics_Types.tac_verb_dbg =
               (uu___359_1936.FStar_Tactics_Types.tac_verb_dbg)
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
                  let uu___360_2101 = e  in
                  {
                    FStar_TypeChecker_Env.solver =
                      (uu___360_2101.FStar_TypeChecker_Env.solver);
                    FStar_TypeChecker_Env.range =
                      (uu___360_2101.FStar_TypeChecker_Env.range);
                    FStar_TypeChecker_Env.curmodule =
                      (uu___360_2101.FStar_TypeChecker_Env.curmodule);
                    FStar_TypeChecker_Env.gamma =
                      (uu___360_2101.FStar_TypeChecker_Env.gamma);
                    FStar_TypeChecker_Env.gamma_sig =
                      (uu___360_2101.FStar_TypeChecker_Env.gamma_sig);
                    FStar_TypeChecker_Env.gamma_cache =
                      (uu___360_2101.FStar_TypeChecker_Env.gamma_cache);
                    FStar_TypeChecker_Env.modules =
                      (uu___360_2101.FStar_TypeChecker_Env.modules);
                    FStar_TypeChecker_Env.expected_typ =
                      (uu___360_2101.FStar_TypeChecker_Env.expected_typ);
                    FStar_TypeChecker_Env.sigtab =
                      (uu___360_2101.FStar_TypeChecker_Env.sigtab);
                    FStar_TypeChecker_Env.is_pattern =
                      (uu___360_2101.FStar_TypeChecker_Env.is_pattern);
                    FStar_TypeChecker_Env.instantiate_imp =
                      (uu___360_2101.FStar_TypeChecker_Env.instantiate_imp);
                    FStar_TypeChecker_Env.effects =
                      (uu___360_2101.FStar_TypeChecker_Env.effects);
                    FStar_TypeChecker_Env.generalize =
                      (uu___360_2101.FStar_TypeChecker_Env.generalize);
                    FStar_TypeChecker_Env.letrecs =
                      (uu___360_2101.FStar_TypeChecker_Env.letrecs);
                    FStar_TypeChecker_Env.top_level =
                      (uu___360_2101.FStar_TypeChecker_Env.top_level);
                    FStar_TypeChecker_Env.check_uvars =
                      (uu___360_2101.FStar_TypeChecker_Env.check_uvars);
                    FStar_TypeChecker_Env.use_eq =
                      (uu___360_2101.FStar_TypeChecker_Env.use_eq);
                    FStar_TypeChecker_Env.is_iface =
                      (uu___360_2101.FStar_TypeChecker_Env.is_iface);
                    FStar_TypeChecker_Env.admit =
                      (uu___360_2101.FStar_TypeChecker_Env.admit);
                    FStar_TypeChecker_Env.lax =
                      (uu___360_2101.FStar_TypeChecker_Env.lax);
                    FStar_TypeChecker_Env.lax_universes =
                      (uu___360_2101.FStar_TypeChecker_Env.lax_universes);
                    FStar_TypeChecker_Env.failhard =
                      (uu___360_2101.FStar_TypeChecker_Env.failhard);
                    FStar_TypeChecker_Env.nosynth =
                      (uu___360_2101.FStar_TypeChecker_Env.nosynth);
                    FStar_TypeChecker_Env.uvar_subtyping = false;
                    FStar_TypeChecker_Env.tc_term =
                      (uu___360_2101.FStar_TypeChecker_Env.tc_term);
                    FStar_TypeChecker_Env.type_of =
                      (uu___360_2101.FStar_TypeChecker_Env.type_of);
                    FStar_TypeChecker_Env.universe_of =
                      (uu___360_2101.FStar_TypeChecker_Env.universe_of);
                    FStar_TypeChecker_Env.check_type_of =
                      (uu___360_2101.FStar_TypeChecker_Env.check_type_of);
                    FStar_TypeChecker_Env.use_bv_sorts =
                      (uu___360_2101.FStar_TypeChecker_Env.use_bv_sorts);
                    FStar_TypeChecker_Env.qtbl_name_and_index =
                      (uu___360_2101.FStar_TypeChecker_Env.qtbl_name_and_index);
                    FStar_TypeChecker_Env.normalized_eff_names =
                      (uu___360_2101.FStar_TypeChecker_Env.normalized_eff_names);
                    FStar_TypeChecker_Env.proof_ns =
                      (uu___360_2101.FStar_TypeChecker_Env.proof_ns);
                    FStar_TypeChecker_Env.synth_hook =
                      (uu___360_2101.FStar_TypeChecker_Env.synth_hook);
                    FStar_TypeChecker_Env.splice =
                      (uu___360_2101.FStar_TypeChecker_Env.splice);
                    FStar_TypeChecker_Env.is_native_tactic =
                      (uu___360_2101.FStar_TypeChecker_Env.is_native_tactic);
                    FStar_TypeChecker_Env.identifier_info =
                      (uu___360_2101.FStar_TypeChecker_Env.identifier_info);
                    FStar_TypeChecker_Env.tc_hooks =
                      (uu___360_2101.FStar_TypeChecker_Env.tc_hooks);
                    FStar_TypeChecker_Env.dsenv =
                      (uu___360_2101.FStar_TypeChecker_Env.dsenv);
                    FStar_TypeChecker_Env.dep_graph =
                      (uu___360_2101.FStar_TypeChecker_Env.dep_graph)
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
           (let uu___363_2209 = ps  in
            {
              FStar_Tactics_Types.main_context =
                (uu___363_2209.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___363_2209.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___363_2209.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___363_2209.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (uu___363_2209.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___363_2209.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___363_2209.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___363_2209.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___363_2209.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy = pol;
              FStar_Tactics_Types.freshness =
                (uu___363_2209.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___363_2209.FStar_Tactics_Types.tac_verb_dbg)
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
  
let (getopts : FStar_Options.optionstate tac) =
  let uu____2254 = let uu____2259 = cur_goal ()  in trytac uu____2259  in
  bind uu____2254
    (fun uu___336_2266  ->
       match uu___336_2266 with
       | FStar_Pervasives_Native.Some g -> ret g.FStar_Tactics_Types.opts
       | FStar_Pervasives_Native.None  ->
           let uu____2272 = FStar_Options.peek ()  in ret uu____2272)
  
let (proc_guard :
  Prims.string -> env -> FStar_TypeChecker_Env.guard_t -> unit tac) =
  fun reason  ->
    fun e  ->
      fun g  ->
        bind getopts
          (fun opts  ->
             let uu____2295 =
               let uu____2296 = FStar_TypeChecker_Rel.simplify_guard e g  in
               uu____2296.FStar_TypeChecker_Env.guard_f  in
             match uu____2295 with
             | FStar_TypeChecker_Common.Trivial  -> ret ()
             | FStar_TypeChecker_Common.NonTrivial f ->
                 let uu____2300 = istrivial e f  in
                 if uu____2300
                 then ret ()
                 else
                   bind get
                     (fun ps  ->
                        match ps.FStar_Tactics_Types.guard_policy with
                        | FStar_Tactics_Types.Drop  -> ret ()
                        | FStar_Tactics_Types.Goal  ->
                            let uu____2308 =
                              mk_irrelevant_goal reason e f opts  in
                            bind uu____2308
                              (fun goal  ->
                                 let goal1 =
                                   let uu___364_2315 = goal  in
                                   {
                                     FStar_Tactics_Types.goal_main_env =
                                       (uu___364_2315.FStar_Tactics_Types.goal_main_env);
                                     FStar_Tactics_Types.goal_ctx_uvar =
                                       (uu___364_2315.FStar_Tactics_Types.goal_ctx_uvar);
                                     FStar_Tactics_Types.opts =
                                       (uu___364_2315.FStar_Tactics_Types.opts);
                                     FStar_Tactics_Types.is_guard = true
                                   }  in
                                 push_goals [goal1])
                        | FStar_Tactics_Types.SMT  ->
                            let uu____2316 =
                              mk_irrelevant_goal reason e f opts  in
                            bind uu____2316
                              (fun goal  ->
                                 let goal1 =
                                   let uu___365_2323 = goal  in
                                   {
                                     FStar_Tactics_Types.goal_main_env =
                                       (uu___365_2323.FStar_Tactics_Types.goal_main_env);
                                     FStar_Tactics_Types.goal_ctx_uvar =
                                       (uu___365_2323.FStar_Tactics_Types.goal_ctx_uvar);
                                     FStar_Tactics_Types.opts =
                                       (uu___365_2323.FStar_Tactics_Types.opts);
                                     FStar_Tactics_Types.is_guard = true
                                   }  in
                                 push_smt_goals [goal1])
                        | FStar_Tactics_Types.Force  ->
                            (try
                               let uu____2331 =
                                 let uu____2332 =
                                   let uu____2333 =
                                     FStar_TypeChecker_Rel.discharge_guard_no_smt
                                       e g
                                      in
                                   FStar_All.pipe_left
                                     FStar_TypeChecker_Rel.is_trivial
                                     uu____2333
                                    in
                                 Prims.op_Negation uu____2332  in
                               if uu____2331
                               then
                                 mlog
                                   (fun uu____2338  ->
                                      let uu____2339 =
                                        FStar_TypeChecker_Rel.guard_to_string
                                          e g
                                         in
                                      FStar_Util.print1 "guard = %s\n"
                                        uu____2339)
                                   (fun uu____2341  ->
                                      fail1 "Forcing the guard failed %s)"
                                        reason)
                               else ret ()
                             with
                             | uu____2348 ->
                                 mlog
                                   (fun uu____2351  ->
                                      let uu____2352 =
                                        FStar_TypeChecker_Rel.guard_to_string
                                          e g
                                         in
                                      FStar_Util.print1 "guard = %s\n"
                                        uu____2352)
                                   (fun uu____2354  ->
                                      fail1 "Forcing the guard failed (%s)"
                                        reason))))
  
let (tc : FStar_Syntax_Syntax.term -> FStar_Reflection_Data.typ tac) =
  fun t  ->
    let uu____2364 =
      let uu____2367 = cur_goal ()  in
      bind uu____2367
        (fun goal  ->
           let uu____2373 =
             let uu____2382 = FStar_Tactics_Types.goal_env goal  in
             __tc uu____2382 t  in
           bind uu____2373
             (fun uu____2394  ->
                match uu____2394 with
                | (t1,typ,guard) ->
                    let uu____2406 =
                      let uu____2409 = FStar_Tactics_Types.goal_env goal  in
                      proc_guard "tc" uu____2409 guard  in
                    bind uu____2406 (fun uu____2411  -> ret typ)))
       in
    FStar_All.pipe_left (wrap_err "tc") uu____2364
  
let (add_irrelevant_goal :
  Prims.string ->
    env -> FStar_Reflection_Data.typ -> FStar_Options.optionstate -> unit tac)
  =
  fun reason  ->
    fun env  ->
      fun phi  ->
        fun opts  ->
          let uu____2440 = mk_irrelevant_goal reason env phi opts  in
          bind uu____2440 (fun goal  -> add_goals [goal])
  
let (trivial : unit -> unit tac) =
  fun uu____2451  ->
    let uu____2454 = cur_goal ()  in
    bind uu____2454
      (fun goal  ->
         let uu____2460 =
           let uu____2461 = FStar_Tactics_Types.goal_env goal  in
           let uu____2462 = FStar_Tactics_Types.goal_type goal  in
           istrivial uu____2461 uu____2462  in
         if uu____2460
         then solve' goal FStar_Syntax_Util.exp_unit
         else
           (let uu____2466 =
              let uu____2467 = FStar_Tactics_Types.goal_env goal  in
              let uu____2468 = FStar_Tactics_Types.goal_type goal  in
              tts uu____2467 uu____2468  in
            fail1 "Not a trivial goal: %s" uu____2466))
  
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
          let uu____2497 =
            let uu____2498 = FStar_TypeChecker_Rel.simplify_guard e g  in
            uu____2498.FStar_TypeChecker_Env.guard_f  in
          match uu____2497 with
          | FStar_TypeChecker_Common.Trivial  ->
              ret FStar_Pervasives_Native.None
          | FStar_TypeChecker_Common.NonTrivial f ->
              let uu____2506 = istrivial e f  in
              if uu____2506
              then ret FStar_Pervasives_Native.None
              else
                (let uu____2514 = mk_irrelevant_goal reason e f opts  in
                 bind uu____2514
                   (fun goal  ->
                      ret
                        (FStar_Pervasives_Native.Some
                           (let uu___368_2524 = goal  in
                            {
                              FStar_Tactics_Types.goal_main_env =
                                (uu___368_2524.FStar_Tactics_Types.goal_main_env);
                              FStar_Tactics_Types.goal_ctx_uvar =
                                (uu___368_2524.FStar_Tactics_Types.goal_ctx_uvar);
                              FStar_Tactics_Types.opts =
                                (uu___368_2524.FStar_Tactics_Types.opts);
                              FStar_Tactics_Types.is_guard = true
                            }))))
  
let (smt : unit -> unit tac) =
  fun uu____2531  ->
    let uu____2534 = cur_goal ()  in
    bind uu____2534
      (fun g  ->
         let uu____2540 = is_irrelevant g  in
         if uu____2540
         then bind __dismiss (fun uu____2544  -> add_smt_goals [g])
         else
           (let uu____2546 =
              let uu____2547 = FStar_Tactics_Types.goal_env g  in
              let uu____2548 = FStar_Tactics_Types.goal_type g  in
              tts uu____2547 uu____2548  in
            fail1 "goal is not irrelevant: cannot dispatch to smt (%s)"
              uu____2546))
  
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
             let uu____2597 =
               try
                 let uu____2631 =
                   let uu____2640 = FStar_BigInt.to_int_fs n1  in
                   FStar_List.splitAt uu____2640 p.FStar_Tactics_Types.goals
                    in
                 ret uu____2631
               with | uu____2662 -> fail "divide: not enough goals"  in
             bind uu____2597
               (fun uu____2689  ->
                  match uu____2689 with
                  | (lgs,rgs) ->
                      let lp =
                        let uu___369_2715 = p  in
                        {
                          FStar_Tactics_Types.main_context =
                            (uu___369_2715.FStar_Tactics_Types.main_context);
                          FStar_Tactics_Types.main_goal =
                            (uu___369_2715.FStar_Tactics_Types.main_goal);
                          FStar_Tactics_Types.all_implicits =
                            (uu___369_2715.FStar_Tactics_Types.all_implicits);
                          FStar_Tactics_Types.goals = lgs;
                          FStar_Tactics_Types.smt_goals = [];
                          FStar_Tactics_Types.depth =
                            (uu___369_2715.FStar_Tactics_Types.depth);
                          FStar_Tactics_Types.__dump =
                            (uu___369_2715.FStar_Tactics_Types.__dump);
                          FStar_Tactics_Types.psc =
                            (uu___369_2715.FStar_Tactics_Types.psc);
                          FStar_Tactics_Types.entry_range =
                            (uu___369_2715.FStar_Tactics_Types.entry_range);
                          FStar_Tactics_Types.guard_policy =
                            (uu___369_2715.FStar_Tactics_Types.guard_policy);
                          FStar_Tactics_Types.freshness =
                            (uu___369_2715.FStar_Tactics_Types.freshness);
                          FStar_Tactics_Types.tac_verb_dbg =
                            (uu___369_2715.FStar_Tactics_Types.tac_verb_dbg)
                        }  in
                      let rp =
                        let uu___370_2717 = p  in
                        {
                          FStar_Tactics_Types.main_context =
                            (uu___370_2717.FStar_Tactics_Types.main_context);
                          FStar_Tactics_Types.main_goal =
                            (uu___370_2717.FStar_Tactics_Types.main_goal);
                          FStar_Tactics_Types.all_implicits =
                            (uu___370_2717.FStar_Tactics_Types.all_implicits);
                          FStar_Tactics_Types.goals = rgs;
                          FStar_Tactics_Types.smt_goals = [];
                          FStar_Tactics_Types.depth =
                            (uu___370_2717.FStar_Tactics_Types.depth);
                          FStar_Tactics_Types.__dump =
                            (uu___370_2717.FStar_Tactics_Types.__dump);
                          FStar_Tactics_Types.psc =
                            (uu___370_2717.FStar_Tactics_Types.psc);
                          FStar_Tactics_Types.entry_range =
                            (uu___370_2717.FStar_Tactics_Types.entry_range);
                          FStar_Tactics_Types.guard_policy =
                            (uu___370_2717.FStar_Tactics_Types.guard_policy);
                          FStar_Tactics_Types.freshness =
                            (uu___370_2717.FStar_Tactics_Types.freshness);
                          FStar_Tactics_Types.tac_verb_dbg =
                            (uu___370_2717.FStar_Tactics_Types.tac_verb_dbg)
                        }  in
                      let uu____2718 = set lp  in
                      bind uu____2718
                        (fun uu____2726  ->
                           bind l
                             (fun a  ->
                                bind get
                                  (fun lp'  ->
                                     let uu____2740 = set rp  in
                                     bind uu____2740
                                       (fun uu____2748  ->
                                          bind r
                                            (fun b  ->
                                               bind get
                                                 (fun rp'  ->
                                                    let p' =
                                                      let uu___371_2764 = p
                                                         in
                                                      {
                                                        FStar_Tactics_Types.main_context
                                                          =
                                                          (uu___371_2764.FStar_Tactics_Types.main_context);
                                                        FStar_Tactics_Types.main_goal
                                                          =
                                                          (uu___371_2764.FStar_Tactics_Types.main_goal);
                                                        FStar_Tactics_Types.all_implicits
                                                          =
                                                          (uu___371_2764.FStar_Tactics_Types.all_implicits);
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
                                                          (uu___371_2764.FStar_Tactics_Types.depth);
                                                        FStar_Tactics_Types.__dump
                                                          =
                                                          (uu___371_2764.FStar_Tactics_Types.__dump);
                                                        FStar_Tactics_Types.psc
                                                          =
                                                          (uu___371_2764.FStar_Tactics_Types.psc);
                                                        FStar_Tactics_Types.entry_range
                                                          =
                                                          (uu___371_2764.FStar_Tactics_Types.entry_range);
                                                        FStar_Tactics_Types.guard_policy
                                                          =
                                                          (uu___371_2764.FStar_Tactics_Types.guard_policy);
                                                        FStar_Tactics_Types.freshness
                                                          =
                                                          (uu___371_2764.FStar_Tactics_Types.freshness);
                                                        FStar_Tactics_Types.tac_verb_dbg
                                                          =
                                                          (uu___371_2764.FStar_Tactics_Types.tac_verb_dbg)
                                                      }  in
                                                    let uu____2765 = set p'
                                                       in
                                                    bind uu____2765
                                                      (fun uu____2773  ->
                                                         bind
                                                           remove_solved_goals
                                                           (fun uu____2779 
                                                              -> ret (a, b)))))))))))
  
let focus : 'a . 'a tac -> 'a tac =
  fun f  ->
    let uu____2800 = divide FStar_BigInt.one f idtac  in
    bind uu____2800
      (fun uu____2813  -> match uu____2813 with | (a,()) -> ret a)
  
let rec map : 'a . 'a tac -> 'a Prims.list tac =
  fun tau  ->
    bind get
      (fun p  ->
         match p.FStar_Tactics_Types.goals with
         | [] -> ret []
         | uu____2850::uu____2851 ->
             let uu____2854 =
               let uu____2863 = map tau  in
               divide FStar_BigInt.one tau uu____2863  in
             bind uu____2854
               (fun uu____2881  ->
                  match uu____2881 with | (h,t) -> ret (h :: t)))
  
let (seq : unit tac -> unit tac -> unit tac) =
  fun t1  ->
    fun t2  ->
      let uu____2922 =
        bind t1
          (fun uu____2927  ->
             let uu____2928 = map t2  in
             bind uu____2928 (fun uu____2936  -> ret ()))
         in
      focus uu____2922
  
let (intro : unit -> FStar_Syntax_Syntax.binder tac) =
  fun uu____2945  ->
    let uu____2948 =
      let uu____2951 = cur_goal ()  in
      bind uu____2951
        (fun goal  ->
           let uu____2960 =
             let uu____2967 = FStar_Tactics_Types.goal_type goal  in
             FStar_Syntax_Util.arrow_one uu____2967  in
           match uu____2960 with
           | FStar_Pervasives_Native.Some (b,c) ->
               let uu____2976 =
                 let uu____2977 = FStar_Syntax_Util.is_total_comp c  in
                 Prims.op_Negation uu____2977  in
               if uu____2976
               then fail "Codomain is effectful"
               else
                 (let env' =
                    let uu____2982 = FStar_Tactics_Types.goal_env goal  in
                    FStar_TypeChecker_Env.push_binders uu____2982 [b]  in
                  let typ' = comp_to_typ c  in
                  let uu____2992 = new_uvar "intro" env' typ'  in
                  bind uu____2992
                    (fun uu____3008  ->
                       match uu____3008 with
                       | (body,ctx_uvar) ->
                           let sol =
                             FStar_Syntax_Util.abs [b] body
                               FStar_Pervasives_Native.None
                              in
                           let uu____3028 = set_solution goal sol  in
                           bind uu____3028
                             (fun uu____3034  ->
                                let g =
                                  FStar_Tactics_Types.mk_goal env' ctx_uvar
                                    goal.FStar_Tactics_Types.opts
                                    goal.FStar_Tactics_Types.is_guard
                                   in
                                let uu____3036 =
                                  let uu____3039 = bnorm_goal g  in
                                  replace_cur uu____3039  in
                                bind uu____3036 (fun uu____3041  -> ret b))))
           | FStar_Pervasives_Native.None  ->
               let uu____3046 =
                 let uu____3047 = FStar_Tactics_Types.goal_env goal  in
                 let uu____3048 = FStar_Tactics_Types.goal_type goal  in
                 tts uu____3047 uu____3048  in
               fail1 "goal is not an arrow (%s)" uu____3046)
       in
    FStar_All.pipe_left (wrap_err "intro") uu____2948
  
let (intro_rec :
  unit ->
    (FStar_Syntax_Syntax.binder,FStar_Syntax_Syntax.binder)
      FStar_Pervasives_Native.tuple2 tac)
  =
  fun uu____3063  ->
    let uu____3070 = cur_goal ()  in
    bind uu____3070
      (fun goal  ->
         FStar_Util.print_string
           "WARNING (intro_rec): calling this is known to cause normalizer loops\n";
         FStar_Util.print_string
           "WARNING (intro_rec): proceed at your own risk...\n";
         (let uu____3087 =
            let uu____3094 = FStar_Tactics_Types.goal_type goal  in
            FStar_Syntax_Util.arrow_one uu____3094  in
          match uu____3087 with
          | FStar_Pervasives_Native.Some (b,c) ->
              let uu____3107 =
                let uu____3108 = FStar_Syntax_Util.is_total_comp c  in
                Prims.op_Negation uu____3108  in
              if uu____3107
              then fail "Codomain is effectful"
              else
                (let bv =
                   let uu____3121 = FStar_Tactics_Types.goal_type goal  in
                   FStar_Syntax_Syntax.gen_bv "__recf"
                     FStar_Pervasives_Native.None uu____3121
                    in
                 let bs =
                   let uu____3129 = FStar_Syntax_Syntax.mk_binder bv  in
                   [uu____3129; b]  in
                 let env' =
                   let uu____3147 = FStar_Tactics_Types.goal_env goal  in
                   FStar_TypeChecker_Env.push_binders uu____3147 bs  in
                 let uu____3148 =
                   let uu____3155 = comp_to_typ c  in
                   new_uvar "intro_rec" env' uu____3155  in
                 bind uu____3148
                   (fun uu____3174  ->
                      match uu____3174 with
                      | (u,ctx_uvar_u) ->
                          let lb =
                            let uu____3188 =
                              FStar_Tactics_Types.goal_type goal  in
                            let uu____3191 =
                              FStar_Syntax_Util.abs [b] u
                                FStar_Pervasives_Native.None
                               in
                            FStar_Syntax_Util.mk_letbinding
                              (FStar_Util.Inl bv) [] uu____3188
                              FStar_Parser_Const.effect_Tot_lid uu____3191 []
                              FStar_Range.dummyRange
                             in
                          let body = FStar_Syntax_Syntax.bv_to_name bv  in
                          let uu____3205 =
                            FStar_Syntax_Subst.close_let_rec [lb] body  in
                          (match uu____3205 with
                           | (lbs,body1) ->
                               let tm =
                                 let uu____3227 =
                                   let uu____3228 =
                                     FStar_Tactics_Types.goal_witness goal
                                      in
                                   uu____3228.FStar_Syntax_Syntax.pos  in
                                 FStar_Syntax_Syntax.mk
                                   (FStar_Syntax_Syntax.Tm_let
                                      ((true, lbs), body1))
                                   FStar_Pervasives_Native.None uu____3227
                                  in
                               let uu____3241 = set_solution goal tm  in
                               bind uu____3241
                                 (fun uu____3250  ->
                                    let uu____3251 =
                                      let uu____3254 =
                                        bnorm_goal
                                          (let uu___374_3257 = goal  in
                                           {
                                             FStar_Tactics_Types.goal_main_env
                                               =
                                               (uu___374_3257.FStar_Tactics_Types.goal_main_env);
                                             FStar_Tactics_Types.goal_ctx_uvar
                                               = ctx_uvar_u;
                                             FStar_Tactics_Types.opts =
                                               (uu___374_3257.FStar_Tactics_Types.opts);
                                             FStar_Tactics_Types.is_guard =
                                               (uu___374_3257.FStar_Tactics_Types.is_guard)
                                           })
                                         in
                                      replace_cur uu____3254  in
                                    bind uu____3251
                                      (fun uu____3264  ->
                                         let uu____3265 =
                                           let uu____3270 =
                                             FStar_Syntax_Syntax.mk_binder bv
                                              in
                                           (uu____3270, b)  in
                                         ret uu____3265)))))
          | FStar_Pervasives_Native.None  ->
              let uu____3279 =
                let uu____3280 = FStar_Tactics_Types.goal_env goal  in
                let uu____3281 = FStar_Tactics_Types.goal_type goal  in
                tts uu____3280 uu____3281  in
              fail1 "intro_rec: goal is not an arrow (%s)" uu____3279))
  
let (norm : FStar_Syntax_Embeddings.norm_step Prims.list -> unit tac) =
  fun s  ->
    let uu____3299 = cur_goal ()  in
    bind uu____3299
      (fun goal  ->
         mlog
           (fun uu____3306  ->
              let uu____3307 =
                let uu____3308 = FStar_Tactics_Types.goal_witness goal  in
                FStar_Syntax_Print.term_to_string uu____3308  in
              FStar_Util.print1 "norm: witness = %s\n" uu____3307)
           (fun uu____3313  ->
              let steps =
                let uu____3317 = FStar_TypeChecker_Normalize.tr_norm_steps s
                   in
                FStar_List.append
                  [FStar_TypeChecker_Normalize.Reify;
                  FStar_TypeChecker_Normalize.UnfoldTac] uu____3317
                 in
              let t =
                let uu____3321 = FStar_Tactics_Types.goal_env goal  in
                let uu____3322 = FStar_Tactics_Types.goal_type goal  in
                normalize steps uu____3321 uu____3322  in
              let uu____3323 = FStar_Tactics_Types.goal_with_type goal t  in
              replace_cur uu____3323))
  
let (norm_term_env :
  env ->
    FStar_Syntax_Embeddings.norm_step Prims.list ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term tac)
  =
  fun e  ->
    fun s  ->
      fun t  ->
        let uu____3347 =
          mlog
            (fun uu____3352  ->
               let uu____3353 = FStar_Syntax_Print.term_to_string t  in
               FStar_Util.print1 "norm_term: tm = %s\n" uu____3353)
            (fun uu____3355  ->
               bind get
                 (fun ps  ->
                    let opts =
                      match ps.FStar_Tactics_Types.goals with
                      | g::uu____3361 -> g.FStar_Tactics_Types.opts
                      | uu____3364 -> FStar_Options.peek ()  in
                    mlog
                      (fun uu____3369  ->
                         let uu____3370 = FStar_Syntax_Print.term_to_string t
                            in
                         FStar_Util.print1 "norm_term_env: t = %s\n"
                           uu____3370)
                      (fun uu____3373  ->
                         let uu____3374 = __tc e t  in
                         bind uu____3374
                           (fun uu____3395  ->
                              match uu____3395 with
                              | (t1,uu____3405,uu____3406) ->
                                  let steps =
                                    let uu____3410 =
                                      FStar_TypeChecker_Normalize.tr_norm_steps
                                        s
                                       in
                                    FStar_List.append
                                      [FStar_TypeChecker_Normalize.Reify;
                                      FStar_TypeChecker_Normalize.UnfoldTac]
                                      uu____3410
                                     in
                                  let t2 =
                                    normalize steps
                                      ps.FStar_Tactics_Types.main_context t1
                                     in
                                  ret t2))))
           in
        FStar_All.pipe_left (wrap_err "norm_term") uu____3347
  
let (refine_intro : unit -> unit tac) =
  fun uu____3424  ->
    let uu____3427 =
      let uu____3430 = cur_goal ()  in
      bind uu____3430
        (fun g  ->
           let uu____3437 =
             let uu____3448 = FStar_Tactics_Types.goal_env g  in
             let uu____3449 = FStar_Tactics_Types.goal_type g  in
             FStar_TypeChecker_Rel.base_and_refinement uu____3448 uu____3449
              in
           match uu____3437 with
           | (uu____3452,FStar_Pervasives_Native.None ) ->
               fail "not a refinement"
           | (t,FStar_Pervasives_Native.Some (bv,phi)) ->
               let g1 = FStar_Tactics_Types.goal_with_type g t  in
               let uu____3477 =
                 let uu____3482 =
                   let uu____3487 =
                     let uu____3488 = FStar_Syntax_Syntax.mk_binder bv  in
                     [uu____3488]  in
                   FStar_Syntax_Subst.open_term uu____3487 phi  in
                 match uu____3482 with
                 | (bvs,phi1) ->
                     let uu____3507 =
                       let uu____3508 = FStar_List.hd bvs  in
                       FStar_Pervasives_Native.fst uu____3508  in
                     (uu____3507, phi1)
                  in
               (match uu____3477 with
                | (bv1,phi1) ->
                    let uu____3521 =
                      let uu____3524 = FStar_Tactics_Types.goal_env g  in
                      let uu____3525 =
                        let uu____3526 =
                          let uu____3529 =
                            let uu____3530 =
                              let uu____3537 =
                                FStar_Tactics_Types.goal_witness g  in
                              (bv1, uu____3537)  in
                            FStar_Syntax_Syntax.NT uu____3530  in
                          [uu____3529]  in
                        FStar_Syntax_Subst.subst uu____3526 phi1  in
                      mk_irrelevant_goal "refine_intro refinement" uu____3524
                        uu____3525 g.FStar_Tactics_Types.opts
                       in
                    bind uu____3521
                      (fun g2  ->
                         bind __dismiss
                           (fun uu____3545  -> add_goals [g1; g2]))))
       in
    FStar_All.pipe_left (wrap_err "refine_intro") uu____3427
  
let (__exact_now : Prims.bool -> FStar_Syntax_Syntax.term -> unit tac) =
  fun set_expected_typ1  ->
    fun t  ->
      let uu____3564 = cur_goal ()  in
      bind uu____3564
        (fun goal  ->
           let env =
             if set_expected_typ1
             then
               let uu____3572 = FStar_Tactics_Types.goal_env goal  in
               let uu____3573 = FStar_Tactics_Types.goal_type goal  in
               FStar_TypeChecker_Env.set_expected_typ uu____3572 uu____3573
             else FStar_Tactics_Types.goal_env goal  in
           let uu____3575 = __tc env t  in
           bind uu____3575
             (fun uu____3594  ->
                match uu____3594 with
                | (t1,typ,guard) ->
                    mlog
                      (fun uu____3609  ->
                         let uu____3610 =
                           FStar_Syntax_Print.term_to_string typ  in
                         let uu____3611 =
                           let uu____3612 = FStar_Tactics_Types.goal_env goal
                              in
                           FStar_TypeChecker_Rel.guard_to_string uu____3612
                             guard
                            in
                         FStar_Util.print2
                           "__exact_now: got type %s\n__exact_now: and guard %s\n"
                           uu____3610 uu____3611)
                      (fun uu____3615  ->
                         let uu____3616 =
                           let uu____3619 = FStar_Tactics_Types.goal_env goal
                              in
                           proc_guard "__exact typing" uu____3619 guard  in
                         bind uu____3616
                           (fun uu____3621  ->
                              mlog
                                (fun uu____3625  ->
                                   let uu____3626 =
                                     FStar_Syntax_Print.term_to_string typ
                                      in
                                   let uu____3627 =
                                     let uu____3628 =
                                       FStar_Tactics_Types.goal_type goal  in
                                     FStar_Syntax_Print.term_to_string
                                       uu____3628
                                      in
                                   FStar_Util.print2
                                     "__exact_now: unifying %s and %s\n"
                                     uu____3626 uu____3627)
                                (fun uu____3631  ->
                                   let uu____3632 =
                                     let uu____3635 =
                                       FStar_Tactics_Types.goal_env goal  in
                                     let uu____3636 =
                                       FStar_Tactics_Types.goal_type goal  in
                                     do_unify uu____3635 typ uu____3636  in
                                   bind uu____3632
                                     (fun b  ->
                                        if b
                                        then solve goal t1
                                        else
                                          (let uu____3642 =
                                             let uu____3643 =
                                               FStar_Tactics_Types.goal_env
                                                 goal
                                                in
                                             tts uu____3643 t1  in
                                           let uu____3644 =
                                             let uu____3645 =
                                               FStar_Tactics_Types.goal_env
                                                 goal
                                                in
                                             tts uu____3645 typ  in
                                           let uu____3646 =
                                             let uu____3647 =
                                               FStar_Tactics_Types.goal_env
                                                 goal
                                                in
                                             let uu____3648 =
                                               FStar_Tactics_Types.goal_type
                                                 goal
                                                in
                                             tts uu____3647 uu____3648  in
                                           let uu____3649 =
                                             let uu____3650 =
                                               FStar_Tactics_Types.goal_env
                                                 goal
                                                in
                                             let uu____3651 =
                                               FStar_Tactics_Types.goal_witness
                                                 goal
                                                in
                                             tts uu____3650 uu____3651  in
                                           fail4
                                             "%s : %s does not exactly solve the goal %s (witness = %s)"
                                             uu____3642 uu____3644 uu____3646
                                             uu____3649)))))))
  
let (t_exact : Prims.bool -> FStar_Syntax_Syntax.term -> unit tac) =
  fun set_expected_typ1  ->
    fun tm  ->
      let uu____3666 =
        mlog
          (fun uu____3671  ->
             let uu____3672 = FStar_Syntax_Print.term_to_string tm  in
             FStar_Util.print1 "t_exact: tm = %s\n" uu____3672)
          (fun uu____3675  ->
             let uu____3676 =
               let uu____3683 = __exact_now set_expected_typ1 tm  in
               trytac' uu____3683  in
             bind uu____3676
               (fun uu___338_3692  ->
                  match uu___338_3692 with
                  | FStar_Util.Inr r -> ret ()
                  | FStar_Util.Inl e ->
                      mlog
                        (fun uu____3702  ->
                           FStar_Util.print_string
                             "__exact_now failed, trying refine...\n")
                        (fun uu____3705  ->
                           let uu____3706 =
                             let uu____3713 =
                               let uu____3716 =
                                 norm [FStar_Syntax_Embeddings.Delta]  in
                               bind uu____3716
                                 (fun uu____3721  ->
                                    let uu____3722 = refine_intro ()  in
                                    bind uu____3722
                                      (fun uu____3726  ->
                                         __exact_now set_expected_typ1 tm))
                                in
                             trytac' uu____3713  in
                           bind uu____3706
                             (fun uu___337_3733  ->
                                match uu___337_3733 with
                                | FStar_Util.Inr r -> ret ()
                                | FStar_Util.Inl uu____3741 -> fail e))))
         in
      FStar_All.pipe_left (wrap_err "exact") uu____3666
  
let (uvar_free_in_goal :
  FStar_Syntax_Syntax.uvar -> FStar_Tactics_Types.goal -> Prims.bool) =
  fun u  ->
    fun g  ->
      if g.FStar_Tactics_Types.is_guard
      then false
      else
        (let free_uvars =
           let uu____3770 =
             let uu____3773 =
               let uu____3776 = FStar_Tactics_Types.goal_type g  in
               FStar_Syntax_Free.uvars uu____3776  in
             FStar_Util.set_elements uu____3773  in
           FStar_List.map (fun u1  -> u1.FStar_Syntax_Syntax.ctx_uvar_head)
             uu____3770
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
          let uu____3854 = f x  in
          bind uu____3854
            (fun y  ->
               let uu____3862 = mapM f xs  in
               bind uu____3862 (fun ys  -> ret (y :: ys)))
  
exception NoUnif 
let (uu___is_NoUnif : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with | NoUnif  -> true | uu____3882 -> false
  
let rec (__apply :
  Prims.bool ->
    FStar_Syntax_Syntax.term -> FStar_Reflection_Data.typ -> unit tac)
  =
  fun uopt  ->
    fun tm  ->
      fun typ  ->
        let uu____3902 = cur_goal ()  in
        bind uu____3902
          (fun goal  ->
             mlog
               (fun uu____3909  ->
                  let uu____3910 = FStar_Syntax_Print.term_to_string tm  in
                  FStar_Util.print1 ">>> Calling __exact(%s)\n" uu____3910)
               (fun uu____3913  ->
                  let uu____3914 =
                    let uu____3919 =
                      let uu____3922 = t_exact false tm  in
                      with_policy FStar_Tactics_Types.Force uu____3922  in
                    trytac_exn uu____3919  in
                  bind uu____3914
                    (fun uu___339_3929  ->
                       match uu___339_3929 with
                       | FStar_Pervasives_Native.Some r -> ret ()
                       | FStar_Pervasives_Native.None  ->
                           mlog
                             (fun uu____3937  ->
                                let uu____3938 =
                                  FStar_Syntax_Print.term_to_string typ  in
                                FStar_Util.print1 ">>> typ = %s\n" uu____3938)
                             (fun uu____3941  ->
                                let uu____3942 =
                                  FStar_Syntax_Util.arrow_one typ  in
                                match uu____3942 with
                                | FStar_Pervasives_Native.None  ->
                                    FStar_Exn.raise NoUnif
                                | FStar_Pervasives_Native.Some ((bv,aq),c) ->
                                    mlog
                                      (fun uu____3966  ->
                                         let uu____3967 =
                                           FStar_Syntax_Print.binder_to_string
                                             (bv, aq)
                                            in
                                         FStar_Util.print1
                                           "__apply: pushing binder %s\n"
                                           uu____3967)
                                      (fun uu____3970  ->
                                         let uu____3971 =
                                           let uu____3972 =
                                             FStar_Syntax_Util.is_total_comp
                                               c
                                              in
                                           Prims.op_Negation uu____3972  in
                                         if uu____3971
                                         then
                                           fail "apply: not total codomain"
                                         else
                                           (let uu____3976 =
                                              let uu____3983 =
                                                FStar_Tactics_Types.goal_env
                                                  goal
                                                 in
                                              new_uvar "apply" uu____3983
                                                bv.FStar_Syntax_Syntax.sort
                                               in
                                            bind uu____3976
                                              (fun uu____3994  ->
                                                 match uu____3994 with
                                                 | (u,_goal_u) ->
                                                     let tm' =
                                                       FStar_Syntax_Syntax.mk_Tm_app
                                                         tm [(u, aq)]
                                                         FStar_Pervasives_Native.None
                                                         tm.FStar_Syntax_Syntax.pos
                                                        in
                                                     let typ' =
                                                       let uu____4021 =
                                                         comp_to_typ c  in
                                                       FStar_All.pipe_left
                                                         (FStar_Syntax_Subst.subst
                                                            [FStar_Syntax_Syntax.NT
                                                               (bv, u)])
                                                         uu____4021
                                                        in
                                                     let uu____4024 =
                                                       __apply uopt tm' typ'
                                                        in
                                                     bind uu____4024
                                                       (fun uu____4032  ->
                                                          let u1 =
                                                            let uu____4034 =
                                                              FStar_Tactics_Types.goal_env
                                                                goal
                                                               in
                                                            bnorm uu____4034
                                                              u
                                                             in
                                                          let uu____4035 =
                                                            let uu____4036 =
                                                              let uu____4039
                                                                =
                                                                let uu____4040
                                                                  =
                                                                  FStar_Syntax_Util.head_and_args
                                                                    u1
                                                                   in
                                                                FStar_Pervasives_Native.fst
                                                                  uu____4040
                                                                 in
                                                              FStar_Syntax_Subst.compress
                                                                uu____4039
                                                               in
                                                            uu____4036.FStar_Syntax_Syntax.n
                                                             in
                                                          match uu____4035
                                                          with
                                                          | FStar_Syntax_Syntax.Tm_uvar
                                                              (goal_u,uu____4068)
                                                              ->
                                                              bind get
                                                                (fun ps  ->
                                                                   let uu____4088
                                                                    =
                                                                    uopt &&
                                                                    (uvar_free
                                                                    goal_u.FStar_Syntax_Syntax.ctx_uvar_head
                                                                    ps)  in
                                                                   if
                                                                    uu____4088
                                                                   then
                                                                    ret ()
                                                                   else
                                                                    (let uu____4092
                                                                    =
                                                                    let uu____4095
                                                                    =
                                                                    bnorm_goal
                                                                    (let uu___375_4098
                                                                    = goal
                                                                     in
                                                                    {
                                                                    FStar_Tactics_Types.goal_main_env
                                                                    =
                                                                    (uu___375_4098.FStar_Tactics_Types.goal_main_env);
                                                                    FStar_Tactics_Types.goal_ctx_uvar
                                                                    = goal_u;
                                                                    FStar_Tactics_Types.opts
                                                                    =
                                                                    (uu___375_4098.FStar_Tactics_Types.opts);
                                                                    FStar_Tactics_Types.is_guard
                                                                    = false
                                                                    })  in
                                                                    [uu____4095]
                                                                     in
                                                                    add_goals
                                                                    uu____4092))
                                                          | t -> ret ()))))))))
  
let try_unif : 'a . 'a tac -> 'a tac -> 'a tac =
  fun t  ->
    fun t'  -> mk_tac (fun ps  -> try run t ps with | NoUnif  -> run t' ps)
  
let (apply : Prims.bool -> FStar_Syntax_Syntax.term -> unit tac) =
  fun uopt  ->
    fun tm  ->
      let uu____4153 =
        mlog
          (fun uu____4158  ->
             let uu____4159 = FStar_Syntax_Print.term_to_string tm  in
             FStar_Util.print1 "apply: tm = %s\n" uu____4159)
          (fun uu____4162  ->
             let uu____4163 = cur_goal ()  in
             bind uu____4163
               (fun goal  ->
                  let uu____4169 =
                    let uu____4178 = FStar_Tactics_Types.goal_env goal  in
                    __tc uu____4178 tm  in
                  bind uu____4169
                    (fun uu____4192  ->
                       match uu____4192 with
                       | (tm1,typ,guard) ->
                           let typ1 =
                             let uu____4205 =
                               FStar_Tactics_Types.goal_env goal  in
                             bnorm uu____4205 typ  in
                           let uu____4206 =
                             let uu____4209 =
                               let uu____4212 = __apply uopt tm1 typ1  in
                               bind uu____4212
                                 (fun uu____4217  ->
                                    let uu____4218 =
                                      FStar_Tactics_Types.goal_env goal  in
                                    proc_guard "apply guard" uu____4218 guard)
                                in
                             focus uu____4209  in
                           let uu____4219 =
                             let uu____4222 =
                               let uu____4223 =
                                 FStar_Tactics_Types.goal_env goal  in
                               tts uu____4223 tm1  in
                             let uu____4224 =
                               let uu____4225 =
                                 FStar_Tactics_Types.goal_env goal  in
                               tts uu____4225 typ1  in
                             let uu____4226 =
                               let uu____4227 =
                                 FStar_Tactics_Types.goal_env goal  in
                               let uu____4228 =
                                 FStar_Tactics_Types.goal_type goal  in
                               tts uu____4227 uu____4228  in
                             fail3
                               "Cannot instantiate %s (of type %s) to match goal (%s)"
                               uu____4222 uu____4224 uu____4226
                              in
                           try_unif uu____4206 uu____4219)))
         in
      FStar_All.pipe_left (wrap_err "apply") uu____4153
  
let (lemma_or_sq :
  FStar_Syntax_Syntax.comp ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun c  ->
    let ct = FStar_Syntax_Util.comp_to_comp_typ_nouniv c  in
    let uu____4251 =
      FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
        FStar_Parser_Const.effect_Lemma_lid
       in
    if uu____4251
    then
      let uu____4258 =
        match ct.FStar_Syntax_Syntax.effect_args with
        | pre::post::uu____4273 ->
            ((FStar_Pervasives_Native.fst pre),
              (FStar_Pervasives_Native.fst post))
        | uu____4312 -> failwith "apply_lemma: impossible: not a lemma"  in
      match uu____4258 with
      | (pre,post) ->
          let post1 =
            let uu____4342 =
              let uu____4351 =
                FStar_Syntax_Syntax.as_arg FStar_Syntax_Util.exp_unit  in
              [uu____4351]  in
            FStar_Syntax_Util.mk_app post uu____4342  in
          FStar_Pervasives_Native.Some (pre, post1)
    else
      (let uu____4375 =
         FStar_Syntax_Util.is_pure_effect ct.FStar_Syntax_Syntax.effect_name
          in
       if uu____4375
       then
         let uu____4382 =
           FStar_Syntax_Util.un_squash ct.FStar_Syntax_Syntax.result_typ  in
         FStar_Util.map_opt uu____4382
           (fun post  -> (FStar_Syntax_Util.t_true, post))
       else FStar_Pervasives_Native.None)
  
let (apply_lemma : FStar_Syntax_Syntax.term -> unit tac) =
  fun tm  ->
    let uu____4415 =
      let uu____4418 =
        mlog
          (fun uu____4423  ->
             let uu____4424 = FStar_Syntax_Print.term_to_string tm  in
             FStar_Util.print1 "apply_lemma: tm = %s\n" uu____4424)
          (fun uu____4428  ->
             let is_unit_t t =
               let uu____4435 =
                 let uu____4436 = FStar_Syntax_Subst.compress t  in
                 uu____4436.FStar_Syntax_Syntax.n  in
               match uu____4435 with
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.unit_lid
                   -> true
               | uu____4440 -> false  in
             let uu____4441 = cur_goal ()  in
             bind uu____4441
               (fun goal  ->
                  let uu____4447 =
                    let uu____4456 = FStar_Tactics_Types.goal_env goal  in
                    __tc uu____4456 tm  in
                  bind uu____4447
                    (fun uu____4471  ->
                       match uu____4471 with
                       | (tm1,t,guard) ->
                           let uu____4483 =
                             FStar_Syntax_Util.arrow_formals_comp t  in
                           (match uu____4483 with
                            | (bs,comp) ->
                                let uu____4510 = lemma_or_sq comp  in
                                (match uu____4510 with
                                 | FStar_Pervasives_Native.None  ->
                                     fail "not a lemma or squashed function"
                                 | FStar_Pervasives_Native.Some (pre,post) ->
                                     let uu____4529 =
                                       FStar_List.fold_left
                                         (fun uu____4571  ->
                                            fun uu____4572  ->
                                              match (uu____4571, uu____4572)
                                              with
                                              | ((uvs,guard1,subst1),(b,aq))
                                                  ->
                                                  let b_t =
                                                    FStar_Syntax_Subst.subst
                                                      subst1
                                                      b.FStar_Syntax_Syntax.sort
                                                     in
                                                  let uu____4663 =
                                                    is_unit_t b_t  in
                                                  if uu____4663
                                                  then
                                                    (((FStar_Syntax_Util.exp_unit,
                                                        aq) :: uvs), guard1,
                                                      ((FStar_Syntax_Syntax.NT
                                                          (b,
                                                            FStar_Syntax_Util.exp_unit))
                                                      :: subst1))
                                                  else
                                                    (let uu____4693 =
                                                       let uu____4706 =
                                                         let uu____4707 =
                                                           FStar_Tactics_Types.goal_type
                                                             goal
                                                            in
                                                         uu____4707.FStar_Syntax_Syntax.pos
                                                          in
                                                       let uu____4710 =
                                                         FStar_Tactics_Types.goal_env
                                                           goal
                                                          in
                                                       FStar_TypeChecker_Util.new_implicit_var
                                                         "apply_lemma"
                                                         uu____4706
                                                         uu____4710 b_t
                                                        in
                                                     match uu____4693 with
                                                     | (u,uu____4726,g_u) ->
                                                         let uu____4740 =
                                                           FStar_TypeChecker_Rel.conj_guard
                                                             guard1 g_u
                                                            in
                                                         (((u, aq) :: uvs),
                                                           uu____4740,
                                                           ((FStar_Syntax_Syntax.NT
                                                               (b, u)) ::
                                                           subst1))))
                                         ([], guard, []) bs
                                        in
                                     (match uu____4529 with
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
                                          let uu____4801 =
                                            let uu____4804 =
                                              FStar_Tactics_Types.goal_env
                                                goal
                                               in
                                            let uu____4805 =
                                              FStar_Syntax_Util.mk_squash
                                                FStar_Syntax_Syntax.U_zero
                                                post1
                                               in
                                            let uu____4806 =
                                              FStar_Tactics_Types.goal_type
                                                goal
                                               in
                                            do_unify uu____4804 uu____4805
                                              uu____4806
                                             in
                                          bind uu____4801
                                            (fun b  ->
                                               if Prims.op_Negation b
                                               then
                                                 let uu____4814 =
                                                   let uu____4815 =
                                                     FStar_Tactics_Types.goal_env
                                                       goal
                                                      in
                                                   tts uu____4815 tm1  in
                                                 let uu____4816 =
                                                   let uu____4817 =
                                                     FStar_Tactics_Types.goal_env
                                                       goal
                                                      in
                                                   let uu____4818 =
                                                     FStar_Syntax_Util.mk_squash
                                                       FStar_Syntax_Syntax.U_zero
                                                       post1
                                                      in
                                                   tts uu____4817 uu____4818
                                                    in
                                                 let uu____4819 =
                                                   let uu____4820 =
                                                     FStar_Tactics_Types.goal_env
                                                       goal
                                                      in
                                                   let uu____4821 =
                                                     FStar_Tactics_Types.goal_type
                                                       goal
                                                      in
                                                   tts uu____4820 uu____4821
                                                    in
                                                 fail3
                                                   "Cannot instantiate lemma %s (with postcondition: %s) to match goal (%s)"
                                                   uu____4814 uu____4816
                                                   uu____4819
                                               else
                                                 (let uu____4823 =
                                                    add_implicits
                                                      implicits.FStar_TypeChecker_Env.implicits
                                                     in
                                                  bind uu____4823
                                                    (fun uu____4828  ->
                                                       let uu____4829 =
                                                         solve' goal
                                                           FStar_Syntax_Util.exp_unit
                                                          in
                                                       bind uu____4829
                                                         (fun uu____4837  ->
                                                            let is_free_uvar
                                                              uv t1 =
                                                              let free_uvars
                                                                =
                                                                let uu____4862
                                                                  =
                                                                  let uu____4865
                                                                    =
                                                                    FStar_Syntax_Free.uvars
                                                                    t1  in
                                                                  FStar_Util.set_elements
                                                                    uu____4865
                                                                   in
                                                                FStar_List.map
                                                                  (fun x  ->
                                                                    x.FStar_Syntax_Syntax.ctx_uvar_head)
                                                                  uu____4862
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
                                                                   let uu____4900
                                                                    =
                                                                    FStar_Tactics_Types.goal_type
                                                                    g'  in
                                                                   is_free_uvar
                                                                    uv
                                                                    uu____4900)
                                                                goals
                                                               in
                                                            let checkone t1
                                                              goals =
                                                              let uu____4916
                                                                =
                                                                FStar_Syntax_Util.head_and_args
                                                                  t1
                                                                 in
                                                              match uu____4916
                                                              with
                                                              | (hd1,uu____4932)
                                                                  ->
                                                                  (match 
                                                                    hd1.FStar_Syntax_Syntax.n
                                                                   with
                                                                   | 
                                                                   FStar_Syntax_Syntax.Tm_uvar
                                                                    (uv,uu____4954)
                                                                    ->
                                                                    appears
                                                                    uv.FStar_Syntax_Syntax.ctx_uvar_head
                                                                    goals
                                                                   | 
                                                                   uu____4971
                                                                    -> false)
                                                               in
                                                            let uu____4972 =
                                                              FStar_All.pipe_right
                                                                implicits.FStar_TypeChecker_Env.implicits
                                                                (mapM
                                                                   (fun
                                                                    uu____5035
                                                                     ->
                                                                    match uu____5035
                                                                    with
                                                                    | 
                                                                    (_msg,term,ctx_uvar,_range)
                                                                    ->
                                                                    let uu____5058
                                                                    =
                                                                    FStar_Syntax_Util.head_and_args
                                                                    term  in
                                                                    (match uu____5058
                                                                    with
                                                                    | 
                                                                    (hd1,uu____5084)
                                                                    ->
                                                                    let uu____5105
                                                                    =
                                                                    let uu____5106
                                                                    =
                                                                    FStar_Syntax_Subst.compress
                                                                    hd1  in
                                                                    uu____5106.FStar_Syntax_Syntax.n
                                                                     in
                                                                    (match uu____5105
                                                                    with
                                                                    | 
                                                                    FStar_Syntax_Syntax.Tm_uvar
                                                                    (ctx_uvar1,uu____5120)
                                                                    ->
                                                                    let goal1
                                                                    =
                                                                    bnorm_goal
                                                                    (let uu___378_5140
                                                                    = goal
                                                                     in
                                                                    {
                                                                    FStar_Tactics_Types.goal_main_env
                                                                    =
                                                                    (uu___378_5140.FStar_Tactics_Types.goal_main_env);
                                                                    FStar_Tactics_Types.goal_ctx_uvar
                                                                    =
                                                                    ctx_uvar1;
                                                                    FStar_Tactics_Types.opts
                                                                    =
                                                                    (uu___378_5140.FStar_Tactics_Types.opts);
                                                                    FStar_Tactics_Types.is_guard
                                                                    =
                                                                    (uu___378_5140.FStar_Tactics_Types.is_guard)
                                                                    })  in
                                                                    ret
                                                                    ([goal1],
                                                                    [])
                                                                    | 
                                                                    uu____5153
                                                                    ->
                                                                    let env =
                                                                    let uu___379_5155
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    goal  in
                                                                    {
                                                                    FStar_TypeChecker_Env.solver
                                                                    =
                                                                    (uu___379_5155.FStar_TypeChecker_Env.solver);
                                                                    FStar_TypeChecker_Env.range
                                                                    =
                                                                    (uu___379_5155.FStar_TypeChecker_Env.range);
                                                                    FStar_TypeChecker_Env.curmodule
                                                                    =
                                                                    (uu___379_5155.FStar_TypeChecker_Env.curmodule);
                                                                    FStar_TypeChecker_Env.gamma
                                                                    =
                                                                    (ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_gamma);
                                                                    FStar_TypeChecker_Env.gamma_sig
                                                                    =
                                                                    (uu___379_5155.FStar_TypeChecker_Env.gamma_sig);
                                                                    FStar_TypeChecker_Env.gamma_cache
                                                                    =
                                                                    (uu___379_5155.FStar_TypeChecker_Env.gamma_cache);
                                                                    FStar_TypeChecker_Env.modules
                                                                    =
                                                                    (uu___379_5155.FStar_TypeChecker_Env.modules);
                                                                    FStar_TypeChecker_Env.expected_typ
                                                                    =
                                                                    (uu___379_5155.FStar_TypeChecker_Env.expected_typ);
                                                                    FStar_TypeChecker_Env.sigtab
                                                                    =
                                                                    (uu___379_5155.FStar_TypeChecker_Env.sigtab);
                                                                    FStar_TypeChecker_Env.is_pattern
                                                                    =
                                                                    (uu___379_5155.FStar_TypeChecker_Env.is_pattern);
                                                                    FStar_TypeChecker_Env.instantiate_imp
                                                                    =
                                                                    (uu___379_5155.FStar_TypeChecker_Env.instantiate_imp);
                                                                    FStar_TypeChecker_Env.effects
                                                                    =
                                                                    (uu___379_5155.FStar_TypeChecker_Env.effects);
                                                                    FStar_TypeChecker_Env.generalize
                                                                    =
                                                                    (uu___379_5155.FStar_TypeChecker_Env.generalize);
                                                                    FStar_TypeChecker_Env.letrecs
                                                                    =
                                                                    (uu___379_5155.FStar_TypeChecker_Env.letrecs);
                                                                    FStar_TypeChecker_Env.top_level
                                                                    =
                                                                    (uu___379_5155.FStar_TypeChecker_Env.top_level);
                                                                    FStar_TypeChecker_Env.check_uvars
                                                                    =
                                                                    (uu___379_5155.FStar_TypeChecker_Env.check_uvars);
                                                                    FStar_TypeChecker_Env.use_eq
                                                                    =
                                                                    (uu___379_5155.FStar_TypeChecker_Env.use_eq);
                                                                    FStar_TypeChecker_Env.is_iface
                                                                    =
                                                                    (uu___379_5155.FStar_TypeChecker_Env.is_iface);
                                                                    FStar_TypeChecker_Env.admit
                                                                    =
                                                                    (uu___379_5155.FStar_TypeChecker_Env.admit);
                                                                    FStar_TypeChecker_Env.lax
                                                                    =
                                                                    (uu___379_5155.FStar_TypeChecker_Env.lax);
                                                                    FStar_TypeChecker_Env.lax_universes
                                                                    =
                                                                    (uu___379_5155.FStar_TypeChecker_Env.lax_universes);
                                                                    FStar_TypeChecker_Env.failhard
                                                                    =
                                                                    (uu___379_5155.FStar_TypeChecker_Env.failhard);
                                                                    FStar_TypeChecker_Env.nosynth
                                                                    =
                                                                    (uu___379_5155.FStar_TypeChecker_Env.nosynth);
                                                                    FStar_TypeChecker_Env.uvar_subtyping
                                                                    =
                                                                    (uu___379_5155.FStar_TypeChecker_Env.uvar_subtyping);
                                                                    FStar_TypeChecker_Env.tc_term
                                                                    =
                                                                    (uu___379_5155.FStar_TypeChecker_Env.tc_term);
                                                                    FStar_TypeChecker_Env.type_of
                                                                    =
                                                                    (uu___379_5155.FStar_TypeChecker_Env.type_of);
                                                                    FStar_TypeChecker_Env.universe_of
                                                                    =
                                                                    (uu___379_5155.FStar_TypeChecker_Env.universe_of);
                                                                    FStar_TypeChecker_Env.check_type_of
                                                                    =
                                                                    (uu___379_5155.FStar_TypeChecker_Env.check_type_of);
                                                                    FStar_TypeChecker_Env.use_bv_sorts
                                                                    =
                                                                    (uu___379_5155.FStar_TypeChecker_Env.use_bv_sorts);
                                                                    FStar_TypeChecker_Env.qtbl_name_and_index
                                                                    =
                                                                    (uu___379_5155.FStar_TypeChecker_Env.qtbl_name_and_index);
                                                                    FStar_TypeChecker_Env.normalized_eff_names
                                                                    =
                                                                    (uu___379_5155.FStar_TypeChecker_Env.normalized_eff_names);
                                                                    FStar_TypeChecker_Env.proof_ns
                                                                    =
                                                                    (uu___379_5155.FStar_TypeChecker_Env.proof_ns);
                                                                    FStar_TypeChecker_Env.synth_hook
                                                                    =
                                                                    (uu___379_5155.FStar_TypeChecker_Env.synth_hook);
                                                                    FStar_TypeChecker_Env.splice
                                                                    =
                                                                    (uu___379_5155.FStar_TypeChecker_Env.splice);
                                                                    FStar_TypeChecker_Env.is_native_tactic
                                                                    =
                                                                    (uu___379_5155.FStar_TypeChecker_Env.is_native_tactic);
                                                                    FStar_TypeChecker_Env.identifier_info
                                                                    =
                                                                    (uu___379_5155.FStar_TypeChecker_Env.identifier_info);
                                                                    FStar_TypeChecker_Env.tc_hooks
                                                                    =
                                                                    (uu___379_5155.FStar_TypeChecker_Env.tc_hooks);
                                                                    FStar_TypeChecker_Env.dsenv
                                                                    =
                                                                    (uu___379_5155.FStar_TypeChecker_Env.dsenv);
                                                                    FStar_TypeChecker_Env.dep_graph
                                                                    =
                                                                    (uu___379_5155.FStar_TypeChecker_Env.dep_graph)
                                                                    }  in
                                                                    let g_typ
                                                                    =
                                                                    let uu____5157
                                                                    =
                                                                    FStar_Options.__temp_fast_implicits
                                                                    ()  in
                                                                    if
                                                                    uu____5157
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
                                                                    let uu____5160
                                                                    =
                                                                    let uu____5167
                                                                    =
                                                                    FStar_TypeChecker_Env.set_expected_typ
                                                                    env
                                                                    ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_typ
                                                                     in
                                                                    env.FStar_TypeChecker_Env.type_of
                                                                    uu____5167
                                                                    term1  in
                                                                    match uu____5160
                                                                    with
                                                                    | 
                                                                    (uu____5168,uu____5169,g_typ)
                                                                    -> g_typ)
                                                                     in
                                                                    let uu____5171
                                                                    =
                                                                    let uu____5176
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    goal  in
                                                                    goal_from_guard
                                                                    "apply_lemma solved arg"
                                                                    uu____5176
                                                                    g_typ
                                                                    goal.FStar_Tactics_Types.opts
                                                                     in
                                                                    bind
                                                                    uu____5171
                                                                    (fun
                                                                    uu___340_5188
                                                                     ->
                                                                    match uu___340_5188
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
                                                            bind uu____4972
                                                              (fun goals_  ->
                                                                 let sub_goals
                                                                   =
                                                                   let uu____5256
                                                                    =
                                                                    FStar_List.map
                                                                    FStar_Pervasives_Native.fst
                                                                    goals_
                                                                     in
                                                                   FStar_List.flatten
                                                                    uu____5256
                                                                    in
                                                                 let smt_goals
                                                                   =
                                                                   let uu____5278
                                                                    =
                                                                    FStar_List.map
                                                                    FStar_Pervasives_Native.snd
                                                                    goals_
                                                                     in
                                                                   FStar_List.flatten
                                                                    uu____5278
                                                                    in
                                                                 let rec filter'
                                                                   f xs =
                                                                   match xs
                                                                   with
                                                                   | 
                                                                   [] -> []
                                                                   | 
                                                                   x::xs1 ->
                                                                    let uu____5339
                                                                    = f x xs1
                                                                     in
                                                                    if
                                                                    uu____5339
                                                                    then
                                                                    let uu____5342
                                                                    =
                                                                    filter' f
                                                                    xs1  in x
                                                                    ::
                                                                    uu____5342
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
                                                                    let uu____5356
                                                                    =
                                                                    let uu____5357
                                                                    =
                                                                    FStar_Tactics_Types.goal_witness
                                                                    g  in
                                                                    checkone
                                                                    uu____5357
                                                                    goals  in
                                                                    Prims.op_Negation
                                                                    uu____5356)
                                                                    sub_goals
                                                                    in
                                                                 let uu____5358
                                                                   =
                                                                   let uu____5361
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    goal  in
                                                                   proc_guard
                                                                    "apply_lemma guard"
                                                                    uu____5361
                                                                    guard
                                                                    in
                                                                 bind
                                                                   uu____5358
                                                                   (fun
                                                                    uu____5364
                                                                     ->
                                                                    let uu____5365
                                                                    =
                                                                    let uu____5368
                                                                    =
                                                                    let uu____5369
                                                                    =
                                                                    let uu____5370
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    goal  in
                                                                    let uu____5371
                                                                    =
                                                                    FStar_Syntax_Util.mk_squash
                                                                    FStar_Syntax_Syntax.U_zero
                                                                    pre1  in
                                                                    istrivial
                                                                    uu____5370
                                                                    uu____5371
                                                                     in
                                                                    Prims.op_Negation
                                                                    uu____5369
                                                                     in
                                                                    if
                                                                    uu____5368
                                                                    then
                                                                    let uu____5374
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    goal  in
                                                                    add_irrelevant_goal
                                                                    "apply_lemma precondition"
                                                                    uu____5374
                                                                    pre1
                                                                    goal.FStar_Tactics_Types.opts
                                                                    else
                                                                    ret ()
                                                                     in
                                                                    bind
                                                                    uu____5365
                                                                    (fun
                                                                    uu____5378
                                                                     ->
                                                                    let uu____5379
                                                                    =
                                                                    add_smt_goals
                                                                    smt_goals
                                                                     in
                                                                    bind
                                                                    uu____5379
                                                                    (fun
                                                                    uu____5383
                                                                     ->
                                                                    add_goals
                                                                    sub_goals1))))))))))))))
         in
      focus uu____4418  in
    FStar_All.pipe_left (wrap_err "apply_lemma") uu____4415
  
let (destruct_eq' :
  FStar_Reflection_Data.typ ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun typ  ->
    let uu____5405 = FStar_Syntax_Util.destruct_typ_as_formula typ  in
    match uu____5405 with
    | FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn
        (l,uu____5415::(e1,uu____5417)::(e2,uu____5419)::[])) when
        FStar_Ident.lid_equals l FStar_Parser_Const.eq2_lid ->
        FStar_Pervasives_Native.Some (e1, e2)
    | uu____5462 -> FStar_Pervasives_Native.None
  
let (destruct_eq :
  FStar_Reflection_Data.typ ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun typ  ->
    let uu____5486 = destruct_eq' typ  in
    match uu____5486 with
    | FStar_Pervasives_Native.Some t -> FStar_Pervasives_Native.Some t
    | FStar_Pervasives_Native.None  ->
        let uu____5516 = FStar_Syntax_Util.un_squash typ  in
        (match uu____5516 with
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
        let uu____5578 = FStar_TypeChecker_Env.pop_bv e1  in
        match uu____5578 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (bv',e') ->
            if FStar_Syntax_Syntax.bv_eq bvar bv'
            then FStar_Pervasives_Native.Some (e', [])
            else
              (let uu____5626 = aux e'  in
               FStar_Util.map_opt uu____5626
                 (fun uu____5650  ->
                    match uu____5650 with | (e'',bvs) -> (e'', (bv' :: bvs))))
         in
      let uu____5671 = aux e  in
      FStar_Util.map_opt uu____5671
        (fun uu____5695  ->
           match uu____5695 with | (e',bvs) -> (e', (FStar_List.rev bvs)))
  
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
          let uu____5762 =
            let uu____5771 = FStar_Tactics_Types.goal_env g  in
            split_env b1 uu____5771  in
          FStar_Util.map_opt uu____5762
            (fun uu____5786  ->
               match uu____5786 with
               | (e0,bvs) ->
                   let s1 bv =
                     let uu___380_5805 = bv  in
                     let uu____5806 =
                       FStar_Syntax_Subst.subst s bv.FStar_Syntax_Syntax.sort
                        in
                     {
                       FStar_Syntax_Syntax.ppname =
                         (uu___380_5805.FStar_Syntax_Syntax.ppname);
                       FStar_Syntax_Syntax.index =
                         (uu___380_5805.FStar_Syntax_Syntax.index);
                       FStar_Syntax_Syntax.sort = uu____5806
                     }  in
                   let bvs1 = FStar_List.map s1 bvs  in
                   let new_env = push_bvs e0 (b2 :: bvs1)  in
                   let new_goal =
                     let uu___381_5814 = g.FStar_Tactics_Types.goal_ctx_uvar
                        in
                     let uu____5815 =
                       FStar_TypeChecker_Env.all_binders new_env  in
                     let uu____5822 =
                       let uu____5825 = FStar_Tactics_Types.goal_type g  in
                       FStar_Syntax_Subst.subst s uu____5825  in
                     {
                       FStar_Syntax_Syntax.ctx_uvar_head =
                         (uu___381_5814.FStar_Syntax_Syntax.ctx_uvar_head);
                       FStar_Syntax_Syntax.ctx_uvar_gamma =
                         (new_env.FStar_TypeChecker_Env.gamma);
                       FStar_Syntax_Syntax.ctx_uvar_binders = uu____5815;
                       FStar_Syntax_Syntax.ctx_uvar_typ = uu____5822;
                       FStar_Syntax_Syntax.ctx_uvar_reason =
                         (uu___381_5814.FStar_Syntax_Syntax.ctx_uvar_reason);
                       FStar_Syntax_Syntax.ctx_uvar_should_check =
                         (uu___381_5814.FStar_Syntax_Syntax.ctx_uvar_should_check);
                       FStar_Syntax_Syntax.ctx_uvar_range =
                         (uu___381_5814.FStar_Syntax_Syntax.ctx_uvar_range)
                     }  in
                   let uu___382_5826 = g  in
                   {
                     FStar_Tactics_Types.goal_main_env =
                       (uu___382_5826.FStar_Tactics_Types.goal_main_env);
                     FStar_Tactics_Types.goal_ctx_uvar = new_goal;
                     FStar_Tactics_Types.opts =
                       (uu___382_5826.FStar_Tactics_Types.opts);
                     FStar_Tactics_Types.is_guard =
                       (uu___382_5826.FStar_Tactics_Types.is_guard)
                   })
  
let (rewrite : FStar_Syntax_Syntax.binder -> unit tac) =
  fun h  ->
    let uu____5836 =
      let uu____5839 = cur_goal ()  in
      bind uu____5839
        (fun goal  ->
           let uu____5847 = h  in
           match uu____5847 with
           | (bv,uu____5851) ->
               mlog
                 (fun uu____5855  ->
                    let uu____5856 = FStar_Syntax_Print.bv_to_string bv  in
                    let uu____5857 =
                      FStar_Syntax_Print.term_to_string
                        bv.FStar_Syntax_Syntax.sort
                       in
                    FStar_Util.print2 "+++Rewrite %s : %s\n" uu____5856
                      uu____5857)
                 (fun uu____5860  ->
                    let uu____5861 =
                      let uu____5870 = FStar_Tactics_Types.goal_env goal  in
                      split_env bv uu____5870  in
                    match uu____5861 with
                    | FStar_Pervasives_Native.None  ->
                        fail "binder not found in environment"
                    | FStar_Pervasives_Native.Some (e0,bvs) ->
                        let uu____5891 =
                          destruct_eq bv.FStar_Syntax_Syntax.sort  in
                        (match uu____5891 with
                         | FStar_Pervasives_Native.Some (x,e) ->
                             let uu____5906 =
                               let uu____5907 = FStar_Syntax_Subst.compress x
                                  in
                               uu____5907.FStar_Syntax_Syntax.n  in
                             (match uu____5906 with
                              | FStar_Syntax_Syntax.Tm_name x1 ->
                                  let s = [FStar_Syntax_Syntax.NT (x1, e)]
                                     in
                                  let s1 bv1 =
                                    let uu___383_5924 = bv1  in
                                    let uu____5925 =
                                      FStar_Syntax_Subst.subst s
                                        bv1.FStar_Syntax_Syntax.sort
                                       in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___383_5924.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___383_5924.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = uu____5925
                                    }  in
                                  let bvs1 = FStar_List.map s1 bvs  in
                                  let new_env = push_bvs e0 (bv :: bvs1)  in
                                  let new_goal =
                                    let uu___384_5933 =
                                      goal.FStar_Tactics_Types.goal_ctx_uvar
                                       in
                                    let uu____5934 =
                                      FStar_TypeChecker_Env.all_binders
                                        new_env
                                       in
                                    let uu____5941 =
                                      let uu____5944 =
                                        FStar_Tactics_Types.goal_type goal
                                         in
                                      FStar_Syntax_Subst.subst s uu____5944
                                       in
                                    {
                                      FStar_Syntax_Syntax.ctx_uvar_head =
                                        (uu___384_5933.FStar_Syntax_Syntax.ctx_uvar_head);
                                      FStar_Syntax_Syntax.ctx_uvar_gamma =
                                        (new_env.FStar_TypeChecker_Env.gamma);
                                      FStar_Syntax_Syntax.ctx_uvar_binders =
                                        uu____5934;
                                      FStar_Syntax_Syntax.ctx_uvar_typ =
                                        uu____5941;
                                      FStar_Syntax_Syntax.ctx_uvar_reason =
                                        (uu___384_5933.FStar_Syntax_Syntax.ctx_uvar_reason);
                                      FStar_Syntax_Syntax.ctx_uvar_should_check
                                        =
                                        (uu___384_5933.FStar_Syntax_Syntax.ctx_uvar_should_check);
                                      FStar_Syntax_Syntax.ctx_uvar_range =
                                        (uu___384_5933.FStar_Syntax_Syntax.ctx_uvar_range)
                                    }  in
                                  replace_cur
                                    (let uu___385_5947 = goal  in
                                     {
                                       FStar_Tactics_Types.goal_main_env =
                                         (uu___385_5947.FStar_Tactics_Types.goal_main_env);
                                       FStar_Tactics_Types.goal_ctx_uvar =
                                         new_goal;
                                       FStar_Tactics_Types.opts =
                                         (uu___385_5947.FStar_Tactics_Types.opts);
                                       FStar_Tactics_Types.is_guard =
                                         (uu___385_5947.FStar_Tactics_Types.is_guard)
                                     })
                              | uu____5948 ->
                                  fail
                                    "Not an equality hypothesis with a variable on the LHS")
                         | uu____5949 -> fail "Not an equality hypothesis")))
       in
    FStar_All.pipe_left (wrap_err "rewrite") uu____5836
  
let (rename_to : FStar_Syntax_Syntax.binder -> Prims.string -> unit tac) =
  fun b  ->
    fun s  ->
      let uu____5974 =
        let uu____5977 = cur_goal ()  in
        bind uu____5977
          (fun goal  ->
             let uu____5988 = b  in
             match uu____5988 with
             | (bv,uu____5992) ->
                 let bv' =
                   let uu____5994 =
                     let uu___386_5995 = bv  in
                     let uu____5996 =
                       FStar_Ident.mk_ident
                         (s,
                           ((bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange))
                        in
                     {
                       FStar_Syntax_Syntax.ppname = uu____5996;
                       FStar_Syntax_Syntax.index =
                         (uu___386_5995.FStar_Syntax_Syntax.index);
                       FStar_Syntax_Syntax.sort =
                         (uu___386_5995.FStar_Syntax_Syntax.sort)
                     }  in
                   FStar_Syntax_Syntax.freshen_bv uu____5994  in
                 let s1 =
                   let uu____6000 =
                     let uu____6001 =
                       let uu____6008 = FStar_Syntax_Syntax.bv_to_name bv'
                          in
                       (bv, uu____6008)  in
                     FStar_Syntax_Syntax.NT uu____6001  in
                   [uu____6000]  in
                 let uu____6013 = subst_goal bv bv' s1 goal  in
                 (match uu____6013 with
                  | FStar_Pervasives_Native.None  ->
                      fail "binder not found in environment"
                  | FStar_Pervasives_Native.Some goal1 -> replace_cur goal1))
         in
      FStar_All.pipe_left (wrap_err "rename_to") uu____5974
  
let (binder_retype : FStar_Syntax_Syntax.binder -> unit tac) =
  fun b  ->
    let uu____6032 =
      let uu____6035 = cur_goal ()  in
      bind uu____6035
        (fun goal  ->
           let uu____6044 = b  in
           match uu____6044 with
           | (bv,uu____6048) ->
               let uu____6049 =
                 let uu____6058 = FStar_Tactics_Types.goal_env goal  in
                 split_env bv uu____6058  in
               (match uu____6049 with
                | FStar_Pervasives_Native.None  ->
                    fail "binder is not present in environment"
                | FStar_Pervasives_Native.Some (e0,bvs) ->
                    let uu____6079 = FStar_Syntax_Util.type_u ()  in
                    (match uu____6079 with
                     | (ty,u) ->
                         let uu____6088 = new_uvar "binder_retype" e0 ty  in
                         bind uu____6088
                           (fun uu____6106  ->
                              match uu____6106 with
                              | (t',u_t') ->
                                  let bv'' =
                                    let uu___387_6116 = bv  in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___387_6116.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___387_6116.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = t'
                                    }  in
                                  let s =
                                    let uu____6120 =
                                      let uu____6121 =
                                        let uu____6128 =
                                          FStar_Syntax_Syntax.bv_to_name bv''
                                           in
                                        (bv, uu____6128)  in
                                      FStar_Syntax_Syntax.NT uu____6121  in
                                    [uu____6120]  in
                                  let bvs1 =
                                    FStar_List.map
                                      (fun b1  ->
                                         let uu___388_6140 = b1  in
                                         let uu____6141 =
                                           FStar_Syntax_Subst.subst s
                                             b1.FStar_Syntax_Syntax.sort
                                            in
                                         {
                                           FStar_Syntax_Syntax.ppname =
                                             (uu___388_6140.FStar_Syntax_Syntax.ppname);
                                           FStar_Syntax_Syntax.index =
                                             (uu___388_6140.FStar_Syntax_Syntax.index);
                                           FStar_Syntax_Syntax.sort =
                                             uu____6141
                                         }) bvs
                                     in
                                  let env' = push_bvs e0 (bv'' :: bvs1)  in
                                  bind __dismiss
                                    (fun uu____6148  ->
                                       let new_goal =
                                         let uu____6150 =
                                           FStar_Tactics_Types.goal_with_env
                                             goal env'
                                            in
                                         let uu____6151 =
                                           let uu____6152 =
                                             FStar_Tactics_Types.goal_type
                                               goal
                                              in
                                           FStar_Syntax_Subst.subst s
                                             uu____6152
                                            in
                                         FStar_Tactics_Types.goal_with_type
                                           uu____6150 uu____6151
                                          in
                                       let uu____6153 = add_goals [new_goal]
                                          in
                                       bind uu____6153
                                         (fun uu____6158  ->
                                            let uu____6159 =
                                              FStar_Syntax_Util.mk_eq2
                                                (FStar_Syntax_Syntax.U_succ u)
                                                ty
                                                bv.FStar_Syntax_Syntax.sort
                                                t'
                                               in
                                            add_irrelevant_goal
                                              "binder_retype equation" e0
                                              uu____6159
                                              goal.FStar_Tactics_Types.opts))))))
       in
    FStar_All.pipe_left (wrap_err "binder_retype") uu____6032
  
let (norm_binder_type :
  FStar_Syntax_Embeddings.norm_step Prims.list ->
    FStar_Syntax_Syntax.binder -> unit tac)
  =
  fun s  ->
    fun b  ->
      let uu____6182 =
        let uu____6185 = cur_goal ()  in
        bind uu____6185
          (fun goal  ->
             let uu____6194 = b  in
             match uu____6194 with
             | (bv,uu____6198) ->
                 let uu____6199 =
                   let uu____6208 = FStar_Tactics_Types.goal_env goal  in
                   split_env bv uu____6208  in
                 (match uu____6199 with
                  | FStar_Pervasives_Native.None  ->
                      fail "binder is not present in environment"
                  | FStar_Pervasives_Native.Some (e0,bvs) ->
                      let steps =
                        let uu____6232 =
                          FStar_TypeChecker_Normalize.tr_norm_steps s  in
                        FStar_List.append
                          [FStar_TypeChecker_Normalize.Reify;
                          FStar_TypeChecker_Normalize.UnfoldTac] uu____6232
                         in
                      let sort' =
                        normalize steps e0 bv.FStar_Syntax_Syntax.sort  in
                      let bv' =
                        let uu___389_6237 = bv  in
                        {
                          FStar_Syntax_Syntax.ppname =
                            (uu___389_6237.FStar_Syntax_Syntax.ppname);
                          FStar_Syntax_Syntax.index =
                            (uu___389_6237.FStar_Syntax_Syntax.index);
                          FStar_Syntax_Syntax.sort = sort'
                        }  in
                      let env' = push_bvs e0 (bv' :: bvs)  in
                      let uu____6239 =
                        FStar_Tactics_Types.goal_with_env goal env'  in
                      replace_cur uu____6239))
         in
      FStar_All.pipe_left (wrap_err "norm_binder_type") uu____6182
  
let (revert : unit -> unit tac) =
  fun uu____6250  ->
    let uu____6253 = cur_goal ()  in
    bind uu____6253
      (fun goal  ->
         let uu____6259 =
           let uu____6266 = FStar_Tactics_Types.goal_env goal  in
           FStar_TypeChecker_Env.pop_bv uu____6266  in
         match uu____6259 with
         | FStar_Pervasives_Native.None  ->
             fail "Cannot revert; empty context"
         | FStar_Pervasives_Native.Some (x,env') ->
             let typ' =
               let uu____6282 =
                 let uu____6285 = FStar_Tactics_Types.goal_type goal  in
                 FStar_Syntax_Syntax.mk_Total uu____6285  in
               FStar_Syntax_Util.arrow [(x, FStar_Pervasives_Native.None)]
                 uu____6282
                in
             let uu____6294 = new_uvar "revert" env' typ'  in
             bind uu____6294
               (fun uu____6309  ->
                  match uu____6309 with
                  | (r,u_r) ->
                      let uu____6318 =
                        let uu____6321 =
                          let uu____6322 =
                            let uu____6323 =
                              FStar_Tactics_Types.goal_type goal  in
                            uu____6323.FStar_Syntax_Syntax.pos  in
                          let uu____6326 =
                            let uu____6331 =
                              let uu____6332 =
                                let uu____6339 =
                                  FStar_Syntax_Syntax.bv_to_name x  in
                                FStar_Syntax_Syntax.as_arg uu____6339  in
                              [uu____6332]  in
                            FStar_Syntax_Syntax.mk_Tm_app r uu____6331  in
                          uu____6326 FStar_Pervasives_Native.None uu____6322
                           in
                        set_solution goal uu____6321  in
                      bind uu____6318
                        (fun uu____6356  ->
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
      let uu____6368 = FStar_Syntax_Free.names t  in
      FStar_Util.set_mem bv uu____6368
  
let rec (clear : FStar_Syntax_Syntax.binder -> unit tac) =
  fun b  ->
    let bv = FStar_Pervasives_Native.fst b  in
    let uu____6381 = cur_goal ()  in
    bind uu____6381
      (fun goal  ->
         mlog
           (fun uu____6389  ->
              let uu____6390 = FStar_Syntax_Print.binder_to_string b  in
              let uu____6391 =
                let uu____6392 =
                  let uu____6393 =
                    let uu____6400 = FStar_Tactics_Types.goal_env goal  in
                    FStar_TypeChecker_Env.all_binders uu____6400  in
                  FStar_All.pipe_right uu____6393 FStar_List.length  in
                FStar_All.pipe_right uu____6392 FStar_Util.string_of_int  in
              FStar_Util.print2 "Clear of (%s), env has %s binders\n"
                uu____6390 uu____6391)
           (fun uu____6413  ->
              let uu____6414 =
                let uu____6423 = FStar_Tactics_Types.goal_env goal  in
                split_env bv uu____6423  in
              match uu____6414 with
              | FStar_Pervasives_Native.None  ->
                  fail "Cannot clear; binder not in environment"
              | FStar_Pervasives_Native.Some (e',bvs) ->
                  let rec check1 bvs1 =
                    match bvs1 with
                    | [] -> ret ()
                    | bv'::bvs2 ->
                        let uu____6462 =
                          free_in bv bv'.FStar_Syntax_Syntax.sort  in
                        if uu____6462
                        then
                          let uu____6465 =
                            let uu____6466 =
                              FStar_Syntax_Print.bv_to_string bv'  in
                            FStar_Util.format1
                              "Cannot clear; binder present in the type of %s"
                              uu____6466
                             in
                          fail uu____6465
                        else check1 bvs2
                     in
                  let uu____6468 =
                    let uu____6469 = FStar_Tactics_Types.goal_type goal  in
                    free_in bv uu____6469  in
                  if uu____6468
                  then fail "Cannot clear; binder present in goal"
                  else
                    (let uu____6473 = check1 bvs  in
                     bind uu____6473
                       (fun uu____6479  ->
                          let env' = push_bvs e' bvs  in
                          let uu____6481 =
                            let uu____6488 =
                              FStar_Tactics_Types.goal_type goal  in
                            new_uvar "clear.witness" env' uu____6488  in
                          bind uu____6481
                            (fun uu____6497  ->
                               match uu____6497 with
                               | (ut,uvar_ut) ->
                                   let uu____6506 = set_solution goal ut  in
                                   bind uu____6506
                                     (fun uu____6511  ->
                                        let uu____6512 =
                                          FStar_Tactics_Types.mk_goal env'
                                            uvar_ut
                                            goal.FStar_Tactics_Types.opts
                                            goal.FStar_Tactics_Types.is_guard
                                           in
                                        replace_cur uu____6512))))))
  
let (clear_top : unit -> unit tac) =
  fun uu____6519  ->
    let uu____6522 = cur_goal ()  in
    bind uu____6522
      (fun goal  ->
         let uu____6528 =
           let uu____6535 = FStar_Tactics_Types.goal_env goal  in
           FStar_TypeChecker_Env.pop_bv uu____6535  in
         match uu____6528 with
         | FStar_Pervasives_Native.None  ->
             fail "Cannot clear; empty context"
         | FStar_Pervasives_Native.Some (x,uu____6543) ->
             let uu____6548 = FStar_Syntax_Syntax.mk_binder x  in
             clear uu____6548)
  
let (prune : Prims.string -> unit tac) =
  fun s  ->
    let uu____6558 = cur_goal ()  in
    bind uu____6558
      (fun g  ->
         let ctx = FStar_Tactics_Types.goal_env g  in
         let ctx' =
           let uu____6568 = FStar_Ident.path_of_text s  in
           FStar_TypeChecker_Env.rem_proof_ns ctx uu____6568  in
         let g' = FStar_Tactics_Types.goal_with_env g ctx'  in
         bind __dismiss (fun uu____6571  -> add_goals [g']))
  
let (addns : Prims.string -> unit tac) =
  fun s  ->
    let uu____6581 = cur_goal ()  in
    bind uu____6581
      (fun g  ->
         let ctx = FStar_Tactics_Types.goal_env g  in
         let ctx' =
           let uu____6591 = FStar_Ident.path_of_text s  in
           FStar_TypeChecker_Env.add_proof_ns ctx uu____6591  in
         let g' = FStar_Tactics_Types.goal_with_env g ctx'  in
         bind __dismiss (fun uu____6594  -> add_goals [g']))
  
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
            let uu____6634 = FStar_Syntax_Subst.compress t  in
            uu____6634.FStar_Syntax_Syntax.n  in
          let uu____6637 =
            if d = FStar_Tactics_Types.TopDown
            then
              f env
                (let uu___393_6643 = t  in
                 {
                   FStar_Syntax_Syntax.n = tn;
                   FStar_Syntax_Syntax.pos =
                     (uu___393_6643.FStar_Syntax_Syntax.pos);
                   FStar_Syntax_Syntax.vars =
                     (uu___393_6643.FStar_Syntax_Syntax.vars)
                 })
            else ret t  in
          bind uu____6637
            (fun t1  ->
               let ff = tac_fold_env d f env  in
               let tn1 =
                 let uu____6659 =
                   let uu____6660 = FStar_Syntax_Subst.compress t1  in
                   uu____6660.FStar_Syntax_Syntax.n  in
                 match uu____6659 with
                 | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
                     let uu____6687 = ff hd1  in
                     bind uu____6687
                       (fun hd2  ->
                          let fa uu____6709 =
                            match uu____6709 with
                            | (a,q) ->
                                let uu____6722 = ff a  in
                                bind uu____6722 (fun a1  -> ret (a1, q))
                             in
                          let uu____6735 = mapM fa args  in
                          bind uu____6735
                            (fun args1  ->
                               ret (FStar_Syntax_Syntax.Tm_app (hd2, args1))))
                 | FStar_Syntax_Syntax.Tm_abs (bs,t2,k) ->
                     let uu____6801 = FStar_Syntax_Subst.open_term bs t2  in
                     (match uu____6801 with
                      | (bs1,t') ->
                          let uu____6810 =
                            let uu____6813 =
                              FStar_TypeChecker_Env.push_binders env bs1  in
                            tac_fold_env d f uu____6813 t'  in
                          bind uu____6810
                            (fun t''  ->
                               let uu____6817 =
                                 let uu____6818 =
                                   let uu____6835 =
                                     FStar_Syntax_Subst.close_binders bs1  in
                                   let uu____6842 =
                                     FStar_Syntax_Subst.close bs1 t''  in
                                   (uu____6835, uu____6842, k)  in
                                 FStar_Syntax_Syntax.Tm_abs uu____6818  in
                               ret uu____6817))
                 | FStar_Syntax_Syntax.Tm_arrow (bs,k) -> ret tn
                 | FStar_Syntax_Syntax.Tm_match (hd1,brs) ->
                     let uu____6911 = ff hd1  in
                     bind uu____6911
                       (fun hd2  ->
                          let ffb br =
                            let uu____6926 =
                              FStar_Syntax_Subst.open_branch br  in
                            match uu____6926 with
                            | (pat,w,e) ->
                                let bvs = FStar_Syntax_Syntax.pat_bvs pat  in
                                let ff1 =
                                  let uu____6958 =
                                    FStar_TypeChecker_Env.push_bvs env bvs
                                     in
                                  tac_fold_env d f uu____6958  in
                                let uu____6959 = ff1 e  in
                                bind uu____6959
                                  (fun e1  ->
                                     let br1 =
                                       FStar_Syntax_Subst.close_branch
                                         (pat, w, e1)
                                        in
                                     ret br1)
                             in
                          let uu____6974 = mapM ffb brs  in
                          bind uu____6974
                            (fun brs1  ->
                               ret (FStar_Syntax_Syntax.Tm_match (hd2, brs1))))
                 | FStar_Syntax_Syntax.Tm_let
                     ((false
                       ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inl bv;
                          FStar_Syntax_Syntax.lbunivs = uu____7018;
                          FStar_Syntax_Syntax.lbtyp = uu____7019;
                          FStar_Syntax_Syntax.lbeff = uu____7020;
                          FStar_Syntax_Syntax.lbdef = def;
                          FStar_Syntax_Syntax.lbattrs = uu____7022;
                          FStar_Syntax_Syntax.lbpos = uu____7023;_}::[]),e)
                     ->
                     let lb =
                       let uu____7048 =
                         let uu____7049 = FStar_Syntax_Subst.compress t1  in
                         uu____7049.FStar_Syntax_Syntax.n  in
                       match uu____7048 with
                       | FStar_Syntax_Syntax.Tm_let
                           ((false ,lb::[]),uu____7053) -> lb
                       | uu____7066 -> failwith "impossible"  in
                     let fflb lb1 =
                       let uu____7075 = ff lb1.FStar_Syntax_Syntax.lbdef  in
                       bind uu____7075
                         (fun def1  ->
                            ret
                              (let uu___390_7081 = lb1  in
                               {
                                 FStar_Syntax_Syntax.lbname =
                                   (uu___390_7081.FStar_Syntax_Syntax.lbname);
                                 FStar_Syntax_Syntax.lbunivs =
                                   (uu___390_7081.FStar_Syntax_Syntax.lbunivs);
                                 FStar_Syntax_Syntax.lbtyp =
                                   (uu___390_7081.FStar_Syntax_Syntax.lbtyp);
                                 FStar_Syntax_Syntax.lbeff =
                                   (uu___390_7081.FStar_Syntax_Syntax.lbeff);
                                 FStar_Syntax_Syntax.lbdef = def1;
                                 FStar_Syntax_Syntax.lbattrs =
                                   (uu___390_7081.FStar_Syntax_Syntax.lbattrs);
                                 FStar_Syntax_Syntax.lbpos =
                                   (uu___390_7081.FStar_Syntax_Syntax.lbpos)
                               }))
                        in
                     let uu____7082 = fflb lb  in
                     bind uu____7082
                       (fun lb1  ->
                          let uu____7092 =
                            let uu____7097 =
                              let uu____7098 =
                                FStar_Syntax_Syntax.mk_binder bv  in
                              [uu____7098]  in
                            FStar_Syntax_Subst.open_term uu____7097 e  in
                          match uu____7092 with
                          | (bs,e1) ->
                              let ff1 =
                                let uu____7122 =
                                  FStar_TypeChecker_Env.push_binders env bs
                                   in
                                tac_fold_env d f uu____7122  in
                              let uu____7123 = ff1 e1  in
                              bind uu____7123
                                (fun e2  ->
                                   let e3 = FStar_Syntax_Subst.close bs e2
                                      in
                                   ret
                                     (FStar_Syntax_Syntax.Tm_let
                                        ((false, [lb1]), e3))))
                 | FStar_Syntax_Syntax.Tm_let ((true ,lbs),e) ->
                     let fflb lb =
                       let uu____7164 = ff lb.FStar_Syntax_Syntax.lbdef  in
                       bind uu____7164
                         (fun def  ->
                            ret
                              (let uu___391_7170 = lb  in
                               {
                                 FStar_Syntax_Syntax.lbname =
                                   (uu___391_7170.FStar_Syntax_Syntax.lbname);
                                 FStar_Syntax_Syntax.lbunivs =
                                   (uu___391_7170.FStar_Syntax_Syntax.lbunivs);
                                 FStar_Syntax_Syntax.lbtyp =
                                   (uu___391_7170.FStar_Syntax_Syntax.lbtyp);
                                 FStar_Syntax_Syntax.lbeff =
                                   (uu___391_7170.FStar_Syntax_Syntax.lbeff);
                                 FStar_Syntax_Syntax.lbdef = def;
                                 FStar_Syntax_Syntax.lbattrs =
                                   (uu___391_7170.FStar_Syntax_Syntax.lbattrs);
                                 FStar_Syntax_Syntax.lbpos =
                                   (uu___391_7170.FStar_Syntax_Syntax.lbpos)
                               }))
                        in
                     let uu____7171 = FStar_Syntax_Subst.open_let_rec lbs e
                        in
                     (match uu____7171 with
                      | (lbs1,e1) ->
                          let uu____7186 = mapM fflb lbs1  in
                          bind uu____7186
                            (fun lbs2  ->
                               let uu____7198 = ff e1  in
                               bind uu____7198
                                 (fun e2  ->
                                    let uu____7206 =
                                      FStar_Syntax_Subst.close_let_rec lbs2
                                        e2
                                       in
                                    match uu____7206 with
                                    | (lbs3,e3) ->
                                        ret
                                          (FStar_Syntax_Syntax.Tm_let
                                             ((true, lbs3), e3)))))
                 | FStar_Syntax_Syntax.Tm_ascribed (t2,asc,eff) ->
                     let uu____7274 = ff t2  in
                     bind uu____7274
                       (fun t3  ->
                          ret
                            (FStar_Syntax_Syntax.Tm_ascribed (t3, asc, eff)))
                 | FStar_Syntax_Syntax.Tm_meta (t2,m) ->
                     let uu____7305 = ff t2  in
                     bind uu____7305
                       (fun t3  -> ret (FStar_Syntax_Syntax.Tm_meta (t3, m)))
                 | uu____7312 -> ret tn  in
               bind tn1
                 (fun tn2  ->
                    let t' =
                      let uu___392_7319 = t1  in
                      {
                        FStar_Syntax_Syntax.n = tn2;
                        FStar_Syntax_Syntax.pos =
                          (uu___392_7319.FStar_Syntax_Syntax.pos);
                        FStar_Syntax_Syntax.vars =
                          (uu___392_7319.FStar_Syntax_Syntax.vars)
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
            let uu____7356 = FStar_TypeChecker_TcTerm.tc_term env t  in
            match uu____7356 with
            | (t1,lcomp,g) ->
                let uu____7368 =
                  (let uu____7371 =
                     FStar_Syntax_Util.is_pure_or_ghost_lcomp lcomp  in
                   Prims.op_Negation uu____7371) ||
                    (let uu____7373 = FStar_TypeChecker_Rel.is_trivial g  in
                     Prims.op_Negation uu____7373)
                   in
                if uu____7368
                then ret t1
                else
                  (let rewrite_eq =
                     let typ = lcomp.FStar_Syntax_Syntax.res_typ  in
                     let uu____7381 = new_uvar "pointwise_rec" env typ  in
                     bind uu____7381
                       (fun uu____7397  ->
                          match uu____7397 with
                          | (ut,uvar_ut) ->
                              (log ps
                                 (fun uu____7410  ->
                                    let uu____7411 =
                                      FStar_Syntax_Print.term_to_string t1
                                       in
                                    let uu____7412 =
                                      FStar_Syntax_Print.term_to_string ut
                                       in
                                    FStar_Util.print2
                                      "Pointwise_rec: making equality\n\t%s ==\n\t%s\n"
                                      uu____7411 uu____7412);
                               (let uu____7413 =
                                  let uu____7416 =
                                    let uu____7417 =
                                      FStar_TypeChecker_TcTerm.universe_of
                                        env typ
                                       in
                                    FStar_Syntax_Util.mk_eq2 uu____7417 typ
                                      t1 ut
                                     in
                                  add_irrelevant_goal
                                    "pointwise_rec equation" env uu____7416
                                    opts
                                   in
                                bind uu____7413
                                  (fun uu____7420  ->
                                     let uu____7421 =
                                       bind tau
                                         (fun uu____7427  ->
                                            let ut1 =
                                              FStar_TypeChecker_Normalize.reduce_uvar_solutions
                                                env ut
                                               in
                                            log ps
                                              (fun uu____7433  ->
                                                 let uu____7434 =
                                                   FStar_Syntax_Print.term_to_string
                                                     t1
                                                    in
                                                 let uu____7435 =
                                                   FStar_Syntax_Print.term_to_string
                                                     ut1
                                                    in
                                                 FStar_Util.print2
                                                   "Pointwise_rec: succeeded rewriting\n\t%s to\n\t%s\n"
                                                   uu____7434 uu____7435);
                                            ret ut1)
                                        in
                                     focus uu____7421))))
                      in
                   let uu____7436 = trytac' rewrite_eq  in
                   bind uu____7436
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
          let uu____7634 = FStar_Syntax_Subst.compress t  in
          maybe_continue ctrl uu____7634
            (fun t1  ->
               let uu____7642 =
                 f env
                   (let uu___396_7651 = t1  in
                    {
                      FStar_Syntax_Syntax.n = (t1.FStar_Syntax_Syntax.n);
                      FStar_Syntax_Syntax.pos =
                        (uu___396_7651.FStar_Syntax_Syntax.pos);
                      FStar_Syntax_Syntax.vars =
                        (uu___396_7651.FStar_Syntax_Syntax.vars)
                    })
                  in
               bind uu____7642
                 (fun uu____7667  ->
                    match uu____7667 with
                    | (t2,ctrl1) ->
                        maybe_continue ctrl1 t2
                          (fun t3  ->
                             let uu____7690 =
                               let uu____7691 =
                                 FStar_Syntax_Subst.compress t3  in
                               uu____7691.FStar_Syntax_Syntax.n  in
                             match uu____7690 with
                             | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
                                 let uu____7724 =
                                   ctrl_tac_fold f env ctrl1 hd1  in
                                 bind uu____7724
                                   (fun uu____7749  ->
                                      match uu____7749 with
                                      | (hd2,ctrl2) ->
                                          let ctrl3 = keep_going ctrl2  in
                                          let uu____7765 =
                                            ctrl_tac_fold_args f env ctrl3
                                              args
                                             in
                                          bind uu____7765
                                            (fun uu____7792  ->
                                               match uu____7792 with
                                               | (args1,ctrl4) ->
                                                   ret
                                                     ((let uu___394_7822 = t3
                                                          in
                                                       {
                                                         FStar_Syntax_Syntax.n
                                                           =
                                                           (FStar_Syntax_Syntax.Tm_app
                                                              (hd2, args1));
                                                         FStar_Syntax_Syntax.pos
                                                           =
                                                           (uu___394_7822.FStar_Syntax_Syntax.pos);
                                                         FStar_Syntax_Syntax.vars
                                                           =
                                                           (uu___394_7822.FStar_Syntax_Syntax.vars)
                                                       }), ctrl4)))
                             | FStar_Syntax_Syntax.Tm_abs (bs,t4,k) ->
                                 let uu____7858 =
                                   FStar_Syntax_Subst.open_term bs t4  in
                                 (match uu____7858 with
                                  | (bs1,t') ->
                                      let uu____7873 =
                                        let uu____7880 =
                                          FStar_TypeChecker_Env.push_binders
                                            env bs1
                                           in
                                        ctrl_tac_fold f uu____7880 ctrl1 t'
                                         in
                                      bind uu____7873
                                        (fun uu____7898  ->
                                           match uu____7898 with
                                           | (t'',ctrl2) ->
                                               let uu____7913 =
                                                 let uu____7920 =
                                                   let uu___395_7923 = t4  in
                                                   let uu____7926 =
                                                     let uu____7927 =
                                                       let uu____7944 =
                                                         FStar_Syntax_Subst.close_binders
                                                           bs1
                                                          in
                                                       let uu____7951 =
                                                         FStar_Syntax_Subst.close
                                                           bs1 t''
                                                          in
                                                       (uu____7944,
                                                         uu____7951, k)
                                                        in
                                                     FStar_Syntax_Syntax.Tm_abs
                                                       uu____7927
                                                      in
                                                   {
                                                     FStar_Syntax_Syntax.n =
                                                       uu____7926;
                                                     FStar_Syntax_Syntax.pos
                                                       =
                                                       (uu___395_7923.FStar_Syntax_Syntax.pos);
                                                     FStar_Syntax_Syntax.vars
                                                       =
                                                       (uu___395_7923.FStar_Syntax_Syntax.vars)
                                                   }  in
                                                 (uu____7920, ctrl2)  in
                                               ret uu____7913))
                             | FStar_Syntax_Syntax.Tm_arrow (bs,k) ->
                                 ret (t3, ctrl1)
                             | uu____7998 -> ret (t3, ctrl1))))

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
              let uu____8041 = ctrl_tac_fold f env ctrl t  in
              bind uu____8041
                (fun uu____8065  ->
                   match uu____8065 with
                   | (t1,ctrl1) ->
                       let uu____8080 = ctrl_tac_fold_args f env ctrl1 ts1
                          in
                       bind uu____8080
                         (fun uu____8107  ->
                            match uu____8107 with
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
              let uu____8189 =
                let uu____8196 =
                  add_irrelevant_goal "dummy" env FStar_Syntax_Util.t_true
                    opts
                   in
                bind uu____8196
                  (fun uu____8205  ->
                     let uu____8206 = ctrl t1  in
                     bind uu____8206
                       (fun res  ->
                          let uu____8229 = trivial ()  in
                          bind uu____8229 (fun uu____8237  -> ret res)))
                 in
              bind uu____8189
                (fun uu____8253  ->
                   match uu____8253 with
                   | (should_rewrite,ctrl1) ->
                       if Prims.op_Negation should_rewrite
                       then ret (t1, ctrl1)
                       else
                         (let uu____8277 =
                            FStar_TypeChecker_TcTerm.tc_term env t1  in
                          match uu____8277 with
                          | (t2,lcomp,g) ->
                              let uu____8293 =
                                (let uu____8296 =
                                   FStar_Syntax_Util.is_pure_or_ghost_lcomp
                                     lcomp
                                    in
                                 Prims.op_Negation uu____8296) ||
                                  (let uu____8298 =
                                     FStar_TypeChecker_Rel.is_trivial g  in
                                   Prims.op_Negation uu____8298)
                                 in
                              if uu____8293
                              then ret (t2, globalStop)
                              else
                                (let typ = lcomp.FStar_Syntax_Syntax.res_typ
                                    in
                                 let uu____8311 =
                                   new_uvar "pointwise_rec" env typ  in
                                 bind uu____8311
                                   (fun uu____8331  ->
                                      match uu____8331 with
                                      | (ut,uvar_ut) ->
                                          (log ps
                                             (fun uu____8348  ->
                                                let uu____8349 =
                                                  FStar_Syntax_Print.term_to_string
                                                    t2
                                                   in
                                                let uu____8350 =
                                                  FStar_Syntax_Print.term_to_string
                                                    ut
                                                   in
                                                FStar_Util.print2
                                                  "Pointwise_rec: making equality\n\t%s ==\n\t%s\n"
                                                  uu____8349 uu____8350);
                                           (let uu____8351 =
                                              let uu____8354 =
                                                let uu____8355 =
                                                  FStar_TypeChecker_TcTerm.universe_of
                                                    env typ
                                                   in
                                                FStar_Syntax_Util.mk_eq2
                                                  uu____8355 typ t2 ut
                                                 in
                                              add_irrelevant_goal
                                                "rewrite_rec equation" env
                                                uu____8354 opts
                                               in
                                            bind uu____8351
                                              (fun uu____8362  ->
                                                 let uu____8363 =
                                                   bind rewriter
                                                     (fun uu____8377  ->
                                                        let ut1 =
                                                          FStar_TypeChecker_Normalize.reduce_uvar_solutions
                                                            env ut
                                                           in
                                                        log ps
                                                          (fun uu____8383  ->
                                                             let uu____8384 =
                                                               FStar_Syntax_Print.term_to_string
                                                                 t2
                                                                in
                                                             let uu____8385 =
                                                               FStar_Syntax_Print.term_to_string
                                                                 ut1
                                                                in
                                                             FStar_Util.print2
                                                               "rewrite_rec: succeeded rewriting\n\t%s to\n\t%s\n"
                                                               uu____8384
                                                               uu____8385);
                                                        ret (ut1, ctrl1))
                                                    in
                                                 focus uu____8363)))))))
  
let (topdown_rewrite :
  (FStar_Syntax_Syntax.term ->
     (Prims.bool,FStar_BigInt.t) FStar_Pervasives_Native.tuple2 tac)
    -> unit tac -> unit tac)
  =
  fun ctrl  ->
    fun rewriter  ->
      let uu____8426 =
        bind get
          (fun ps  ->
             let uu____8436 =
               match ps.FStar_Tactics_Types.goals with
               | g::gs -> (g, gs)
               | [] -> failwith "no goals"  in
             match uu____8436 with
             | (g,gs) ->
                 let gt1 = FStar_Tactics_Types.goal_type g  in
                 (log ps
                    (fun uu____8473  ->
                       let uu____8474 = FStar_Syntax_Print.term_to_string gt1
                          in
                       FStar_Util.print1 "Topdown_rewrite starting with %s\n"
                         uu____8474);
                  bind dismiss_all
                    (fun uu____8477  ->
                       let uu____8478 =
                         let uu____8485 = FStar_Tactics_Types.goal_env g  in
                         ctrl_tac_fold
                           (rewrite_rec ps ctrl rewriter
                              g.FStar_Tactics_Types.opts) uu____8485
                           keepGoing gt1
                          in
                       bind uu____8478
                         (fun uu____8497  ->
                            match uu____8497 with
                            | (gt',uu____8505) ->
                                (log ps
                                   (fun uu____8509  ->
                                      let uu____8510 =
                                        FStar_Syntax_Print.term_to_string gt'
                                         in
                                      FStar_Util.print1
                                        "Topdown_rewrite seems to have succeded with %s\n"
                                        uu____8510);
                                 (let uu____8511 = push_goals gs  in
                                  bind uu____8511
                                    (fun uu____8516  ->
                                       let uu____8517 =
                                         let uu____8520 =
                                           FStar_Tactics_Types.goal_with_type
                                             g gt'
                                            in
                                         [uu____8520]  in
                                       add_goals uu____8517)))))))
         in
      FStar_All.pipe_left (wrap_err "topdown_rewrite") uu____8426
  
let (pointwise : FStar_Tactics_Types.direction -> unit tac -> unit tac) =
  fun d  ->
    fun tau  ->
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
                       FStar_Util.print1 "Pointwise starting with %s\n"
                         uu____8591);
                  bind dismiss_all
                    (fun uu____8594  ->
                       let uu____8595 =
                         let uu____8598 = FStar_Tactics_Types.goal_env g  in
                         tac_fold_env d
                           (pointwise_rec ps tau g.FStar_Tactics_Types.opts)
                           uu____8598 gt1
                          in
                       bind uu____8595
                         (fun gt'  ->
                            log ps
                              (fun uu____8606  ->
                                 let uu____8607 =
                                   FStar_Syntax_Print.term_to_string gt'  in
                                 FStar_Util.print1
                                   "Pointwise seems to have succeded with %s\n"
                                   uu____8607);
                            (let uu____8608 = push_goals gs  in
                             bind uu____8608
                               (fun uu____8613  ->
                                  let uu____8614 =
                                    let uu____8617 =
                                      FStar_Tactics_Types.goal_with_type g
                                        gt'
                                       in
                                    [uu____8617]  in
                                  add_goals uu____8614))))))
         in
      FStar_All.pipe_left (wrap_err "pointwise") uu____8543
  
let (trefl : unit -> unit tac) =
  fun uu____8628  ->
    let uu____8631 =
      let uu____8634 = cur_goal ()  in
      bind uu____8634
        (fun g  ->
           let uu____8652 =
             let uu____8657 = FStar_Tactics_Types.goal_type g  in
             FStar_Syntax_Util.un_squash uu____8657  in
           match uu____8652 with
           | FStar_Pervasives_Native.Some t ->
               let uu____8665 = FStar_Syntax_Util.head_and_args' t  in
               (match uu____8665 with
                | (hd1,args) ->
                    let uu____8698 =
                      let uu____8709 =
                        let uu____8710 = FStar_Syntax_Util.un_uinst hd1  in
                        uu____8710.FStar_Syntax_Syntax.n  in
                      (uu____8709, args)  in
                    (match uu____8698 with
                     | (FStar_Syntax_Syntax.Tm_fvar
                        fv,uu____8722::(l,uu____8724)::(r,uu____8726)::[])
                         when
                         FStar_Syntax_Syntax.fv_eq_lid fv
                           FStar_Parser_Const.eq2_lid
                         ->
                         let uu____8753 =
                           let uu____8756 = FStar_Tactics_Types.goal_env g
                              in
                           do_unify uu____8756 l r  in
                         bind uu____8753
                           (fun b  ->
                              if Prims.op_Negation b
                              then
                                let uu____8763 =
                                  let uu____8764 =
                                    FStar_Tactics_Types.goal_env g  in
                                  tts uu____8764 l  in
                                let uu____8765 =
                                  let uu____8766 =
                                    FStar_Tactics_Types.goal_env g  in
                                  tts uu____8766 r  in
                                fail2 "not a trivial equality (%s vs %s)"
                                  uu____8763 uu____8765
                              else solve' g FStar_Syntax_Util.exp_unit)
                     | (hd2,uu____8769) ->
                         let uu____8782 =
                           let uu____8783 = FStar_Tactics_Types.goal_env g
                              in
                           tts uu____8783 t  in
                         fail1 "trefl: not an equality (%s)" uu____8782))
           | FStar_Pervasives_Native.None  -> fail "not an irrelevant goal")
       in
    FStar_All.pipe_left (wrap_err "trefl") uu____8631
  
let (dup : unit -> unit tac) =
  fun uu____8796  ->
    let uu____8799 = cur_goal ()  in
    bind uu____8799
      (fun g  ->
         let uu____8805 =
           let uu____8812 = FStar_Tactics_Types.goal_env g  in
           let uu____8813 = FStar_Tactics_Types.goal_type g  in
           new_uvar "dup" uu____8812 uu____8813  in
         bind uu____8805
           (fun uu____8822  ->
              match uu____8822 with
              | (u,u_uvar) ->
                  let g' =
                    let uu___397_8832 = g  in
                    {
                      FStar_Tactics_Types.goal_main_env =
                        (uu___397_8832.FStar_Tactics_Types.goal_main_env);
                      FStar_Tactics_Types.goal_ctx_uvar = u_uvar;
                      FStar_Tactics_Types.opts =
                        (uu___397_8832.FStar_Tactics_Types.opts);
                      FStar_Tactics_Types.is_guard =
                        (uu___397_8832.FStar_Tactics_Types.is_guard)
                    }  in
                  bind __dismiss
                    (fun uu____8835  ->
                       let uu____8836 =
                         let uu____8839 = FStar_Tactics_Types.goal_env g  in
                         let uu____8840 =
                           let uu____8841 =
                             let uu____8842 = FStar_Tactics_Types.goal_env g
                                in
                             let uu____8843 = FStar_Tactics_Types.goal_type g
                                in
                             FStar_TypeChecker_TcTerm.universe_of uu____8842
                               uu____8843
                              in
                           let uu____8844 = FStar_Tactics_Types.goal_type g
                              in
                           let uu____8845 =
                             FStar_Tactics_Types.goal_witness g  in
                           FStar_Syntax_Util.mk_eq2 uu____8841 uu____8844 u
                             uu____8845
                            in
                         add_irrelevant_goal "dup equation" uu____8839
                           uu____8840 g.FStar_Tactics_Types.opts
                          in
                       bind uu____8836
                         (fun uu____8848  ->
                            let uu____8849 = add_goals [g']  in
                            bind uu____8849 (fun uu____8853  -> ret ())))))
  
let (flip : unit -> unit tac) =
  fun uu____8860  ->
    bind get
      (fun ps  ->
         match ps.FStar_Tactics_Types.goals with
         | g1::g2::gs ->
             set
               (let uu___398_8877 = ps  in
                {
                  FStar_Tactics_Types.main_context =
                    (uu___398_8877.FStar_Tactics_Types.main_context);
                  FStar_Tactics_Types.main_goal =
                    (uu___398_8877.FStar_Tactics_Types.main_goal);
                  FStar_Tactics_Types.all_implicits =
                    (uu___398_8877.FStar_Tactics_Types.all_implicits);
                  FStar_Tactics_Types.goals = (g2 :: g1 :: gs);
                  FStar_Tactics_Types.smt_goals =
                    (uu___398_8877.FStar_Tactics_Types.smt_goals);
                  FStar_Tactics_Types.depth =
                    (uu___398_8877.FStar_Tactics_Types.depth);
                  FStar_Tactics_Types.__dump =
                    (uu___398_8877.FStar_Tactics_Types.__dump);
                  FStar_Tactics_Types.psc =
                    (uu___398_8877.FStar_Tactics_Types.psc);
                  FStar_Tactics_Types.entry_range =
                    (uu___398_8877.FStar_Tactics_Types.entry_range);
                  FStar_Tactics_Types.guard_policy =
                    (uu___398_8877.FStar_Tactics_Types.guard_policy);
                  FStar_Tactics_Types.freshness =
                    (uu___398_8877.FStar_Tactics_Types.freshness);
                  FStar_Tactics_Types.tac_verb_dbg =
                    (uu___398_8877.FStar_Tactics_Types.tac_verb_dbg)
                })
         | uu____8878 -> fail "flip: less than 2 goals")
  
let (later : unit -> unit tac) =
  fun uu____8887  ->
    bind get
      (fun ps  ->
         match ps.FStar_Tactics_Types.goals with
         | [] -> ret ()
         | g::gs ->
             set
               (let uu___399_8900 = ps  in
                {
                  FStar_Tactics_Types.main_context =
                    (uu___399_8900.FStar_Tactics_Types.main_context);
                  FStar_Tactics_Types.main_goal =
                    (uu___399_8900.FStar_Tactics_Types.main_goal);
                  FStar_Tactics_Types.all_implicits =
                    (uu___399_8900.FStar_Tactics_Types.all_implicits);
                  FStar_Tactics_Types.goals = (FStar_List.append gs [g]);
                  FStar_Tactics_Types.smt_goals =
                    (uu___399_8900.FStar_Tactics_Types.smt_goals);
                  FStar_Tactics_Types.depth =
                    (uu___399_8900.FStar_Tactics_Types.depth);
                  FStar_Tactics_Types.__dump =
                    (uu___399_8900.FStar_Tactics_Types.__dump);
                  FStar_Tactics_Types.psc =
                    (uu___399_8900.FStar_Tactics_Types.psc);
                  FStar_Tactics_Types.entry_range =
                    (uu___399_8900.FStar_Tactics_Types.entry_range);
                  FStar_Tactics_Types.guard_policy =
                    (uu___399_8900.FStar_Tactics_Types.guard_policy);
                  FStar_Tactics_Types.freshness =
                    (uu___399_8900.FStar_Tactics_Types.freshness);
                  FStar_Tactics_Types.tac_verb_dbg =
                    (uu___399_8900.FStar_Tactics_Types.tac_verb_dbg)
                }))
  
let (qed : unit -> unit tac) =
  fun uu____8907  ->
    bind get
      (fun ps  ->
         match ps.FStar_Tactics_Types.goals with
         | [] -> ret ()
         | uu____8914 -> fail "Not done!")
  
let (cases :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 tac)
  =
  fun t  ->
    let uu____8934 =
      let uu____8941 = cur_goal ()  in
      bind uu____8941
        (fun g  ->
           let uu____8951 =
             let uu____8960 = FStar_Tactics_Types.goal_env g  in
             __tc uu____8960 t  in
           bind uu____8951
             (fun uu____8988  ->
                match uu____8988 with
                | (t1,typ,guard) ->
                    let uu____9004 = FStar_Syntax_Util.head_and_args typ  in
                    (match uu____9004 with
                     | (hd1,args) ->
                         let uu____9047 =
                           let uu____9060 =
                             let uu____9061 = FStar_Syntax_Util.un_uinst hd1
                                in
                             uu____9061.FStar_Syntax_Syntax.n  in
                           (uu____9060, args)  in
                         (match uu____9047 with
                          | (FStar_Syntax_Syntax.Tm_fvar
                             fv,(p,uu____9080)::(q,uu____9082)::[]) when
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
                                let uu____9120 =
                                  let uu____9121 =
                                    FStar_Tactics_Types.goal_env g  in
                                  FStar_TypeChecker_Env.push_bv uu____9121
                                    v_p
                                   in
                                FStar_Tactics_Types.goal_with_env g
                                  uu____9120
                                 in
                              let g2 =
                                let uu____9123 =
                                  let uu____9124 =
                                    FStar_Tactics_Types.goal_env g  in
                                  FStar_TypeChecker_Env.push_bv uu____9124
                                    v_q
                                   in
                                FStar_Tactics_Types.goal_with_env g
                                  uu____9123
                                 in
                              bind __dismiss
                                (fun uu____9131  ->
                                   let uu____9132 = add_goals [g1; g2]  in
                                   bind uu____9132
                                     (fun uu____9141  ->
                                        let uu____9142 =
                                          let uu____9147 =
                                            FStar_Syntax_Syntax.bv_to_name
                                              v_p
                                             in
                                          let uu____9148 =
                                            FStar_Syntax_Syntax.bv_to_name
                                              v_q
                                             in
                                          (uu____9147, uu____9148)  in
                                        ret uu____9142))
                          | uu____9153 ->
                              let uu____9166 =
                                let uu____9167 =
                                  FStar_Tactics_Types.goal_env g  in
                                tts uu____9167 typ  in
                              fail1 "Not a disjunction: %s" uu____9166))))
       in
    FStar_All.pipe_left (wrap_err "cases") uu____8934
  
let (set_options : Prims.string -> unit tac) =
  fun s  ->
    let uu____9197 =
      let uu____9200 = cur_goal ()  in
      bind uu____9200
        (fun g  ->
           FStar_Options.push ();
           (let uu____9213 = FStar_Util.smap_copy g.FStar_Tactics_Types.opts
               in
            FStar_Options.set uu____9213);
           (let res = FStar_Options.set_options FStar_Options.Set s  in
            let opts' = FStar_Options.peek ()  in
            FStar_Options.pop ();
            (match res with
             | FStar_Getopt.Success  ->
                 let g' =
                   let uu___400_9220 = g  in
                   {
                     FStar_Tactics_Types.goal_main_env =
                       (uu___400_9220.FStar_Tactics_Types.goal_main_env);
                     FStar_Tactics_Types.goal_ctx_uvar =
                       (uu___400_9220.FStar_Tactics_Types.goal_ctx_uvar);
                     FStar_Tactics_Types.opts = opts';
                     FStar_Tactics_Types.is_guard =
                       (uu___400_9220.FStar_Tactics_Types.is_guard)
                   }  in
                 replace_cur g'
             | FStar_Getopt.Error err ->
                 fail2 "Setting options `%s` failed: %s" s err
             | FStar_Getopt.Help  ->
                 fail1 "Setting options `%s` failed (got `Help`?)" s)))
       in
    FStar_All.pipe_left (wrap_err "set_options") uu____9197
  
let (top_env : unit -> env tac) =
  fun uu____9232  ->
    bind get
      (fun ps  -> FStar_All.pipe_left ret ps.FStar_Tactics_Types.main_context)
  
let (cur_env : unit -> env tac) =
  fun uu____9245  ->
    let uu____9248 = cur_goal ()  in
    bind uu____9248
      (fun g  ->
         let uu____9254 = FStar_Tactics_Types.goal_env g  in
         FStar_All.pipe_left ret uu____9254)
  
let (cur_goal' : unit -> FStar_Syntax_Syntax.term tac) =
  fun uu____9263  ->
    let uu____9266 = cur_goal ()  in
    bind uu____9266
      (fun g  ->
         let uu____9272 = FStar_Tactics_Types.goal_type g  in
         FStar_All.pipe_left ret uu____9272)
  
let (cur_witness : unit -> FStar_Syntax_Syntax.term tac) =
  fun uu____9281  ->
    let uu____9284 = cur_goal ()  in
    bind uu____9284
      (fun g  ->
         let uu____9290 = FStar_Tactics_Types.goal_witness g  in
         FStar_All.pipe_left ret uu____9290)
  
let (unquote :
  FStar_Reflection_Data.typ ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term tac)
  =
  fun ty  ->
    fun tm  ->
      let uu____9307 =
        mlog
          (fun uu____9312  ->
             let uu____9313 = FStar_Syntax_Print.term_to_string tm  in
             FStar_Util.print1 "unquote: tm = %s\n" uu____9313)
          (fun uu____9316  ->
             let uu____9317 = cur_goal ()  in
             bind uu____9317
               (fun goal  ->
                  let env =
                    let uu____9325 = FStar_Tactics_Types.goal_env goal  in
                    FStar_TypeChecker_Env.set_expected_typ uu____9325 ty  in
                  let uu____9326 = __tc env tm  in
                  bind uu____9326
                    (fun uu____9345  ->
                       match uu____9345 with
                       | (tm1,typ,guard) ->
                           mlog
                             (fun uu____9359  ->
                                let uu____9360 =
                                  FStar_Syntax_Print.term_to_string tm1  in
                                FStar_Util.print1 "unquote: tm' = %s\n"
                                  uu____9360)
                             (fun uu____9362  ->
                                mlog
                                  (fun uu____9365  ->
                                     let uu____9366 =
                                       FStar_Syntax_Print.term_to_string typ
                                        in
                                     FStar_Util.print1 "unquote: typ = %s\n"
                                       uu____9366)
                                  (fun uu____9369  ->
                                     let uu____9370 =
                                       proc_guard "unquote" env guard  in
                                     bind uu____9370
                                       (fun uu____9374  -> ret tm1))))))
         in
      FStar_All.pipe_left (wrap_err "unquote") uu____9307
  
let (uvar_env :
  env ->
    FStar_Reflection_Data.typ FStar_Pervasives_Native.option ->
      FStar_Syntax_Syntax.term tac)
  =
  fun env  ->
    fun ty  ->
      let uu____9397 =
        match ty with
        | FStar_Pervasives_Native.Some ty1 -> ret ty1
        | FStar_Pervasives_Native.None  ->
            let uu____9403 =
              let uu____9410 =
                let uu____9411 = FStar_Syntax_Util.type_u ()  in
                FStar_All.pipe_left FStar_Pervasives_Native.fst uu____9411
                 in
              new_uvar "uvar_env.2" env uu____9410  in
            bind uu____9403
              (fun uu____9427  ->
                 match uu____9427 with | (typ,uvar_typ) -> ret typ)
         in
      bind uu____9397
        (fun typ  ->
           let uu____9439 = new_uvar "uvar_env" env typ  in
           bind uu____9439
             (fun uu____9453  -> match uu____9453 with | (t,uvar_t) -> ret t))
  
let (unshelve : FStar_Syntax_Syntax.term -> unit tac) =
  fun t  ->
    let uu____9471 =
      bind get
        (fun ps  ->
           let env = ps.FStar_Tactics_Types.main_context  in
           let opts =
             match ps.FStar_Tactics_Types.goals with
             | g::uu____9490 -> g.FStar_Tactics_Types.opts
             | uu____9493 -> FStar_Options.peek ()  in
           let uu____9496 = FStar_Syntax_Util.head_and_args t  in
           match uu____9496 with
           | ({
                FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                  (ctx_uvar,uu____9514);
                FStar_Syntax_Syntax.pos = uu____9515;
                FStar_Syntax_Syntax.vars = uu____9516;_},uu____9517)
               ->
               let env1 =
                 let uu___401_9555 = env  in
                 {
                   FStar_TypeChecker_Env.solver =
                     (uu___401_9555.FStar_TypeChecker_Env.solver);
                   FStar_TypeChecker_Env.range =
                     (uu___401_9555.FStar_TypeChecker_Env.range);
                   FStar_TypeChecker_Env.curmodule =
                     (uu___401_9555.FStar_TypeChecker_Env.curmodule);
                   FStar_TypeChecker_Env.gamma =
                     (ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_gamma);
                   FStar_TypeChecker_Env.gamma_sig =
                     (uu___401_9555.FStar_TypeChecker_Env.gamma_sig);
                   FStar_TypeChecker_Env.gamma_cache =
                     (uu___401_9555.FStar_TypeChecker_Env.gamma_cache);
                   FStar_TypeChecker_Env.modules =
                     (uu___401_9555.FStar_TypeChecker_Env.modules);
                   FStar_TypeChecker_Env.expected_typ =
                     (uu___401_9555.FStar_TypeChecker_Env.expected_typ);
                   FStar_TypeChecker_Env.sigtab =
                     (uu___401_9555.FStar_TypeChecker_Env.sigtab);
                   FStar_TypeChecker_Env.is_pattern =
                     (uu___401_9555.FStar_TypeChecker_Env.is_pattern);
                   FStar_TypeChecker_Env.instantiate_imp =
                     (uu___401_9555.FStar_TypeChecker_Env.instantiate_imp);
                   FStar_TypeChecker_Env.effects =
                     (uu___401_9555.FStar_TypeChecker_Env.effects);
                   FStar_TypeChecker_Env.generalize =
                     (uu___401_9555.FStar_TypeChecker_Env.generalize);
                   FStar_TypeChecker_Env.letrecs =
                     (uu___401_9555.FStar_TypeChecker_Env.letrecs);
                   FStar_TypeChecker_Env.top_level =
                     (uu___401_9555.FStar_TypeChecker_Env.top_level);
                   FStar_TypeChecker_Env.check_uvars =
                     (uu___401_9555.FStar_TypeChecker_Env.check_uvars);
                   FStar_TypeChecker_Env.use_eq =
                     (uu___401_9555.FStar_TypeChecker_Env.use_eq);
                   FStar_TypeChecker_Env.is_iface =
                     (uu___401_9555.FStar_TypeChecker_Env.is_iface);
                   FStar_TypeChecker_Env.admit =
                     (uu___401_9555.FStar_TypeChecker_Env.admit);
                   FStar_TypeChecker_Env.lax =
                     (uu___401_9555.FStar_TypeChecker_Env.lax);
                   FStar_TypeChecker_Env.lax_universes =
                     (uu___401_9555.FStar_TypeChecker_Env.lax_universes);
                   FStar_TypeChecker_Env.failhard =
                     (uu___401_9555.FStar_TypeChecker_Env.failhard);
                   FStar_TypeChecker_Env.nosynth =
                     (uu___401_9555.FStar_TypeChecker_Env.nosynth);
                   FStar_TypeChecker_Env.uvar_subtyping =
                     (uu___401_9555.FStar_TypeChecker_Env.uvar_subtyping);
                   FStar_TypeChecker_Env.tc_term =
                     (uu___401_9555.FStar_TypeChecker_Env.tc_term);
                   FStar_TypeChecker_Env.type_of =
                     (uu___401_9555.FStar_TypeChecker_Env.type_of);
                   FStar_TypeChecker_Env.universe_of =
                     (uu___401_9555.FStar_TypeChecker_Env.universe_of);
                   FStar_TypeChecker_Env.check_type_of =
                     (uu___401_9555.FStar_TypeChecker_Env.check_type_of);
                   FStar_TypeChecker_Env.use_bv_sorts =
                     (uu___401_9555.FStar_TypeChecker_Env.use_bv_sorts);
                   FStar_TypeChecker_Env.qtbl_name_and_index =
                     (uu___401_9555.FStar_TypeChecker_Env.qtbl_name_and_index);
                   FStar_TypeChecker_Env.normalized_eff_names =
                     (uu___401_9555.FStar_TypeChecker_Env.normalized_eff_names);
                   FStar_TypeChecker_Env.proof_ns =
                     (uu___401_9555.FStar_TypeChecker_Env.proof_ns);
                   FStar_TypeChecker_Env.synth_hook =
                     (uu___401_9555.FStar_TypeChecker_Env.synth_hook);
                   FStar_TypeChecker_Env.splice =
                     (uu___401_9555.FStar_TypeChecker_Env.splice);
                   FStar_TypeChecker_Env.is_native_tactic =
                     (uu___401_9555.FStar_TypeChecker_Env.is_native_tactic);
                   FStar_TypeChecker_Env.identifier_info =
                     (uu___401_9555.FStar_TypeChecker_Env.identifier_info);
                   FStar_TypeChecker_Env.tc_hooks =
                     (uu___401_9555.FStar_TypeChecker_Env.tc_hooks);
                   FStar_TypeChecker_Env.dsenv =
                     (uu___401_9555.FStar_TypeChecker_Env.dsenv);
                   FStar_TypeChecker_Env.dep_graph =
                     (uu___401_9555.FStar_TypeChecker_Env.dep_graph)
                 }  in
               let g = FStar_Tactics_Types.mk_goal env1 ctx_uvar opts false
                  in
               let uu____9557 =
                 let uu____9560 = bnorm_goal g  in [uu____9560]  in
               add_goals uu____9557
           | uu____9561 -> fail "not a uvar")
       in
    FStar_All.pipe_left (wrap_err "unshelve") uu____9471
  
let (tac_and : Prims.bool tac -> Prims.bool tac -> Prims.bool tac) =
  fun t1  ->
    fun t2  ->
      let comp =
        bind t1
          (fun b  ->
             let uu____9608 = if b then t2 else ret false  in
             bind uu____9608 (fun b'  -> if b' then ret b' else fail ""))
         in
      let uu____9619 = trytac comp  in
      bind uu____9619
        (fun uu___341_9627  ->
           match uu___341_9627 with
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
        let uu____9653 =
          bind get
            (fun ps  ->
               let uu____9659 = __tc e t1  in
               bind uu____9659
                 (fun uu____9679  ->
                    match uu____9679 with
                    | (t11,ty1,g1) ->
                        let uu____9691 = __tc e t2  in
                        bind uu____9691
                          (fun uu____9711  ->
                             match uu____9711 with
                             | (t21,ty2,g2) ->
                                 let uu____9723 =
                                   proc_guard "unify_env g1" e g1  in
                                 bind uu____9723
                                   (fun uu____9728  ->
                                      let uu____9729 =
                                        proc_guard "unify_env g2" e g2  in
                                      bind uu____9729
                                        (fun uu____9735  ->
                                           let uu____9736 =
                                             do_unify e ty1 ty2  in
                                           let uu____9739 =
                                             do_unify e t11 t21  in
                                           tac_and uu____9736 uu____9739)))))
           in
        FStar_All.pipe_left (wrap_err "unify_env") uu____9653
  
let (launch_process :
  Prims.string -> Prims.string Prims.list -> Prims.string -> Prims.string tac)
  =
  fun prog  ->
    fun args  ->
      fun input  ->
        bind idtac
          (fun uu____9772  ->
             let uu____9773 = FStar_Options.unsafe_tactic_exec ()  in
             if uu____9773
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
        (fun uu____9794  ->
           let uu____9795 =
             FStar_Syntax_Syntax.gen_bv nm FStar_Pervasives_Native.None t  in
           ret uu____9795)
  
let (change : FStar_Reflection_Data.typ -> unit tac) =
  fun ty  ->
    let uu____9805 =
      mlog
        (fun uu____9810  ->
           let uu____9811 = FStar_Syntax_Print.term_to_string ty  in
           FStar_Util.print1 "change: ty = %s\n" uu____9811)
        (fun uu____9814  ->
           let uu____9815 = cur_goal ()  in
           bind uu____9815
             (fun g  ->
                let uu____9821 =
                  let uu____9830 = FStar_Tactics_Types.goal_env g  in
                  __tc uu____9830 ty  in
                bind uu____9821
                  (fun uu____9842  ->
                     match uu____9842 with
                     | (ty1,uu____9852,guard) ->
                         let uu____9854 =
                           let uu____9857 = FStar_Tactics_Types.goal_env g
                              in
                           proc_guard "change" uu____9857 guard  in
                         bind uu____9854
                           (fun uu____9860  ->
                              let uu____9861 =
                                let uu____9864 =
                                  FStar_Tactics_Types.goal_env g  in
                                let uu____9865 =
                                  FStar_Tactics_Types.goal_type g  in
                                do_unify uu____9864 uu____9865 ty1  in
                              bind uu____9861
                                (fun bb  ->
                                   if bb
                                   then
                                     let uu____9871 =
                                       FStar_Tactics_Types.goal_with_type g
                                         ty1
                                        in
                                     replace_cur uu____9871
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
                                        let uu____9877 =
                                          FStar_Tactics_Types.goal_env g  in
                                        let uu____9878 =
                                          FStar_Tactics_Types.goal_type g  in
                                        normalize steps uu____9877 uu____9878
                                         in
                                      let nty =
                                        let uu____9880 =
                                          FStar_Tactics_Types.goal_env g  in
                                        normalize steps uu____9880 ty1  in
                                      let uu____9881 =
                                        let uu____9884 =
                                          FStar_Tactics_Types.goal_env g  in
                                        do_unify uu____9884 ng nty  in
                                      bind uu____9881
                                        (fun b  ->
                                           if b
                                           then
                                             let uu____9890 =
                                               FStar_Tactics_Types.goal_with_type
                                                 g ty1
                                                in
                                             replace_cur uu____9890
                                           else fail "not convertible")))))))
       in
    FStar_All.pipe_left (wrap_err "change") uu____9805
  
let rec last : 'a . 'a Prims.list -> 'a =
  fun l  ->
    match l with
    | [] -> failwith "last: empty list"
    | x::[] -> x
    | uu____9912::xs -> last xs
  
let rec init : 'a . 'a Prims.list -> 'a Prims.list =
  fun l  ->
    match l with
    | [] -> failwith "init: empty list"
    | x::[] -> []
    | x::xs -> let uu____9940 = init xs  in x :: uu____9940
  
let rec (inspect :
  FStar_Syntax_Syntax.term -> FStar_Reflection_Data.term_view tac) =
  fun t  ->
    let uu____9952 =
      let t1 = FStar_Syntax_Util.unascribe t  in
      let t2 = FStar_Syntax_Util.un_uinst t1  in
      match t2.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_meta (t3,uu____9960) -> inspect t3
      | FStar_Syntax_Syntax.Tm_name bv ->
          FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_Var bv)
      | FStar_Syntax_Syntax.Tm_bvar bv ->
          FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_BVar bv)
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_FVar fv)
      | FStar_Syntax_Syntax.Tm_app (hd1,[]) ->
          failwith "empty arguments on Tm_app"
      | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
          let uu____10017 = last args  in
          (match uu____10017 with
           | (a,q) ->
               let q' = FStar_Reflection_Basic.inspect_aqual q  in
               let uu____10039 =
                 let uu____10040 =
                   let uu____10045 =
                     let uu____10046 =
                       let uu____10051 = init args  in
                       FStar_Syntax_Syntax.mk_Tm_app hd1 uu____10051  in
                     uu____10046 FStar_Pervasives_Native.None
                       t2.FStar_Syntax_Syntax.pos
                      in
                   (uu____10045, (a, q'))  in
                 FStar_Reflection_Data.Tv_App uu____10040  in
               FStar_All.pipe_left ret uu____10039)
      | FStar_Syntax_Syntax.Tm_abs ([],uu____10062,uu____10063) ->
          failwith "empty arguments on Tm_abs"
      | FStar_Syntax_Syntax.Tm_abs (bs,t3,k) ->
          let uu____10107 = FStar_Syntax_Subst.open_term bs t3  in
          (match uu____10107 with
           | (bs1,t4) ->
               (match bs1 with
                | [] -> failwith "impossible"
                | b::bs2 ->
                    let uu____10140 =
                      let uu____10141 =
                        let uu____10146 = FStar_Syntax_Util.abs bs2 t4 k  in
                        (b, uu____10146)  in
                      FStar_Reflection_Data.Tv_Abs uu____10141  in
                    FStar_All.pipe_left ret uu____10140))
      | FStar_Syntax_Syntax.Tm_type uu____10149 ->
          FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_Type ())
      | FStar_Syntax_Syntax.Tm_arrow ([],k) ->
          failwith "empty binders on arrow"
      | FStar_Syntax_Syntax.Tm_arrow uu____10169 ->
          let uu____10182 = FStar_Syntax_Util.arrow_one t2  in
          (match uu____10182 with
           | FStar_Pervasives_Native.Some (b,c) ->
               FStar_All.pipe_left ret
                 (FStar_Reflection_Data.Tv_Arrow (b, c))
           | FStar_Pervasives_Native.None  -> failwith "impossible")
      | FStar_Syntax_Syntax.Tm_refine (bv,t3) ->
          let b = FStar_Syntax_Syntax.mk_binder bv  in
          let uu____10212 = FStar_Syntax_Subst.open_term [b] t3  in
          (match uu____10212 with
           | (b',t4) ->
               let b1 =
                 match b' with
                 | b'1::[] -> b'1
                 | uu____10251 -> failwith "impossible"  in
               FStar_All.pipe_left ret
                 (FStar_Reflection_Data.Tv_Refine
                    ((FStar_Pervasives_Native.fst b1), t4)))
      | FStar_Syntax_Syntax.Tm_constant c ->
          let uu____10259 =
            let uu____10260 = FStar_Reflection_Basic.inspect_const c  in
            FStar_Reflection_Data.Tv_Const uu____10260  in
          FStar_All.pipe_left ret uu____10259
      | FStar_Syntax_Syntax.Tm_uvar (ctx_u,s) ->
          let uu____10281 =
            let uu____10282 =
              let uu____10287 =
                let uu____10288 =
                  FStar_Syntax_Unionfind.uvar_id
                    ctx_u.FStar_Syntax_Syntax.ctx_uvar_head
                   in
                FStar_BigInt.of_int_fs uu____10288  in
              (uu____10287, (ctx_u, s))  in
            FStar_Reflection_Data.Tv_Uvar uu____10282  in
          FStar_All.pipe_left ret uu____10281
      | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),t21) ->
          if lb.FStar_Syntax_Syntax.lbunivs <> []
          then FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown
          else
            (match lb.FStar_Syntax_Syntax.lbname with
             | FStar_Util.Inr uu____10322 ->
                 FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown
             | FStar_Util.Inl bv ->
                 let b = FStar_Syntax_Syntax.mk_binder bv  in
                 let uu____10327 = FStar_Syntax_Subst.open_term [b] t21  in
                 (match uu____10327 with
                  | (bs,t22) ->
                      let b1 =
                        match bs with
                        | b1::[] -> b1
                        | uu____10366 ->
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
             | FStar_Util.Inr uu____10396 ->
                 FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown
             | FStar_Util.Inl bv ->
                 let uu____10400 = FStar_Syntax_Subst.open_let_rec [lb] t21
                    in
                 (match uu____10400 with
                  | (lbs,t22) ->
                      (match lbs with
                       | lb1::[] ->
                           (match lb1.FStar_Syntax_Syntax.lbname with
                            | FStar_Util.Inr uu____10420 ->
                                ret FStar_Reflection_Data.Tv_Unknown
                            | FStar_Util.Inl bv1 ->
                                FStar_All.pipe_left ret
                                  (FStar_Reflection_Data.Tv_Let
                                     (true, bv1,
                                       (lb1.FStar_Syntax_Syntax.lbdef), t22)))
                       | uu____10424 ->
                           failwith
                             "impossible: open_term returned different amount of binders")))
      | FStar_Syntax_Syntax.Tm_match (t3,brs) ->
          let rec inspect_pat p =
            match p.FStar_Syntax_Syntax.v with
            | FStar_Syntax_Syntax.Pat_constant c ->
                let uu____10478 = FStar_Reflection_Basic.inspect_const c  in
                FStar_Reflection_Data.Pat_Constant uu____10478
            | FStar_Syntax_Syntax.Pat_cons (fv,ps) ->
                let uu____10497 =
                  let uu____10504 =
                    FStar_List.map
                      (fun uu____10516  ->
                         match uu____10516 with
                         | (p1,uu____10524) -> inspect_pat p1) ps
                     in
                  (fv, uu____10504)  in
                FStar_Reflection_Data.Pat_Cons uu____10497
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
              (fun uu___342_10618  ->
                 match uu___342_10618 with
                 | (pat,uu____10640,t4) ->
                     let uu____10658 = inspect_pat pat  in (uu____10658, t4))
              brs1
             in
          FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_Match (t3, brs2))
      | FStar_Syntax_Syntax.Tm_unknown  ->
          FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown
      | uu____10667 ->
          ((let uu____10669 =
              let uu____10674 =
                let uu____10675 = FStar_Syntax_Print.tag_of_term t2  in
                let uu____10676 = FStar_Syntax_Print.term_to_string t2  in
                FStar_Util.format2
                  "inspect: outside of expected syntax (%s, %s)\n"
                  uu____10675 uu____10676
                 in
              (FStar_Errors.Warning_CantInspect, uu____10674)  in
            FStar_Errors.log_issue t2.FStar_Syntax_Syntax.pos uu____10669);
           FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown)
       in
    wrap_err "inspect" uu____9952
  
let (pack : FStar_Reflection_Data.term_view -> FStar_Syntax_Syntax.term tac)
  =
  fun tv  ->
    match tv with
    | FStar_Reflection_Data.Tv_Var bv ->
        let uu____10689 = FStar_Syntax_Syntax.bv_to_name bv  in
        FStar_All.pipe_left ret uu____10689
    | FStar_Reflection_Data.Tv_BVar bv ->
        let uu____10693 = FStar_Syntax_Syntax.bv_to_tm bv  in
        FStar_All.pipe_left ret uu____10693
    | FStar_Reflection_Data.Tv_FVar fv ->
        let uu____10697 = FStar_Syntax_Syntax.fv_to_tm fv  in
        FStar_All.pipe_left ret uu____10697
    | FStar_Reflection_Data.Tv_App (l,(r,q)) ->
        let q' = FStar_Reflection_Basic.pack_aqual q  in
        let uu____10704 = FStar_Syntax_Util.mk_app l [(r, q')]  in
        FStar_All.pipe_left ret uu____10704
    | FStar_Reflection_Data.Tv_Abs (b,t) ->
        let uu____10723 =
          FStar_Syntax_Util.abs [b] t FStar_Pervasives_Native.None  in
        FStar_All.pipe_left ret uu____10723
    | FStar_Reflection_Data.Tv_Arrow (b,c) ->
        let uu____10736 = FStar_Syntax_Util.arrow [b] c  in
        FStar_All.pipe_left ret uu____10736
    | FStar_Reflection_Data.Tv_Type () ->
        FStar_All.pipe_left ret FStar_Syntax_Util.ktype
    | FStar_Reflection_Data.Tv_Refine (bv,t) ->
        let uu____10751 = FStar_Syntax_Util.refine bv t  in
        FStar_All.pipe_left ret uu____10751
    | FStar_Reflection_Data.Tv_Const c ->
        let uu____10755 =
          let uu____10756 =
            let uu____10763 =
              let uu____10764 = FStar_Reflection_Basic.pack_const c  in
              FStar_Syntax_Syntax.Tm_constant uu____10764  in
            FStar_Syntax_Syntax.mk uu____10763  in
          uu____10756 FStar_Pervasives_Native.None FStar_Range.dummyRange  in
        FStar_All.pipe_left ret uu____10755
    | FStar_Reflection_Data.Tv_Uvar (_u,ctx_u_s) ->
        let uu____10772 =
          FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_uvar ctx_u_s)
            FStar_Pervasives_Native.None FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____10772
    | FStar_Reflection_Data.Tv_Let (false ,bv,t1,t2) ->
        let lb =
          FStar_Syntax_Util.mk_letbinding (FStar_Util.Inl bv) []
            bv.FStar_Syntax_Syntax.sort FStar_Parser_Const.effect_Tot_lid t1
            [] FStar_Range.dummyRange
           in
        let uu____10781 =
          let uu____10782 =
            let uu____10789 =
              let uu____10790 =
                let uu____10803 =
                  let uu____10806 =
                    let uu____10807 = FStar_Syntax_Syntax.mk_binder bv  in
                    [uu____10807]  in
                  FStar_Syntax_Subst.close uu____10806 t2  in
                ((false, [lb]), uu____10803)  in
              FStar_Syntax_Syntax.Tm_let uu____10790  in
            FStar_Syntax_Syntax.mk uu____10789  in
          uu____10782 FStar_Pervasives_Native.None FStar_Range.dummyRange  in
        FStar_All.pipe_left ret uu____10781
    | FStar_Reflection_Data.Tv_Let (true ,bv,t1,t2) ->
        let lb =
          FStar_Syntax_Util.mk_letbinding (FStar_Util.Inl bv) []
            bv.FStar_Syntax_Syntax.sort FStar_Parser_Const.effect_Tot_lid t1
            [] FStar_Range.dummyRange
           in
        let uu____10841 = FStar_Syntax_Subst.close_let_rec [lb] t2  in
        (match uu____10841 with
         | (lbs,body) ->
             let uu____10856 =
               FStar_Syntax_Syntax.mk
                 (FStar_Syntax_Syntax.Tm_let ((true, lbs), body))
                 FStar_Pervasives_Native.None FStar_Range.dummyRange
                in
             FStar_All.pipe_left ret uu____10856)
    | FStar_Reflection_Data.Tv_Match (t,brs) ->
        let wrap v1 =
          {
            FStar_Syntax_Syntax.v = v1;
            FStar_Syntax_Syntax.p = FStar_Range.dummyRange
          }  in
        let rec pack_pat p =
          match p with
          | FStar_Reflection_Data.Pat_Constant c ->
              let uu____10890 =
                let uu____10891 = FStar_Reflection_Basic.pack_const c  in
                FStar_Syntax_Syntax.Pat_constant uu____10891  in
              FStar_All.pipe_left wrap uu____10890
          | FStar_Reflection_Data.Pat_Cons (fv,ps) ->
              let uu____10898 =
                let uu____10899 =
                  let uu____10912 =
                    FStar_List.map
                      (fun p1  ->
                         let uu____10928 = pack_pat p1  in
                         (uu____10928, false)) ps
                     in
                  (fv, uu____10912)  in
                FStar_Syntax_Syntax.Pat_cons uu____10899  in
              FStar_All.pipe_left wrap uu____10898
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
            (fun uu___343_10974  ->
               match uu___343_10974 with
               | (pat,t1) ->
                   let uu____10991 = pack_pat pat  in
                   (uu____10991, FStar_Pervasives_Native.None, t1)) brs
           in
        let brs2 = FStar_List.map FStar_Syntax_Subst.close_branch brs1  in
        let uu____11039 =
          FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_match (t, brs2))
            FStar_Pervasives_Native.None FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____11039
    | FStar_Reflection_Data.Tv_AscribedT (e,t,tacopt) ->
        let uu____11067 =
          FStar_Syntax_Syntax.mk
            (FStar_Syntax_Syntax.Tm_ascribed
               (e, ((FStar_Util.Inl t), tacopt),
                 FStar_Pervasives_Native.None)) FStar_Pervasives_Native.None
            FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____11067
    | FStar_Reflection_Data.Tv_AscribedC (e,c,tacopt) ->
        let uu____11113 =
          FStar_Syntax_Syntax.mk
            (FStar_Syntax_Syntax.Tm_ascribed
               (e, ((FStar_Util.Inr c), tacopt),
                 FStar_Pervasives_Native.None)) FStar_Pervasives_Native.None
            FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____11113
    | FStar_Reflection_Data.Tv_Unknown  ->
        let uu____11152 =
          FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown
            FStar_Pervasives_Native.None FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____11152
  
let (goal_of_goal_ty :
  env ->
    FStar_Reflection_Data.typ ->
      (FStar_Tactics_Types.goal,FStar_TypeChecker_Env.guard_t)
        FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun typ  ->
      let uu____11173 =
        FStar_TypeChecker_Util.new_implicit_var "proofstate_of_goal_ty"
          typ.FStar_Syntax_Syntax.pos env typ
         in
      match uu____11173 with
      | (u,ctx_uvars,g_u) ->
          let uu____11205 = FStar_List.hd ctx_uvars  in
          (match uu____11205 with
           | (ctx_uvar,uu____11219) ->
               let g =
                 let uu____11221 = FStar_Options.peek ()  in
                 FStar_Tactics_Types.mk_goal env ctx_uvar uu____11221 false
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
        let uu____11241 = goal_of_goal_ty env typ  in
        match uu____11241 with
        | (g,g_u) ->
            let ps =
              let uu____11253 =
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
                FStar_Tactics_Types.tac_verb_dbg = uu____11253
              }  in
            let uu____11258 = FStar_Tactics_Types.goal_witness g  in
            (ps, uu____11258)
  