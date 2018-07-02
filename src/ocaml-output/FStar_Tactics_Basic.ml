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
      try (fun uu___345_158  -> match () with | () -> t.tac_f p) ()
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
         try
           (fun uu___348_1105  ->
              match () with
              | () -> let uu____1110 = trytac t  in run uu____1110 ps) ()
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
           (fun uu___350_1222  ->
              match () with
              | () ->
                  let res = FStar_TypeChecker_Rel.teq_nosmt env t1 t2  in
                  ((let uu____1227 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "1346")
                       in
                    if uu____1227
                    then
                      let uu____1228 = FStar_Util.string_of_bool res  in
                      let uu____1229 = FStar_Syntax_Print.term_to_string t1
                         in
                      let uu____1230 = FStar_Syntax_Print.term_to_string t2
                         in
                      FStar_Util.print3
                        "%%%%%%%%do_unify (RESULT %s) %s =? %s\n" uu____1228
                        uu____1229 uu____1230
                    else ());
                   ret res)) ()
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
         ((let uu____1537 =
             let uu____1538 = FStar_Tactics_Types.goal_type g  in
             uu____1538.FStar_Syntax_Syntax.pos  in
           let uu____1541 =
             let uu____1546 =
               let uu____1547 = goal_to_string_verbose g  in
               FStar_Util.format1
                 "The following goal is ill-formed. Keeping calm and carrying on...\n<%s>\n\n"
                 uu____1547
                in
             (FStar_Errors.Warning_IllFormedGoal, uu____1546)  in
           FStar_Errors.log_issue uu____1537 uu____1541);
          (let uu____1548 =
             let uu____1549 = FStar_ST.op_Bang nwarn  in
             uu____1549 + (Prims.parse_int "1")  in
           FStar_ST.op_Colon_Equals nwarn uu____1548))
       else ())
    else ()
  
let (add_goals : FStar_Tactics_Types.goal Prims.list -> unit tac) =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___354_1609 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___354_1609.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___354_1609.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___354_1609.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (FStar_List.append gs p.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (uu___354_1609.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___354_1609.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___354_1609.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___354_1609.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___354_1609.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___354_1609.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___354_1609.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___354_1609.FStar_Tactics_Types.tac_verb_dbg)
            }))
  
let (add_smt_goals : FStar_Tactics_Types.goal Prims.list -> unit tac) =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___355_1629 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___355_1629.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___355_1629.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___355_1629.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___355_1629.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (FStar_List.append gs p.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___355_1629.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___355_1629.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___355_1629.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___355_1629.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___355_1629.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___355_1629.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___355_1629.FStar_Tactics_Types.tac_verb_dbg)
            }))
  
let (push_goals : FStar_Tactics_Types.goal Prims.list -> unit tac) =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___356_1649 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___356_1649.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___356_1649.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___356_1649.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (FStar_List.append p.FStar_Tactics_Types.goals gs);
              FStar_Tactics_Types.smt_goals =
                (uu___356_1649.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___356_1649.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___356_1649.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___356_1649.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___356_1649.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___356_1649.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___356_1649.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___356_1649.FStar_Tactics_Types.tac_verb_dbg)
            }))
  
let (push_smt_goals : FStar_Tactics_Types.goal Prims.list -> unit tac) =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___357_1669 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___357_1669.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___357_1669.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___357_1669.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___357_1669.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (FStar_List.append p.FStar_Tactics_Types.smt_goals gs);
              FStar_Tactics_Types.depth =
                (uu___357_1669.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___357_1669.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___357_1669.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___357_1669.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___357_1669.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___357_1669.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___357_1669.FStar_Tactics_Types.tac_verb_dbg)
            }))
  
let (replace_cur : FStar_Tactics_Types.goal -> unit tac) =
  fun g  -> bind __dismiss (fun uu____1680  -> add_goals [g]) 
let (add_implicits : implicits -> unit tac) =
  fun i  ->
    bind get
      (fun p  ->
         set
           (let uu___358_1694 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___358_1694.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___358_1694.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (FStar_List.append i p.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___358_1694.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (uu___358_1694.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___358_1694.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___358_1694.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___358_1694.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___358_1694.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___358_1694.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___358_1694.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___358_1694.FStar_Tactics_Types.tac_verb_dbg)
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
        let uu____1730 =
          FStar_TypeChecker_Util.new_implicit_var reason
            typ.FStar_Syntax_Syntax.pos env typ
           in
        match uu____1730 with
        | (u,ctx_uvar,g_u) ->
            let uu____1764 =
              add_implicits g_u.FStar_TypeChecker_Env.implicits  in
            bind uu____1764
              (fun uu____1773  ->
                 let uu____1774 =
                   let uu____1779 =
                     let uu____1780 = FStar_List.hd ctx_uvar  in
                     FStar_Pervasives_Native.fst uu____1780  in
                   (u, uu____1779)  in
                 ret uu____1774)
  
let (is_true : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____1798 = FStar_Syntax_Util.un_squash t  in
    match uu____1798 with
    | FStar_Pervasives_Native.Some t' ->
        let uu____1808 =
          let uu____1809 = FStar_Syntax_Subst.compress t'  in
          uu____1809.FStar_Syntax_Syntax.n  in
        (match uu____1808 with
         | FStar_Syntax_Syntax.Tm_fvar fv ->
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.true_lid
         | uu____1813 -> false)
    | uu____1814 -> false
  
let (is_false : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____1824 = FStar_Syntax_Util.un_squash t  in
    match uu____1824 with
    | FStar_Pervasives_Native.Some t' ->
        let uu____1834 =
          let uu____1835 = FStar_Syntax_Subst.compress t'  in
          uu____1835.FStar_Syntax_Syntax.n  in
        (match uu____1834 with
         | FStar_Syntax_Syntax.Tm_fvar fv ->
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.false_lid
         | uu____1839 -> false)
    | uu____1840 -> false
  
let (cur_goal : unit -> FStar_Tactics_Types.goal tac) =
  fun uu____1851  ->
    bind get
      (fun p  ->
         match p.FStar_Tactics_Types.goals with
         | [] -> fail "No more goals (1)"
         | hd1::tl1 ->
             let uu____1862 =
               FStar_Syntax_Unionfind.find
                 (hd1.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_head
                in
             (match uu____1862 with
              | FStar_Pervasives_Native.None  -> ret hd1
              | FStar_Pervasives_Native.Some t ->
                  ((let uu____1869 = goal_to_string_verbose hd1  in
                    let uu____1870 = FStar_Syntax_Print.term_to_string t  in
                    FStar_Util.print2
                      "!!!!!!!!!!!! GOAL IS ALREADY SOLVED! %s\nsol is %s\n"
                      uu____1869 uu____1870);
                   ret hd1)))
  
let (tadmit : unit -> unit tac) =
  fun uu____1877  ->
    let uu____1880 =
      bind get
        (fun ps  ->
           let uu____1886 = cur_goal ()  in
           bind uu____1886
             (fun g  ->
                (let uu____1893 =
                   let uu____1894 = FStar_Tactics_Types.goal_type g  in
                   uu____1894.FStar_Syntax_Syntax.pos  in
                 let uu____1897 =
                   let uu____1902 =
                     let uu____1903 = goal_to_string ps g  in
                     FStar_Util.format1 "Tactics admitted goal <%s>\n\n"
                       uu____1903
                      in
                   (FStar_Errors.Warning_TacAdmit, uu____1902)  in
                 FStar_Errors.log_issue uu____1893 uu____1897);
                solve' g FStar_Syntax_Util.exp_unit))
       in
    FStar_All.pipe_left (wrap_err "tadmit") uu____1880
  
let (fresh : unit -> FStar_BigInt.t tac) =
  fun uu____1914  ->
    bind get
      (fun ps  ->
         let n1 = ps.FStar_Tactics_Types.freshness  in
         let ps1 =
           let uu___359_1924 = ps  in
           {
             FStar_Tactics_Types.main_context =
               (uu___359_1924.FStar_Tactics_Types.main_context);
             FStar_Tactics_Types.main_goal =
               (uu___359_1924.FStar_Tactics_Types.main_goal);
             FStar_Tactics_Types.all_implicits =
               (uu___359_1924.FStar_Tactics_Types.all_implicits);
             FStar_Tactics_Types.goals =
               (uu___359_1924.FStar_Tactics_Types.goals);
             FStar_Tactics_Types.smt_goals =
               (uu___359_1924.FStar_Tactics_Types.smt_goals);
             FStar_Tactics_Types.depth =
               (uu___359_1924.FStar_Tactics_Types.depth);
             FStar_Tactics_Types.__dump =
               (uu___359_1924.FStar_Tactics_Types.__dump);
             FStar_Tactics_Types.psc =
               (uu___359_1924.FStar_Tactics_Types.psc);
             FStar_Tactics_Types.entry_range =
               (uu___359_1924.FStar_Tactics_Types.entry_range);
             FStar_Tactics_Types.guard_policy =
               (uu___359_1924.FStar_Tactics_Types.guard_policy);
             FStar_Tactics_Types.freshness = (n1 + (Prims.parse_int "1"));
             FStar_Tactics_Types.tac_verb_dbg =
               (uu___359_1924.FStar_Tactics_Types.tac_verb_dbg)
           }  in
         let uu____1925 = set ps1  in
         bind uu____1925
           (fun uu____1930  ->
              let uu____1931 = FStar_BigInt.of_int_fs n1  in ret uu____1931))
  
let (ngoals : unit -> FStar_BigInt.t tac) =
  fun uu____1938  ->
    bind get
      (fun ps  ->
         let n1 = FStar_List.length ps.FStar_Tactics_Types.goals  in
         let uu____1946 = FStar_BigInt.of_int_fs n1  in ret uu____1946)
  
let (ngoals_smt : unit -> FStar_BigInt.t tac) =
  fun uu____1959  ->
    bind get
      (fun ps  ->
         let n1 = FStar_List.length ps.FStar_Tactics_Types.smt_goals  in
         let uu____1967 = FStar_BigInt.of_int_fs n1  in ret uu____1967)
  
let (is_guard : unit -> Prims.bool tac) =
  fun uu____1980  ->
    let uu____1983 = cur_goal ()  in
    bind uu____1983 (fun g  -> ret g.FStar_Tactics_Types.is_guard)
  
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
            let uu____2015 = env.FStar_TypeChecker_Env.universe_of env phi
               in
            FStar_Syntax_Util.mk_squash uu____2015 phi  in
          let uu____2016 = new_uvar reason env typ  in
          bind uu____2016
            (fun uu____2031  ->
               match uu____2031 with
               | (uu____2038,ctx_uvar) ->
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
             (fun uu____2083  ->
                let uu____2084 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.print1 "Tac> __tc(%s)\n" uu____2084)
             (fun uu____2087  ->
                let e1 =
                  let uu___360_2089 = e  in
                  {
                    FStar_TypeChecker_Env.solver =
                      (uu___360_2089.FStar_TypeChecker_Env.solver);
                    FStar_TypeChecker_Env.range =
                      (uu___360_2089.FStar_TypeChecker_Env.range);
                    FStar_TypeChecker_Env.curmodule =
                      (uu___360_2089.FStar_TypeChecker_Env.curmodule);
                    FStar_TypeChecker_Env.gamma =
                      (uu___360_2089.FStar_TypeChecker_Env.gamma);
                    FStar_TypeChecker_Env.gamma_sig =
                      (uu___360_2089.FStar_TypeChecker_Env.gamma_sig);
                    FStar_TypeChecker_Env.gamma_cache =
                      (uu___360_2089.FStar_TypeChecker_Env.gamma_cache);
                    FStar_TypeChecker_Env.modules =
                      (uu___360_2089.FStar_TypeChecker_Env.modules);
                    FStar_TypeChecker_Env.expected_typ =
                      (uu___360_2089.FStar_TypeChecker_Env.expected_typ);
                    FStar_TypeChecker_Env.sigtab =
                      (uu___360_2089.FStar_TypeChecker_Env.sigtab);
                    FStar_TypeChecker_Env.is_pattern =
                      (uu___360_2089.FStar_TypeChecker_Env.is_pattern);
                    FStar_TypeChecker_Env.instantiate_imp =
                      (uu___360_2089.FStar_TypeChecker_Env.instantiate_imp);
                    FStar_TypeChecker_Env.effects =
                      (uu___360_2089.FStar_TypeChecker_Env.effects);
                    FStar_TypeChecker_Env.generalize =
                      (uu___360_2089.FStar_TypeChecker_Env.generalize);
                    FStar_TypeChecker_Env.letrecs =
                      (uu___360_2089.FStar_TypeChecker_Env.letrecs);
                    FStar_TypeChecker_Env.top_level =
                      (uu___360_2089.FStar_TypeChecker_Env.top_level);
                    FStar_TypeChecker_Env.check_uvars =
                      (uu___360_2089.FStar_TypeChecker_Env.check_uvars);
                    FStar_TypeChecker_Env.use_eq =
                      (uu___360_2089.FStar_TypeChecker_Env.use_eq);
                    FStar_TypeChecker_Env.is_iface =
                      (uu___360_2089.FStar_TypeChecker_Env.is_iface);
                    FStar_TypeChecker_Env.admit =
                      (uu___360_2089.FStar_TypeChecker_Env.admit);
                    FStar_TypeChecker_Env.lax =
                      (uu___360_2089.FStar_TypeChecker_Env.lax);
                    FStar_TypeChecker_Env.lax_universes =
                      (uu___360_2089.FStar_TypeChecker_Env.lax_universes);
                    FStar_TypeChecker_Env.failhard =
                      (uu___360_2089.FStar_TypeChecker_Env.failhard);
                    FStar_TypeChecker_Env.nosynth =
                      (uu___360_2089.FStar_TypeChecker_Env.nosynth);
                    FStar_TypeChecker_Env.uvar_subtyping = false;
                    FStar_TypeChecker_Env.tc_term =
                      (uu___360_2089.FStar_TypeChecker_Env.tc_term);
                    FStar_TypeChecker_Env.type_of =
                      (uu___360_2089.FStar_TypeChecker_Env.type_of);
                    FStar_TypeChecker_Env.universe_of =
                      (uu___360_2089.FStar_TypeChecker_Env.universe_of);
                    FStar_TypeChecker_Env.check_type_of =
                      (uu___360_2089.FStar_TypeChecker_Env.check_type_of);
                    FStar_TypeChecker_Env.use_bv_sorts =
                      (uu___360_2089.FStar_TypeChecker_Env.use_bv_sorts);
                    FStar_TypeChecker_Env.qtbl_name_and_index =
                      (uu___360_2089.FStar_TypeChecker_Env.qtbl_name_and_index);
                    FStar_TypeChecker_Env.normalized_eff_names =
                      (uu___360_2089.FStar_TypeChecker_Env.normalized_eff_names);
                    FStar_TypeChecker_Env.proof_ns =
                      (uu___360_2089.FStar_TypeChecker_Env.proof_ns);
                    FStar_TypeChecker_Env.synth_hook =
                      (uu___360_2089.FStar_TypeChecker_Env.synth_hook);
                    FStar_TypeChecker_Env.splice =
                      (uu___360_2089.FStar_TypeChecker_Env.splice);
                    FStar_TypeChecker_Env.is_native_tactic =
                      (uu___360_2089.FStar_TypeChecker_Env.is_native_tactic);
                    FStar_TypeChecker_Env.identifier_info =
                      (uu___360_2089.FStar_TypeChecker_Env.identifier_info);
                    FStar_TypeChecker_Env.tc_hooks =
                      (uu___360_2089.FStar_TypeChecker_Env.tc_hooks);
                    FStar_TypeChecker_Env.dsenv =
                      (uu___360_2089.FStar_TypeChecker_Env.dsenv);
                    FStar_TypeChecker_Env.dep_graph =
                      (uu___360_2089.FStar_TypeChecker_Env.dep_graph)
                  }  in
                try
                  (fun uu___362_2100  ->
                     match () with
                     | () ->
                         let uu____2109 =
                           (ps.FStar_Tactics_Types.main_context).FStar_TypeChecker_Env.type_of
                             e1 t
                            in
                         ret uu____2109) ()
                with
                | FStar_Errors.Err (uu____2136,msg) ->
                    let uu____2138 = tts e1 t  in
                    let uu____2139 =
                      let uu____2140 = FStar_TypeChecker_Env.all_binders e1
                         in
                      FStar_All.pipe_right uu____2140
                        (FStar_Syntax_Print.binders_to_string ", ")
                       in
                    fail3 "Cannot type %s in context (%s). Error = (%s)"
                      uu____2138 uu____2139 msg
                | FStar_Errors.Error (uu____2147,msg,uu____2149) ->
                    let uu____2150 = tts e1 t  in
                    let uu____2151 =
                      let uu____2152 = FStar_TypeChecker_Env.all_binders e1
                         in
                      FStar_All.pipe_right uu____2152
                        (FStar_Syntax_Print.binders_to_string ", ")
                       in
                    fail3 "Cannot type %s in context (%s). Error = (%s)"
                      uu____2150 uu____2151 msg))
  
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
  fun uu____2179  ->
    bind get (fun ps  -> ret ps.FStar_Tactics_Types.guard_policy)
  
let (set_guard_policy : FStar_Tactics_Types.guard_policy -> unit tac) =
  fun pol  ->
    bind get
      (fun ps  ->
         set
           (let uu___363_2197 = ps  in
            {
              FStar_Tactics_Types.main_context =
                (uu___363_2197.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___363_2197.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___363_2197.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___363_2197.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (uu___363_2197.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___363_2197.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___363_2197.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___363_2197.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___363_2197.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy = pol;
              FStar_Tactics_Types.freshness =
                (uu___363_2197.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___363_2197.FStar_Tactics_Types.tac_verb_dbg)
            }))
  
let with_policy : 'a . FStar_Tactics_Types.guard_policy -> 'a tac -> 'a tac =
  fun pol  ->
    fun t  ->
      let uu____2221 = get_guard_policy ()  in
      bind uu____2221
        (fun old_pol  ->
           let uu____2227 = set_guard_policy pol  in
           bind uu____2227
             (fun uu____2231  ->
                bind t
                  (fun r  ->
                     let uu____2235 = set_guard_policy old_pol  in
                     bind uu____2235 (fun uu____2239  -> ret r))))
  
let (getopts : FStar_Options.optionstate tac) =
  let uu____2242 = let uu____2247 = cur_goal ()  in trytac uu____2247  in
  bind uu____2242
    (fun uu___336_2254  ->
       match uu___336_2254 with
       | FStar_Pervasives_Native.Some g -> ret g.FStar_Tactics_Types.opts
       | FStar_Pervasives_Native.None  ->
           let uu____2260 = FStar_Options.peek ()  in ret uu____2260)
  
let (proc_guard :
  Prims.string -> env -> FStar_TypeChecker_Env.guard_t -> unit tac) =
  fun reason  ->
    fun e  ->
      fun g  ->
        bind getopts
          (fun opts  ->
             let uu____2283 =
               let uu____2284 = FStar_TypeChecker_Rel.simplify_guard e g  in
               uu____2284.FStar_TypeChecker_Env.guard_f  in
             match uu____2283 with
             | FStar_TypeChecker_Common.Trivial  -> ret ()
             | FStar_TypeChecker_Common.NonTrivial f ->
                 let uu____2288 = istrivial e f  in
                 if uu____2288
                 then ret ()
                 else
                   bind get
                     (fun ps  ->
                        match ps.FStar_Tactics_Types.guard_policy with
                        | FStar_Tactics_Types.Drop  -> ret ()
                        | FStar_Tactics_Types.Goal  ->
                            let uu____2296 =
                              mk_irrelevant_goal reason e f opts  in
                            bind uu____2296
                              (fun goal  ->
                                 let goal1 =
                                   let uu___364_2303 = goal  in
                                   {
                                     FStar_Tactics_Types.goal_main_env =
                                       (uu___364_2303.FStar_Tactics_Types.goal_main_env);
                                     FStar_Tactics_Types.goal_ctx_uvar =
                                       (uu___364_2303.FStar_Tactics_Types.goal_ctx_uvar);
                                     FStar_Tactics_Types.opts =
                                       (uu___364_2303.FStar_Tactics_Types.opts);
                                     FStar_Tactics_Types.is_guard = true
                                   }  in
                                 push_goals [goal1])
                        | FStar_Tactics_Types.SMT  ->
                            let uu____2304 =
                              mk_irrelevant_goal reason e f opts  in
                            bind uu____2304
                              (fun goal  ->
                                 let goal1 =
                                   let uu___365_2311 = goal  in
                                   {
                                     FStar_Tactics_Types.goal_main_env =
                                       (uu___365_2311.FStar_Tactics_Types.goal_main_env);
                                     FStar_Tactics_Types.goal_ctx_uvar =
                                       (uu___365_2311.FStar_Tactics_Types.goal_ctx_uvar);
                                     FStar_Tactics_Types.opts =
                                       (uu___365_2311.FStar_Tactics_Types.opts);
                                     FStar_Tactics_Types.is_guard = true
                                   }  in
                                 push_smt_goals [goal1])
                        | FStar_Tactics_Types.Force  ->
                            (try
                               (fun uu___367_2316  ->
                                  match () with
                                  | () ->
                                      let uu____2319 =
                                        let uu____2320 =
                                          let uu____2321 =
                                            FStar_TypeChecker_Rel.discharge_guard_no_smt
                                              e g
                                             in
                                          FStar_All.pipe_left
                                            FStar_TypeChecker_Rel.is_trivial
                                            uu____2321
                                           in
                                        Prims.op_Negation uu____2320  in
                                      if uu____2319
                                      then
                                        mlog
                                          (fun uu____2326  ->
                                             let uu____2327 =
                                               FStar_TypeChecker_Rel.guard_to_string
                                                 e g
                                                in
                                             FStar_Util.print1 "guard = %s\n"
                                               uu____2327)
                                          (fun uu____2329  ->
                                             fail1
                                               "Forcing the guard failed %s)"
                                               reason)
                                      else ret ()) ()
                             with
                             | uu____2336 ->
                                 mlog
                                   (fun uu____2339  ->
                                      let uu____2340 =
                                        FStar_TypeChecker_Rel.guard_to_string
                                          e g
                                         in
                                      FStar_Util.print1 "guard = %s\n"
                                        uu____2340)
                                   (fun uu____2342  ->
                                      fail1 "Forcing the guard failed (%s)"
                                        reason))))
  
let (tc : FStar_Syntax_Syntax.term -> FStar_Reflection_Data.typ tac) =
  fun t  ->
    let uu____2352 =
      let uu____2355 = cur_goal ()  in
      bind uu____2355
        (fun goal  ->
           let uu____2361 =
             let uu____2370 = FStar_Tactics_Types.goal_env goal  in
             __tc uu____2370 t  in
           bind uu____2361
             (fun uu____2382  ->
                match uu____2382 with
                | (t1,typ,guard) ->
                    let uu____2394 =
                      let uu____2397 = FStar_Tactics_Types.goal_env goal  in
                      proc_guard "tc" uu____2397 guard  in
                    bind uu____2394 (fun uu____2399  -> ret typ)))
       in
    FStar_All.pipe_left (wrap_err "tc") uu____2352
  
let (add_irrelevant_goal :
  Prims.string ->
    env -> FStar_Reflection_Data.typ -> FStar_Options.optionstate -> unit tac)
  =
  fun reason  ->
    fun env  ->
      fun phi  ->
        fun opts  ->
          let uu____2428 = mk_irrelevant_goal reason env phi opts  in
          bind uu____2428 (fun goal  -> add_goals [goal])
  
let (trivial : unit -> unit tac) =
  fun uu____2439  ->
    let uu____2442 = cur_goal ()  in
    bind uu____2442
      (fun goal  ->
         let uu____2448 =
           let uu____2449 = FStar_Tactics_Types.goal_env goal  in
           let uu____2450 = FStar_Tactics_Types.goal_type goal  in
           istrivial uu____2449 uu____2450  in
         if uu____2448
         then solve' goal FStar_Syntax_Util.exp_unit
         else
           (let uu____2454 =
              let uu____2455 = FStar_Tactics_Types.goal_env goal  in
              let uu____2456 = FStar_Tactics_Types.goal_type goal  in
              tts uu____2455 uu____2456  in
            fail1 "Not a trivial goal: %s" uu____2454))
  
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
          let uu____2485 =
            let uu____2486 = FStar_TypeChecker_Rel.simplify_guard e g  in
            uu____2486.FStar_TypeChecker_Env.guard_f  in
          match uu____2485 with
          | FStar_TypeChecker_Common.Trivial  ->
              ret FStar_Pervasives_Native.None
          | FStar_TypeChecker_Common.NonTrivial f ->
              let uu____2494 = istrivial e f  in
              if uu____2494
              then ret FStar_Pervasives_Native.None
              else
                (let uu____2502 = mk_irrelevant_goal reason e f opts  in
                 bind uu____2502
                   (fun goal  ->
                      ret
                        (FStar_Pervasives_Native.Some
                           (let uu___368_2512 = goal  in
                            {
                              FStar_Tactics_Types.goal_main_env =
                                (uu___368_2512.FStar_Tactics_Types.goal_main_env);
                              FStar_Tactics_Types.goal_ctx_uvar =
                                (uu___368_2512.FStar_Tactics_Types.goal_ctx_uvar);
                              FStar_Tactics_Types.opts =
                                (uu___368_2512.FStar_Tactics_Types.opts);
                              FStar_Tactics_Types.is_guard = true
                            }))))
  
let (smt : unit -> unit tac) =
  fun uu____2519  ->
    let uu____2522 = cur_goal ()  in
    bind uu____2522
      (fun g  ->
         let uu____2528 = is_irrelevant g  in
         if uu____2528
         then bind __dismiss (fun uu____2532  -> add_smt_goals [g])
         else
           (let uu____2534 =
              let uu____2535 = FStar_Tactics_Types.goal_env g  in
              let uu____2536 = FStar_Tactics_Types.goal_type g  in
              tts uu____2535 uu____2536  in
            fail1 "goal is not irrelevant: cannot dispatch to smt (%s)"
              uu____2534))
  
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
             let uu____2585 =
               try
                 (fun uu___373_2608  ->
                    match () with
                    | () ->
                        let uu____2619 =
                          let uu____2628 = FStar_BigInt.to_int_fs n1  in
                          FStar_List.splitAt uu____2628
                            p.FStar_Tactics_Types.goals
                           in
                        ret uu____2619) ()
               with | uu____2650 -> fail "divide: not enough goals"  in
             bind uu____2585
               (fun uu____2677  ->
                  match uu____2677 with
                  | (lgs,rgs) ->
                      let lp =
                        let uu___369_2703 = p  in
                        {
                          FStar_Tactics_Types.main_context =
                            (uu___369_2703.FStar_Tactics_Types.main_context);
                          FStar_Tactics_Types.main_goal =
                            (uu___369_2703.FStar_Tactics_Types.main_goal);
                          FStar_Tactics_Types.all_implicits =
                            (uu___369_2703.FStar_Tactics_Types.all_implicits);
                          FStar_Tactics_Types.goals = lgs;
                          FStar_Tactics_Types.smt_goals = [];
                          FStar_Tactics_Types.depth =
                            (uu___369_2703.FStar_Tactics_Types.depth);
                          FStar_Tactics_Types.__dump =
                            (uu___369_2703.FStar_Tactics_Types.__dump);
                          FStar_Tactics_Types.psc =
                            (uu___369_2703.FStar_Tactics_Types.psc);
                          FStar_Tactics_Types.entry_range =
                            (uu___369_2703.FStar_Tactics_Types.entry_range);
                          FStar_Tactics_Types.guard_policy =
                            (uu___369_2703.FStar_Tactics_Types.guard_policy);
                          FStar_Tactics_Types.freshness =
                            (uu___369_2703.FStar_Tactics_Types.freshness);
                          FStar_Tactics_Types.tac_verb_dbg =
                            (uu___369_2703.FStar_Tactics_Types.tac_verb_dbg)
                        }  in
                      let rp =
                        let uu___370_2705 = p  in
                        {
                          FStar_Tactics_Types.main_context =
                            (uu___370_2705.FStar_Tactics_Types.main_context);
                          FStar_Tactics_Types.main_goal =
                            (uu___370_2705.FStar_Tactics_Types.main_goal);
                          FStar_Tactics_Types.all_implicits =
                            (uu___370_2705.FStar_Tactics_Types.all_implicits);
                          FStar_Tactics_Types.goals = rgs;
                          FStar_Tactics_Types.smt_goals = [];
                          FStar_Tactics_Types.depth =
                            (uu___370_2705.FStar_Tactics_Types.depth);
                          FStar_Tactics_Types.__dump =
                            (uu___370_2705.FStar_Tactics_Types.__dump);
                          FStar_Tactics_Types.psc =
                            (uu___370_2705.FStar_Tactics_Types.psc);
                          FStar_Tactics_Types.entry_range =
                            (uu___370_2705.FStar_Tactics_Types.entry_range);
                          FStar_Tactics_Types.guard_policy =
                            (uu___370_2705.FStar_Tactics_Types.guard_policy);
                          FStar_Tactics_Types.freshness =
                            (uu___370_2705.FStar_Tactics_Types.freshness);
                          FStar_Tactics_Types.tac_verb_dbg =
                            (uu___370_2705.FStar_Tactics_Types.tac_verb_dbg)
                        }  in
                      let uu____2706 = set lp  in
                      bind uu____2706
                        (fun uu____2714  ->
                           bind l
                             (fun a  ->
                                bind get
                                  (fun lp'  ->
                                     let uu____2728 = set rp  in
                                     bind uu____2728
                                       (fun uu____2736  ->
                                          bind r
                                            (fun b  ->
                                               bind get
                                                 (fun rp'  ->
                                                    let p' =
                                                      let uu___371_2752 = p
                                                         in
                                                      {
                                                        FStar_Tactics_Types.main_context
                                                          =
                                                          (uu___371_2752.FStar_Tactics_Types.main_context);
                                                        FStar_Tactics_Types.main_goal
                                                          =
                                                          (uu___371_2752.FStar_Tactics_Types.main_goal);
                                                        FStar_Tactics_Types.all_implicits
                                                          =
                                                          (uu___371_2752.FStar_Tactics_Types.all_implicits);
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
                                                          (uu___371_2752.FStar_Tactics_Types.depth);
                                                        FStar_Tactics_Types.__dump
                                                          =
                                                          (uu___371_2752.FStar_Tactics_Types.__dump);
                                                        FStar_Tactics_Types.psc
                                                          =
                                                          (uu___371_2752.FStar_Tactics_Types.psc);
                                                        FStar_Tactics_Types.entry_range
                                                          =
                                                          (uu___371_2752.FStar_Tactics_Types.entry_range);
                                                        FStar_Tactics_Types.guard_policy
                                                          =
                                                          (uu___371_2752.FStar_Tactics_Types.guard_policy);
                                                        FStar_Tactics_Types.freshness
                                                          =
                                                          (uu___371_2752.FStar_Tactics_Types.freshness);
                                                        FStar_Tactics_Types.tac_verb_dbg
                                                          =
                                                          (uu___371_2752.FStar_Tactics_Types.tac_verb_dbg)
                                                      }  in
                                                    let uu____2753 = set p'
                                                       in
                                                    bind uu____2753
                                                      (fun uu____2761  ->
                                                         bind
                                                           remove_solved_goals
                                                           (fun uu____2767 
                                                              -> ret (a, b)))))))))))
  
let focus : 'a . 'a tac -> 'a tac =
  fun f  ->
    let uu____2788 = divide FStar_BigInt.one f idtac  in
    bind uu____2788
      (fun uu____2801  -> match uu____2801 with | (a,()) -> ret a)
  
let rec map : 'a . 'a tac -> 'a Prims.list tac =
  fun tau  ->
    bind get
      (fun p  ->
         match p.FStar_Tactics_Types.goals with
         | [] -> ret []
         | uu____2838::uu____2839 ->
             let uu____2842 =
               let uu____2851 = map tau  in
               divide FStar_BigInt.one tau uu____2851  in
             bind uu____2842
               (fun uu____2869  ->
                  match uu____2869 with | (h,t) -> ret (h :: t)))
  
let (seq : unit tac -> unit tac -> unit tac) =
  fun t1  ->
    fun t2  ->
      let uu____2910 =
        bind t1
          (fun uu____2915  ->
             let uu____2916 = map t2  in
             bind uu____2916 (fun uu____2924  -> ret ()))
         in
      focus uu____2910
  
let (intro : unit -> FStar_Syntax_Syntax.binder tac) =
  fun uu____2933  ->
    let uu____2936 =
      let uu____2939 = cur_goal ()  in
      bind uu____2939
        (fun goal  ->
           let uu____2948 =
             let uu____2955 = FStar_Tactics_Types.goal_type goal  in
             FStar_Syntax_Util.arrow_one uu____2955  in
           match uu____2948 with
           | FStar_Pervasives_Native.Some (b,c) ->
               let uu____2964 =
                 let uu____2965 = FStar_Syntax_Util.is_total_comp c  in
                 Prims.op_Negation uu____2965  in
               if uu____2964
               then fail "Codomain is effectful"
               else
                 (let env' =
                    let uu____2970 = FStar_Tactics_Types.goal_env goal  in
                    FStar_TypeChecker_Env.push_binders uu____2970 [b]  in
                  let typ' = comp_to_typ c  in
                  let uu____2980 = new_uvar "intro" env' typ'  in
                  bind uu____2980
                    (fun uu____2996  ->
                       match uu____2996 with
                       | (body,ctx_uvar) ->
                           let sol =
                             FStar_Syntax_Util.abs [b] body
                               FStar_Pervasives_Native.None
                              in
                           let uu____3016 = set_solution goal sol  in
                           bind uu____3016
                             (fun uu____3022  ->
                                let g =
                                  FStar_Tactics_Types.mk_goal env' ctx_uvar
                                    goal.FStar_Tactics_Types.opts
                                    goal.FStar_Tactics_Types.is_guard
                                   in
                                let uu____3024 =
                                  let uu____3027 = bnorm_goal g  in
                                  replace_cur uu____3027  in
                                bind uu____3024 (fun uu____3029  -> ret b))))
           | FStar_Pervasives_Native.None  ->
               let uu____3034 =
                 let uu____3035 = FStar_Tactics_Types.goal_env goal  in
                 let uu____3036 = FStar_Tactics_Types.goal_type goal  in
                 tts uu____3035 uu____3036  in
               fail1 "goal is not an arrow (%s)" uu____3034)
       in
    FStar_All.pipe_left (wrap_err "intro") uu____2936
  
let (intro_rec :
  unit ->
    (FStar_Syntax_Syntax.binder,FStar_Syntax_Syntax.binder)
      FStar_Pervasives_Native.tuple2 tac)
  =
  fun uu____3051  ->
    let uu____3058 = cur_goal ()  in
    bind uu____3058
      (fun goal  ->
         FStar_Util.print_string
           "WARNING (intro_rec): calling this is known to cause normalizer loops\n";
         FStar_Util.print_string
           "WARNING (intro_rec): proceed at your own risk...\n";
         (let uu____3075 =
            let uu____3082 = FStar_Tactics_Types.goal_type goal  in
            FStar_Syntax_Util.arrow_one uu____3082  in
          match uu____3075 with
          | FStar_Pervasives_Native.Some (b,c) ->
              let uu____3095 =
                let uu____3096 = FStar_Syntax_Util.is_total_comp c  in
                Prims.op_Negation uu____3096  in
              if uu____3095
              then fail "Codomain is effectful"
              else
                (let bv =
                   let uu____3109 = FStar_Tactics_Types.goal_type goal  in
                   FStar_Syntax_Syntax.gen_bv "__recf"
                     FStar_Pervasives_Native.None uu____3109
                    in
                 let bs =
                   let uu____3117 = FStar_Syntax_Syntax.mk_binder bv  in
                   [uu____3117; b]  in
                 let env' =
                   let uu____3135 = FStar_Tactics_Types.goal_env goal  in
                   FStar_TypeChecker_Env.push_binders uu____3135 bs  in
                 let uu____3136 =
                   let uu____3143 = comp_to_typ c  in
                   new_uvar "intro_rec" env' uu____3143  in
                 bind uu____3136
                   (fun uu____3162  ->
                      match uu____3162 with
                      | (u,ctx_uvar_u) ->
                          let lb =
                            let uu____3176 =
                              FStar_Tactics_Types.goal_type goal  in
                            let uu____3179 =
                              FStar_Syntax_Util.abs [b] u
                                FStar_Pervasives_Native.None
                               in
                            FStar_Syntax_Util.mk_letbinding
                              (FStar_Util.Inl bv) [] uu____3176
                              FStar_Parser_Const.effect_Tot_lid uu____3179 []
                              FStar_Range.dummyRange
                             in
                          let body = FStar_Syntax_Syntax.bv_to_name bv  in
                          let uu____3193 =
                            FStar_Syntax_Subst.close_let_rec [lb] body  in
                          (match uu____3193 with
                           | (lbs,body1) ->
                               let tm =
                                 let uu____3215 =
                                   let uu____3216 =
                                     FStar_Tactics_Types.goal_witness goal
                                      in
                                   uu____3216.FStar_Syntax_Syntax.pos  in
                                 FStar_Syntax_Syntax.mk
                                   (FStar_Syntax_Syntax.Tm_let
                                      ((true, lbs), body1))
                                   FStar_Pervasives_Native.None uu____3215
                                  in
                               let uu____3229 = set_solution goal tm  in
                               bind uu____3229
                                 (fun uu____3238  ->
                                    let uu____3239 =
                                      let uu____3242 =
                                        bnorm_goal
                                          (let uu___374_3245 = goal  in
                                           {
                                             FStar_Tactics_Types.goal_main_env
                                               =
                                               (uu___374_3245.FStar_Tactics_Types.goal_main_env);
                                             FStar_Tactics_Types.goal_ctx_uvar
                                               = ctx_uvar_u;
                                             FStar_Tactics_Types.opts =
                                               (uu___374_3245.FStar_Tactics_Types.opts);
                                             FStar_Tactics_Types.is_guard =
                                               (uu___374_3245.FStar_Tactics_Types.is_guard)
                                           })
                                         in
                                      replace_cur uu____3242  in
                                    bind uu____3239
                                      (fun uu____3252  ->
                                         let uu____3253 =
                                           let uu____3258 =
                                             FStar_Syntax_Syntax.mk_binder bv
                                              in
                                           (uu____3258, b)  in
                                         ret uu____3253)))))
          | FStar_Pervasives_Native.None  ->
              let uu____3267 =
                let uu____3268 = FStar_Tactics_Types.goal_env goal  in
                let uu____3269 = FStar_Tactics_Types.goal_type goal  in
                tts uu____3268 uu____3269  in
              fail1 "intro_rec: goal is not an arrow (%s)" uu____3267))
  
let (norm : FStar_Syntax_Embeddings.norm_step Prims.list -> unit tac) =
  fun s  ->
    let uu____3287 = cur_goal ()  in
    bind uu____3287
      (fun goal  ->
         mlog
           (fun uu____3294  ->
              let uu____3295 =
                let uu____3296 = FStar_Tactics_Types.goal_witness goal  in
                FStar_Syntax_Print.term_to_string uu____3296  in
              FStar_Util.print1 "norm: witness = %s\n" uu____3295)
           (fun uu____3301  ->
              let steps =
                let uu____3305 = FStar_TypeChecker_Normalize.tr_norm_steps s
                   in
                FStar_List.append
                  [FStar_TypeChecker_Normalize.Reify;
                  FStar_TypeChecker_Normalize.UnfoldTac] uu____3305
                 in
              let t =
                let uu____3309 = FStar_Tactics_Types.goal_env goal  in
                let uu____3310 = FStar_Tactics_Types.goal_type goal  in
                normalize steps uu____3309 uu____3310  in
              let uu____3311 = FStar_Tactics_Types.goal_with_type goal t  in
              replace_cur uu____3311))
  
let (norm_term_env :
  env ->
    FStar_Syntax_Embeddings.norm_step Prims.list ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term tac)
  =
  fun e  ->
    fun s  ->
      fun t  ->
        let uu____3335 =
          mlog
            (fun uu____3340  ->
               let uu____3341 = FStar_Syntax_Print.term_to_string t  in
               FStar_Util.print1 "norm_term: tm = %s\n" uu____3341)
            (fun uu____3343  ->
               bind get
                 (fun ps  ->
                    let opts =
                      match ps.FStar_Tactics_Types.goals with
                      | g::uu____3349 -> g.FStar_Tactics_Types.opts
                      | uu____3352 -> FStar_Options.peek ()  in
                    mlog
                      (fun uu____3357  ->
                         let uu____3358 = FStar_Syntax_Print.term_to_string t
                            in
                         FStar_Util.print1 "norm_term_env: t = %s\n"
                           uu____3358)
                      (fun uu____3361  ->
                         let uu____3362 = __tc e t  in
                         bind uu____3362
                           (fun uu____3383  ->
                              match uu____3383 with
                              | (t1,uu____3393,uu____3394) ->
                                  let steps =
                                    let uu____3398 =
                                      FStar_TypeChecker_Normalize.tr_norm_steps
                                        s
                                       in
                                    FStar_List.append
                                      [FStar_TypeChecker_Normalize.Reify;
                                      FStar_TypeChecker_Normalize.UnfoldTac]
                                      uu____3398
                                     in
                                  let t2 =
                                    normalize steps
                                      ps.FStar_Tactics_Types.main_context t1
                                     in
                                  ret t2))))
           in
        FStar_All.pipe_left (wrap_err "norm_term") uu____3335
  
let (refine_intro : unit -> unit tac) =
  fun uu____3412  ->
    let uu____3415 =
      let uu____3418 = cur_goal ()  in
      bind uu____3418
        (fun g  ->
           let uu____3425 =
             let uu____3436 = FStar_Tactics_Types.goal_env g  in
             let uu____3437 = FStar_Tactics_Types.goal_type g  in
             FStar_TypeChecker_Rel.base_and_refinement uu____3436 uu____3437
              in
           match uu____3425 with
           | (uu____3440,FStar_Pervasives_Native.None ) ->
               fail "not a refinement"
           | (t,FStar_Pervasives_Native.Some (bv,phi)) ->
               let g1 = FStar_Tactics_Types.goal_with_type g t  in
               let uu____3465 =
                 let uu____3470 =
                   let uu____3475 =
                     let uu____3476 = FStar_Syntax_Syntax.mk_binder bv  in
                     [uu____3476]  in
                   FStar_Syntax_Subst.open_term uu____3475 phi  in
                 match uu____3470 with
                 | (bvs,phi1) ->
                     let uu____3495 =
                       let uu____3496 = FStar_List.hd bvs  in
                       FStar_Pervasives_Native.fst uu____3496  in
                     (uu____3495, phi1)
                  in
               (match uu____3465 with
                | (bv1,phi1) ->
                    let uu____3509 =
                      let uu____3512 = FStar_Tactics_Types.goal_env g  in
                      let uu____3513 =
                        let uu____3514 =
                          let uu____3517 =
                            let uu____3518 =
                              let uu____3525 =
                                FStar_Tactics_Types.goal_witness g  in
                              (bv1, uu____3525)  in
                            FStar_Syntax_Syntax.NT uu____3518  in
                          [uu____3517]  in
                        FStar_Syntax_Subst.subst uu____3514 phi1  in
                      mk_irrelevant_goal "refine_intro refinement" uu____3512
                        uu____3513 g.FStar_Tactics_Types.opts
                       in
                    bind uu____3509
                      (fun g2  ->
                         bind __dismiss
                           (fun uu____3533  -> add_goals [g1; g2]))))
       in
    FStar_All.pipe_left (wrap_err "refine_intro") uu____3415
  
let (__exact_now : Prims.bool -> FStar_Syntax_Syntax.term -> unit tac) =
  fun set_expected_typ1  ->
    fun t  ->
      let uu____3552 = cur_goal ()  in
      bind uu____3552
        (fun goal  ->
           let env =
             if set_expected_typ1
             then
               let uu____3560 = FStar_Tactics_Types.goal_env goal  in
               let uu____3561 = FStar_Tactics_Types.goal_type goal  in
               FStar_TypeChecker_Env.set_expected_typ uu____3560 uu____3561
             else FStar_Tactics_Types.goal_env goal  in
           let uu____3563 = __tc env t  in
           bind uu____3563
             (fun uu____3582  ->
                match uu____3582 with
                | (t1,typ,guard) ->
                    mlog
                      (fun uu____3597  ->
                         let uu____3598 =
                           FStar_Syntax_Print.term_to_string typ  in
                         let uu____3599 =
                           let uu____3600 = FStar_Tactics_Types.goal_env goal
                              in
                           FStar_TypeChecker_Rel.guard_to_string uu____3600
                             guard
                            in
                         FStar_Util.print2
                           "__exact_now: got type %s\n__exact_now: and guard %s\n"
                           uu____3598 uu____3599)
                      (fun uu____3603  ->
                         let uu____3604 =
                           let uu____3607 = FStar_Tactics_Types.goal_env goal
                              in
                           proc_guard "__exact typing" uu____3607 guard  in
                         bind uu____3604
                           (fun uu____3609  ->
                              mlog
                                (fun uu____3613  ->
                                   let uu____3614 =
                                     FStar_Syntax_Print.term_to_string typ
                                      in
                                   let uu____3615 =
                                     let uu____3616 =
                                       FStar_Tactics_Types.goal_type goal  in
                                     FStar_Syntax_Print.term_to_string
                                       uu____3616
                                      in
                                   FStar_Util.print2
                                     "__exact_now: unifying %s and %s\n"
                                     uu____3614 uu____3615)
                                (fun uu____3619  ->
                                   let uu____3620 =
                                     let uu____3623 =
                                       FStar_Tactics_Types.goal_env goal  in
                                     let uu____3624 =
                                       FStar_Tactics_Types.goal_type goal  in
                                     do_unify uu____3623 typ uu____3624  in
                                   bind uu____3620
                                     (fun b  ->
                                        if b
                                        then solve goal t1
                                        else
                                          (let uu____3630 =
                                             let uu____3631 =
                                               FStar_Tactics_Types.goal_env
                                                 goal
                                                in
                                             tts uu____3631 t1  in
                                           let uu____3632 =
                                             let uu____3633 =
                                               FStar_Tactics_Types.goal_env
                                                 goal
                                                in
                                             tts uu____3633 typ  in
                                           let uu____3634 =
                                             let uu____3635 =
                                               FStar_Tactics_Types.goal_env
                                                 goal
                                                in
                                             let uu____3636 =
                                               FStar_Tactics_Types.goal_type
                                                 goal
                                                in
                                             tts uu____3635 uu____3636  in
                                           let uu____3637 =
                                             let uu____3638 =
                                               FStar_Tactics_Types.goal_env
                                                 goal
                                                in
                                             let uu____3639 =
                                               FStar_Tactics_Types.goal_witness
                                                 goal
                                                in
                                             tts uu____3638 uu____3639  in
                                           fail4
                                             "%s : %s does not exactly solve the goal %s (witness = %s)"
                                             uu____3630 uu____3632 uu____3634
                                             uu____3637)))))))
  
let (t_exact : Prims.bool -> FStar_Syntax_Syntax.term -> unit tac) =
  fun set_expected_typ1  ->
    fun tm  ->
      let uu____3654 =
        mlog
          (fun uu____3659  ->
             let uu____3660 = FStar_Syntax_Print.term_to_string tm  in
             FStar_Util.print1 "t_exact: tm = %s\n" uu____3660)
          (fun uu____3663  ->
             let uu____3664 =
               let uu____3671 = __exact_now set_expected_typ1 tm  in
               trytac' uu____3671  in
             bind uu____3664
               (fun uu___338_3680  ->
                  match uu___338_3680 with
                  | FStar_Util.Inr r -> ret ()
                  | FStar_Util.Inl e ->
                      mlog
                        (fun uu____3690  ->
                           FStar_Util.print_string
                             "__exact_now failed, trying refine...\n")
                        (fun uu____3693  ->
                           let uu____3694 =
                             let uu____3701 =
                               let uu____3704 =
                                 norm [FStar_Syntax_Embeddings.Delta]  in
                               bind uu____3704
                                 (fun uu____3709  ->
                                    let uu____3710 = refine_intro ()  in
                                    bind uu____3710
                                      (fun uu____3714  ->
                                         __exact_now set_expected_typ1 tm))
                                in
                             trytac' uu____3701  in
                           bind uu____3694
                             (fun uu___337_3721  ->
                                match uu___337_3721 with
                                | FStar_Util.Inr r -> ret ()
                                | FStar_Util.Inl uu____3729 -> fail e))))
         in
      FStar_All.pipe_left (wrap_err "exact") uu____3654
  
let (uvar_free_in_goal :
  FStar_Syntax_Syntax.uvar -> FStar_Tactics_Types.goal -> Prims.bool) =
  fun u  ->
    fun g  ->
      if g.FStar_Tactics_Types.is_guard
      then false
      else
        (let free_uvars =
           let uu____3758 =
             let uu____3761 =
               let uu____3764 = FStar_Tactics_Types.goal_type g  in
               FStar_Syntax_Free.uvars uu____3764  in
             FStar_Util.set_elements uu____3761  in
           FStar_List.map (fun u1  -> u1.FStar_Syntax_Syntax.ctx_uvar_head)
             uu____3758
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
          let uu____3842 = f x  in
          bind uu____3842
            (fun y  ->
               let uu____3850 = mapM f xs  in
               bind uu____3850 (fun ys  -> ret (y :: ys)))
  
exception NoUnif 
let (uu___is_NoUnif : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with | NoUnif  -> true | uu____3870 -> false
  
let rec (__apply :
  Prims.bool ->
    FStar_Syntax_Syntax.term -> FStar_Reflection_Data.typ -> unit tac)
  =
  fun uopt  ->
    fun tm  ->
      fun typ  ->
        let uu____3890 = cur_goal ()  in
        bind uu____3890
          (fun goal  ->
             mlog
               (fun uu____3897  ->
                  let uu____3898 = FStar_Syntax_Print.term_to_string tm  in
                  FStar_Util.print1 ">>> Calling __exact(%s)\n" uu____3898)
               (fun uu____3901  ->
                  let uu____3902 =
                    let uu____3907 =
                      let uu____3910 = t_exact false tm  in
                      with_policy FStar_Tactics_Types.Force uu____3910  in
                    trytac_exn uu____3907  in
                  bind uu____3902
                    (fun uu___339_3917  ->
                       match uu___339_3917 with
                       | FStar_Pervasives_Native.Some r -> ret ()
                       | FStar_Pervasives_Native.None  ->
                           mlog
                             (fun uu____3925  ->
                                let uu____3926 =
                                  FStar_Syntax_Print.term_to_string typ  in
                                FStar_Util.print1 ">>> typ = %s\n" uu____3926)
                             (fun uu____3929  ->
                                let uu____3930 =
                                  FStar_Syntax_Util.arrow_one typ  in
                                match uu____3930 with
                                | FStar_Pervasives_Native.None  ->
                                    FStar_Exn.raise NoUnif
                                | FStar_Pervasives_Native.Some ((bv,aq),c) ->
                                    mlog
                                      (fun uu____3954  ->
                                         let uu____3955 =
                                           FStar_Syntax_Print.binder_to_string
                                             (bv, aq)
                                            in
                                         FStar_Util.print1
                                           "__apply: pushing binder %s\n"
                                           uu____3955)
                                      (fun uu____3958  ->
                                         let uu____3959 =
                                           let uu____3960 =
                                             FStar_Syntax_Util.is_total_comp
                                               c
                                              in
                                           Prims.op_Negation uu____3960  in
                                         if uu____3959
                                         then
                                           fail "apply: not total codomain"
                                         else
                                           (let uu____3964 =
                                              let uu____3971 =
                                                FStar_Tactics_Types.goal_env
                                                  goal
                                                 in
                                              new_uvar "apply" uu____3971
                                                bv.FStar_Syntax_Syntax.sort
                                               in
                                            bind uu____3964
                                              (fun uu____3982  ->
                                                 match uu____3982 with
                                                 | (u,_goal_u) ->
                                                     let tm' =
                                                       FStar_Syntax_Syntax.mk_Tm_app
                                                         tm [(u, aq)]
                                                         FStar_Pervasives_Native.None
                                                         tm.FStar_Syntax_Syntax.pos
                                                        in
                                                     let typ' =
                                                       let uu____4009 =
                                                         comp_to_typ c  in
                                                       FStar_All.pipe_left
                                                         (FStar_Syntax_Subst.subst
                                                            [FStar_Syntax_Syntax.NT
                                                               (bv, u)])
                                                         uu____4009
                                                        in
                                                     let uu____4012 =
                                                       __apply uopt tm' typ'
                                                        in
                                                     bind uu____4012
                                                       (fun uu____4020  ->
                                                          let u1 =
                                                            let uu____4022 =
                                                              FStar_Tactics_Types.goal_env
                                                                goal
                                                               in
                                                            bnorm uu____4022
                                                              u
                                                             in
                                                          let uu____4023 =
                                                            let uu____4024 =
                                                              let uu____4027
                                                                =
                                                                let uu____4028
                                                                  =
                                                                  FStar_Syntax_Util.head_and_args
                                                                    u1
                                                                   in
                                                                FStar_Pervasives_Native.fst
                                                                  uu____4028
                                                                 in
                                                              FStar_Syntax_Subst.compress
                                                                uu____4027
                                                               in
                                                            uu____4024.FStar_Syntax_Syntax.n
                                                             in
                                                          match uu____4023
                                                          with
                                                          | FStar_Syntax_Syntax.Tm_uvar
                                                              (goal_u,uu____4056)
                                                              ->
                                                              bind get
                                                                (fun ps  ->
                                                                   let uu____4076
                                                                    =
                                                                    uopt &&
                                                                    (uvar_free
                                                                    goal_u.FStar_Syntax_Syntax.ctx_uvar_head
                                                                    ps)  in
                                                                   if
                                                                    uu____4076
                                                                   then
                                                                    ret ()
                                                                   else
                                                                    (let uu____4080
                                                                    =
                                                                    let uu____4083
                                                                    =
                                                                    bnorm_goal
                                                                    (let uu___375_4086
                                                                    = goal
                                                                     in
                                                                    {
                                                                    FStar_Tactics_Types.goal_main_env
                                                                    =
                                                                    (uu___375_4086.FStar_Tactics_Types.goal_main_env);
                                                                    FStar_Tactics_Types.goal_ctx_uvar
                                                                    = goal_u;
                                                                    FStar_Tactics_Types.opts
                                                                    =
                                                                    (uu___375_4086.FStar_Tactics_Types.opts);
                                                                    FStar_Tactics_Types.is_guard
                                                                    = false
                                                                    })  in
                                                                    [uu____4083]
                                                                     in
                                                                    add_goals
                                                                    uu____4080))
                                                          | t -> ret ()))))))))
  
let try_unif : 'a . 'a tac -> 'a tac -> 'a tac =
  fun t  ->
    fun t'  ->
      mk_tac
        (fun ps  ->
           try (fun uu___377_4120  -> match () with | () -> run t ps) ()
           with | NoUnif  -> run t' ps)
  
let (apply : Prims.bool -> FStar_Syntax_Syntax.term -> unit tac) =
  fun uopt  ->
    fun tm  ->
      let uu____4141 =
        mlog
          (fun uu____4146  ->
             let uu____4147 = FStar_Syntax_Print.term_to_string tm  in
             FStar_Util.print1 "apply: tm = %s\n" uu____4147)
          (fun uu____4150  ->
             let uu____4151 = cur_goal ()  in
             bind uu____4151
               (fun goal  ->
                  let uu____4157 =
                    let uu____4166 = FStar_Tactics_Types.goal_env goal  in
                    __tc uu____4166 tm  in
                  bind uu____4157
                    (fun uu____4180  ->
                       match uu____4180 with
                       | (tm1,typ,guard) ->
                           let typ1 =
                             let uu____4193 =
                               FStar_Tactics_Types.goal_env goal  in
                             bnorm uu____4193 typ  in
                           let uu____4194 =
                             let uu____4197 =
                               let uu____4200 = __apply uopt tm1 typ1  in
                               bind uu____4200
                                 (fun uu____4205  ->
                                    let uu____4206 =
                                      FStar_Tactics_Types.goal_env goal  in
                                    proc_guard "apply guard" uu____4206 guard)
                                in
                             focus uu____4197  in
                           let uu____4207 =
                             let uu____4210 =
                               let uu____4211 =
                                 FStar_Tactics_Types.goal_env goal  in
                               tts uu____4211 tm1  in
                             let uu____4212 =
                               let uu____4213 =
                                 FStar_Tactics_Types.goal_env goal  in
                               tts uu____4213 typ1  in
                             let uu____4214 =
                               let uu____4215 =
                                 FStar_Tactics_Types.goal_env goal  in
                               let uu____4216 =
                                 FStar_Tactics_Types.goal_type goal  in
                               tts uu____4215 uu____4216  in
                             fail3
                               "Cannot instantiate %s (of type %s) to match goal (%s)"
                               uu____4210 uu____4212 uu____4214
                              in
                           try_unif uu____4194 uu____4207)))
         in
      FStar_All.pipe_left (wrap_err "apply") uu____4141
  
let (lemma_or_sq :
  FStar_Syntax_Syntax.comp ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun c  ->
    let ct = FStar_Syntax_Util.comp_to_comp_typ_nouniv c  in
    let uu____4239 =
      FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
        FStar_Parser_Const.effect_Lemma_lid
       in
    if uu____4239
    then
      let uu____4246 =
        match ct.FStar_Syntax_Syntax.effect_args with
        | pre::post::uu____4261 ->
            ((FStar_Pervasives_Native.fst pre),
              (FStar_Pervasives_Native.fst post))
        | uu____4300 -> failwith "apply_lemma: impossible: not a lemma"  in
      match uu____4246 with
      | (pre,post) ->
          let post1 =
            let uu____4330 =
              let uu____4339 =
                FStar_Syntax_Syntax.as_arg FStar_Syntax_Util.exp_unit  in
              [uu____4339]  in
            FStar_Syntax_Util.mk_app post uu____4330  in
          FStar_Pervasives_Native.Some (pre, post1)
    else
      (let uu____4363 =
         FStar_Syntax_Util.is_pure_effect ct.FStar_Syntax_Syntax.effect_name
          in
       if uu____4363
       then
         let uu____4370 =
           FStar_Syntax_Util.un_squash ct.FStar_Syntax_Syntax.result_typ  in
         FStar_Util.map_opt uu____4370
           (fun post  -> (FStar_Syntax_Util.t_true, post))
       else FStar_Pervasives_Native.None)
  
let (apply_lemma : FStar_Syntax_Syntax.term -> unit tac) =
  fun tm  ->
    let uu____4403 =
      let uu____4406 =
        mlog
          (fun uu____4411  ->
             let uu____4412 = FStar_Syntax_Print.term_to_string tm  in
             FStar_Util.print1 "apply_lemma: tm = %s\n" uu____4412)
          (fun uu____4416  ->
             let is_unit_t t =
               let uu____4423 =
                 let uu____4424 = FStar_Syntax_Subst.compress t  in
                 uu____4424.FStar_Syntax_Syntax.n  in
               match uu____4423 with
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.unit_lid
                   -> true
               | uu____4428 -> false  in
             let uu____4429 = cur_goal ()  in
             bind uu____4429
               (fun goal  ->
                  let uu____4435 =
                    let uu____4444 = FStar_Tactics_Types.goal_env goal  in
                    __tc uu____4444 tm  in
                  bind uu____4435
                    (fun uu____4459  ->
                       match uu____4459 with
                       | (tm1,t,guard) ->
                           let uu____4471 =
                             FStar_Syntax_Util.arrow_formals_comp t  in
                           (match uu____4471 with
                            | (bs,comp) ->
                                let uu____4498 = lemma_or_sq comp  in
                                (match uu____4498 with
                                 | FStar_Pervasives_Native.None  ->
                                     fail "not a lemma or squashed function"
                                 | FStar_Pervasives_Native.Some (pre,post) ->
                                     let uu____4517 =
                                       FStar_List.fold_left
                                         (fun uu____4559  ->
                                            fun uu____4560  ->
                                              match (uu____4559, uu____4560)
                                              with
                                              | ((uvs,guard1,subst1),(b,aq))
                                                  ->
                                                  let b_t =
                                                    FStar_Syntax_Subst.subst
                                                      subst1
                                                      b.FStar_Syntax_Syntax.sort
                                                     in
                                                  let uu____4651 =
                                                    is_unit_t b_t  in
                                                  if uu____4651
                                                  then
                                                    (((FStar_Syntax_Util.exp_unit,
                                                        aq) :: uvs), guard1,
                                                      ((FStar_Syntax_Syntax.NT
                                                          (b,
                                                            FStar_Syntax_Util.exp_unit))
                                                      :: subst1))
                                                  else
                                                    (let uu____4681 =
                                                       let uu____4694 =
                                                         let uu____4695 =
                                                           FStar_Tactics_Types.goal_type
                                                             goal
                                                            in
                                                         uu____4695.FStar_Syntax_Syntax.pos
                                                          in
                                                       let uu____4698 =
                                                         FStar_Tactics_Types.goal_env
                                                           goal
                                                          in
                                                       FStar_TypeChecker_Util.new_implicit_var
                                                         "apply_lemma"
                                                         uu____4694
                                                         uu____4698 b_t
                                                        in
                                                     match uu____4681 with
                                                     | (u,uu____4714,g_u) ->
                                                         let uu____4728 =
                                                           FStar_TypeChecker_Rel.conj_guard
                                                             guard1 g_u
                                                            in
                                                         (((u, aq) :: uvs),
                                                           uu____4728,
                                                           ((FStar_Syntax_Syntax.NT
                                                               (b, u)) ::
                                                           subst1))))
                                         ([], guard, []) bs
                                        in
                                     (match uu____4517 with
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
                                          let uu____4789 =
                                            let uu____4792 =
                                              FStar_Tactics_Types.goal_env
                                                goal
                                               in
                                            let uu____4793 =
                                              FStar_Syntax_Util.mk_squash
                                                FStar_Syntax_Syntax.U_zero
                                                post1
                                               in
                                            let uu____4794 =
                                              FStar_Tactics_Types.goal_type
                                                goal
                                               in
                                            do_unify uu____4792 uu____4793
                                              uu____4794
                                             in
                                          bind uu____4789
                                            (fun b  ->
                                               if Prims.op_Negation b
                                               then
                                                 let uu____4802 =
                                                   let uu____4803 =
                                                     FStar_Tactics_Types.goal_env
                                                       goal
                                                      in
                                                   tts uu____4803 tm1  in
                                                 let uu____4804 =
                                                   let uu____4805 =
                                                     FStar_Tactics_Types.goal_env
                                                       goal
                                                      in
                                                   let uu____4806 =
                                                     FStar_Syntax_Util.mk_squash
                                                       FStar_Syntax_Syntax.U_zero
                                                       post1
                                                      in
                                                   tts uu____4805 uu____4806
                                                    in
                                                 let uu____4807 =
                                                   let uu____4808 =
                                                     FStar_Tactics_Types.goal_env
                                                       goal
                                                      in
                                                   let uu____4809 =
                                                     FStar_Tactics_Types.goal_type
                                                       goal
                                                      in
                                                   tts uu____4808 uu____4809
                                                    in
                                                 fail3
                                                   "Cannot instantiate lemma %s (with postcondition: %s) to match goal (%s)"
                                                   uu____4802 uu____4804
                                                   uu____4807
                                               else
                                                 (let uu____4811 =
                                                    add_implicits
                                                      implicits.FStar_TypeChecker_Env.implicits
                                                     in
                                                  bind uu____4811
                                                    (fun uu____4816  ->
                                                       let uu____4817 =
                                                         solve' goal
                                                           FStar_Syntax_Util.exp_unit
                                                          in
                                                       bind uu____4817
                                                         (fun uu____4825  ->
                                                            let is_free_uvar
                                                              uv t1 =
                                                              let free_uvars
                                                                =
                                                                let uu____4850
                                                                  =
                                                                  let uu____4853
                                                                    =
                                                                    FStar_Syntax_Free.uvars
                                                                    t1  in
                                                                  FStar_Util.set_elements
                                                                    uu____4853
                                                                   in
                                                                FStar_List.map
                                                                  (fun x  ->
                                                                    x.FStar_Syntax_Syntax.ctx_uvar_head)
                                                                  uu____4850
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
                                                                   let uu____4888
                                                                    =
                                                                    FStar_Tactics_Types.goal_type
                                                                    g'  in
                                                                   is_free_uvar
                                                                    uv
                                                                    uu____4888)
                                                                goals
                                                               in
                                                            let checkone t1
                                                              goals =
                                                              let uu____4904
                                                                =
                                                                FStar_Syntax_Util.head_and_args
                                                                  t1
                                                                 in
                                                              match uu____4904
                                                              with
                                                              | (hd1,uu____4920)
                                                                  ->
                                                                  (match 
                                                                    hd1.FStar_Syntax_Syntax.n
                                                                   with
                                                                   | 
                                                                   FStar_Syntax_Syntax.Tm_uvar
                                                                    (uv,uu____4942)
                                                                    ->
                                                                    appears
                                                                    uv.FStar_Syntax_Syntax.ctx_uvar_head
                                                                    goals
                                                                   | 
                                                                   uu____4959
                                                                    -> false)
                                                               in
                                                            let uu____4960 =
                                                              FStar_All.pipe_right
                                                                implicits.FStar_TypeChecker_Env.implicits
                                                                (mapM
                                                                   (fun
                                                                    uu____5023
                                                                     ->
                                                                    match uu____5023
                                                                    with
                                                                    | 
                                                                    (_msg,term,ctx_uvar,_range)
                                                                    ->
                                                                    let uu____5046
                                                                    =
                                                                    FStar_Syntax_Util.head_and_args
                                                                    term  in
                                                                    (match uu____5046
                                                                    with
                                                                    | 
                                                                    (hd1,uu____5072)
                                                                    ->
                                                                    let uu____5093
                                                                    =
                                                                    let uu____5094
                                                                    =
                                                                    FStar_Syntax_Subst.compress
                                                                    hd1  in
                                                                    uu____5094.FStar_Syntax_Syntax.n
                                                                     in
                                                                    (match uu____5093
                                                                    with
                                                                    | 
                                                                    FStar_Syntax_Syntax.Tm_uvar
                                                                    (ctx_uvar1,uu____5108)
                                                                    ->
                                                                    let goal1
                                                                    =
                                                                    bnorm_goal
                                                                    (let uu___378_5128
                                                                    = goal
                                                                     in
                                                                    {
                                                                    FStar_Tactics_Types.goal_main_env
                                                                    =
                                                                    (uu___378_5128.FStar_Tactics_Types.goal_main_env);
                                                                    FStar_Tactics_Types.goal_ctx_uvar
                                                                    =
                                                                    ctx_uvar1;
                                                                    FStar_Tactics_Types.opts
                                                                    =
                                                                    (uu___378_5128.FStar_Tactics_Types.opts);
                                                                    FStar_Tactics_Types.is_guard
                                                                    =
                                                                    (uu___378_5128.FStar_Tactics_Types.is_guard)
                                                                    })  in
                                                                    ret
                                                                    ([goal1],
                                                                    [])
                                                                    | 
                                                                    uu____5141
                                                                    ->
                                                                    let env =
                                                                    let uu___379_5143
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    goal  in
                                                                    {
                                                                    FStar_TypeChecker_Env.solver
                                                                    =
                                                                    (uu___379_5143.FStar_TypeChecker_Env.solver);
                                                                    FStar_TypeChecker_Env.range
                                                                    =
                                                                    (uu___379_5143.FStar_TypeChecker_Env.range);
                                                                    FStar_TypeChecker_Env.curmodule
                                                                    =
                                                                    (uu___379_5143.FStar_TypeChecker_Env.curmodule);
                                                                    FStar_TypeChecker_Env.gamma
                                                                    =
                                                                    (ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_gamma);
                                                                    FStar_TypeChecker_Env.gamma_sig
                                                                    =
                                                                    (uu___379_5143.FStar_TypeChecker_Env.gamma_sig);
                                                                    FStar_TypeChecker_Env.gamma_cache
                                                                    =
                                                                    (uu___379_5143.FStar_TypeChecker_Env.gamma_cache);
                                                                    FStar_TypeChecker_Env.modules
                                                                    =
                                                                    (uu___379_5143.FStar_TypeChecker_Env.modules);
                                                                    FStar_TypeChecker_Env.expected_typ
                                                                    =
                                                                    (uu___379_5143.FStar_TypeChecker_Env.expected_typ);
                                                                    FStar_TypeChecker_Env.sigtab
                                                                    =
                                                                    (uu___379_5143.FStar_TypeChecker_Env.sigtab);
                                                                    FStar_TypeChecker_Env.is_pattern
                                                                    =
                                                                    (uu___379_5143.FStar_TypeChecker_Env.is_pattern);
                                                                    FStar_TypeChecker_Env.instantiate_imp
                                                                    =
                                                                    (uu___379_5143.FStar_TypeChecker_Env.instantiate_imp);
                                                                    FStar_TypeChecker_Env.effects
                                                                    =
                                                                    (uu___379_5143.FStar_TypeChecker_Env.effects);
                                                                    FStar_TypeChecker_Env.generalize
                                                                    =
                                                                    (uu___379_5143.FStar_TypeChecker_Env.generalize);
                                                                    FStar_TypeChecker_Env.letrecs
                                                                    =
                                                                    (uu___379_5143.FStar_TypeChecker_Env.letrecs);
                                                                    FStar_TypeChecker_Env.top_level
                                                                    =
                                                                    (uu___379_5143.FStar_TypeChecker_Env.top_level);
                                                                    FStar_TypeChecker_Env.check_uvars
                                                                    =
                                                                    (uu___379_5143.FStar_TypeChecker_Env.check_uvars);
                                                                    FStar_TypeChecker_Env.use_eq
                                                                    =
                                                                    (uu___379_5143.FStar_TypeChecker_Env.use_eq);
                                                                    FStar_TypeChecker_Env.is_iface
                                                                    =
                                                                    (uu___379_5143.FStar_TypeChecker_Env.is_iface);
                                                                    FStar_TypeChecker_Env.admit
                                                                    =
                                                                    (uu___379_5143.FStar_TypeChecker_Env.admit);
                                                                    FStar_TypeChecker_Env.lax
                                                                    =
                                                                    (uu___379_5143.FStar_TypeChecker_Env.lax);
                                                                    FStar_TypeChecker_Env.lax_universes
                                                                    =
                                                                    (uu___379_5143.FStar_TypeChecker_Env.lax_universes);
                                                                    FStar_TypeChecker_Env.failhard
                                                                    =
                                                                    (uu___379_5143.FStar_TypeChecker_Env.failhard);
                                                                    FStar_TypeChecker_Env.nosynth
                                                                    =
                                                                    (uu___379_5143.FStar_TypeChecker_Env.nosynth);
                                                                    FStar_TypeChecker_Env.uvar_subtyping
                                                                    =
                                                                    (uu___379_5143.FStar_TypeChecker_Env.uvar_subtyping);
                                                                    FStar_TypeChecker_Env.tc_term
                                                                    =
                                                                    (uu___379_5143.FStar_TypeChecker_Env.tc_term);
                                                                    FStar_TypeChecker_Env.type_of
                                                                    =
                                                                    (uu___379_5143.FStar_TypeChecker_Env.type_of);
                                                                    FStar_TypeChecker_Env.universe_of
                                                                    =
                                                                    (uu___379_5143.FStar_TypeChecker_Env.universe_of);
                                                                    FStar_TypeChecker_Env.check_type_of
                                                                    =
                                                                    (uu___379_5143.FStar_TypeChecker_Env.check_type_of);
                                                                    FStar_TypeChecker_Env.use_bv_sorts
                                                                    =
                                                                    (uu___379_5143.FStar_TypeChecker_Env.use_bv_sorts);
                                                                    FStar_TypeChecker_Env.qtbl_name_and_index
                                                                    =
                                                                    (uu___379_5143.FStar_TypeChecker_Env.qtbl_name_and_index);
                                                                    FStar_TypeChecker_Env.normalized_eff_names
                                                                    =
                                                                    (uu___379_5143.FStar_TypeChecker_Env.normalized_eff_names);
                                                                    FStar_TypeChecker_Env.proof_ns
                                                                    =
                                                                    (uu___379_5143.FStar_TypeChecker_Env.proof_ns);
                                                                    FStar_TypeChecker_Env.synth_hook
                                                                    =
                                                                    (uu___379_5143.FStar_TypeChecker_Env.synth_hook);
                                                                    FStar_TypeChecker_Env.splice
                                                                    =
                                                                    (uu___379_5143.FStar_TypeChecker_Env.splice);
                                                                    FStar_TypeChecker_Env.is_native_tactic
                                                                    =
                                                                    (uu___379_5143.FStar_TypeChecker_Env.is_native_tactic);
                                                                    FStar_TypeChecker_Env.identifier_info
                                                                    =
                                                                    (uu___379_5143.FStar_TypeChecker_Env.identifier_info);
                                                                    FStar_TypeChecker_Env.tc_hooks
                                                                    =
                                                                    (uu___379_5143.FStar_TypeChecker_Env.tc_hooks);
                                                                    FStar_TypeChecker_Env.dsenv
                                                                    =
                                                                    (uu___379_5143.FStar_TypeChecker_Env.dsenv);
                                                                    FStar_TypeChecker_Env.dep_graph
                                                                    =
                                                                    (uu___379_5143.FStar_TypeChecker_Env.dep_graph)
                                                                    }  in
                                                                    let g_typ
                                                                    =
                                                                    let uu____5145
                                                                    =
                                                                    FStar_Options.__temp_fast_implicits
                                                                    ()  in
                                                                    if
                                                                    uu____5145
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
                                                                    let uu____5148
                                                                    =
                                                                    let uu____5155
                                                                    =
                                                                    FStar_TypeChecker_Env.set_expected_typ
                                                                    env
                                                                    ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_typ
                                                                     in
                                                                    env.FStar_TypeChecker_Env.type_of
                                                                    uu____5155
                                                                    term1  in
                                                                    match uu____5148
                                                                    with
                                                                    | 
                                                                    (uu____5156,uu____5157,g_typ)
                                                                    -> g_typ)
                                                                     in
                                                                    let uu____5159
                                                                    =
                                                                    let uu____5164
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    goal  in
                                                                    goal_from_guard
                                                                    "apply_lemma solved arg"
                                                                    uu____5164
                                                                    g_typ
                                                                    goal.FStar_Tactics_Types.opts
                                                                     in
                                                                    bind
                                                                    uu____5159
                                                                    (fun
                                                                    uu___340_5176
                                                                     ->
                                                                    match uu___340_5176
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
                                                            bind uu____4960
                                                              (fun goals_  ->
                                                                 let sub_goals
                                                                   =
                                                                   let uu____5244
                                                                    =
                                                                    FStar_List.map
                                                                    FStar_Pervasives_Native.fst
                                                                    goals_
                                                                     in
                                                                   FStar_List.flatten
                                                                    uu____5244
                                                                    in
                                                                 let smt_goals
                                                                   =
                                                                   let uu____5266
                                                                    =
                                                                    FStar_List.map
                                                                    FStar_Pervasives_Native.snd
                                                                    goals_
                                                                     in
                                                                   FStar_List.flatten
                                                                    uu____5266
                                                                    in
                                                                 let rec filter'
                                                                   f xs =
                                                                   match xs
                                                                   with
                                                                   | 
                                                                   [] -> []
                                                                   | 
                                                                   x::xs1 ->
                                                                    let uu____5327
                                                                    = f x xs1
                                                                     in
                                                                    if
                                                                    uu____5327
                                                                    then
                                                                    let uu____5330
                                                                    =
                                                                    filter' f
                                                                    xs1  in x
                                                                    ::
                                                                    uu____5330
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
                                                                    let uu____5344
                                                                    =
                                                                    let uu____5345
                                                                    =
                                                                    FStar_Tactics_Types.goal_witness
                                                                    g  in
                                                                    checkone
                                                                    uu____5345
                                                                    goals  in
                                                                    Prims.op_Negation
                                                                    uu____5344)
                                                                    sub_goals
                                                                    in
                                                                 let uu____5346
                                                                   =
                                                                   let uu____5349
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    goal  in
                                                                   proc_guard
                                                                    "apply_lemma guard"
                                                                    uu____5349
                                                                    guard
                                                                    in
                                                                 bind
                                                                   uu____5346
                                                                   (fun
                                                                    uu____5352
                                                                     ->
                                                                    let uu____5353
                                                                    =
                                                                    let uu____5356
                                                                    =
                                                                    let uu____5357
                                                                    =
                                                                    let uu____5358
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    goal  in
                                                                    let uu____5359
                                                                    =
                                                                    FStar_Syntax_Util.mk_squash
                                                                    FStar_Syntax_Syntax.U_zero
                                                                    pre1  in
                                                                    istrivial
                                                                    uu____5358
                                                                    uu____5359
                                                                     in
                                                                    Prims.op_Negation
                                                                    uu____5357
                                                                     in
                                                                    if
                                                                    uu____5356
                                                                    then
                                                                    let uu____5362
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    goal  in
                                                                    add_irrelevant_goal
                                                                    "apply_lemma precondition"
                                                                    uu____5362
                                                                    pre1
                                                                    goal.FStar_Tactics_Types.opts
                                                                    else
                                                                    ret ()
                                                                     in
                                                                    bind
                                                                    uu____5353
                                                                    (fun
                                                                    uu____5366
                                                                     ->
                                                                    let uu____5367
                                                                    =
                                                                    add_smt_goals
                                                                    smt_goals
                                                                     in
                                                                    bind
                                                                    uu____5367
                                                                    (fun
                                                                    uu____5371
                                                                     ->
                                                                    add_goals
                                                                    sub_goals1))))))))))))))
         in
      focus uu____4406  in
    FStar_All.pipe_left (wrap_err "apply_lemma") uu____4403
  
let (destruct_eq' :
  FStar_Reflection_Data.typ ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun typ  ->
    let uu____5393 = FStar_Syntax_Util.destruct_typ_as_formula typ  in
    match uu____5393 with
    | FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn
        (l,uu____5403::(e1,uu____5405)::(e2,uu____5407)::[])) when
        FStar_Ident.lid_equals l FStar_Parser_Const.eq2_lid ->
        FStar_Pervasives_Native.Some (e1, e2)
    | uu____5450 -> FStar_Pervasives_Native.None
  
let (destruct_eq :
  FStar_Reflection_Data.typ ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun typ  ->
    let uu____5474 = destruct_eq' typ  in
    match uu____5474 with
    | FStar_Pervasives_Native.Some t -> FStar_Pervasives_Native.Some t
    | FStar_Pervasives_Native.None  ->
        let uu____5504 = FStar_Syntax_Util.un_squash typ  in
        (match uu____5504 with
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
        let uu____5566 = FStar_TypeChecker_Env.pop_bv e1  in
        match uu____5566 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (bv',e') ->
            if FStar_Syntax_Syntax.bv_eq bvar bv'
            then FStar_Pervasives_Native.Some (e', [])
            else
              (let uu____5614 = aux e'  in
               FStar_Util.map_opt uu____5614
                 (fun uu____5638  ->
                    match uu____5638 with | (e'',bvs) -> (e'', (bv' :: bvs))))
         in
      let uu____5659 = aux e  in
      FStar_Util.map_opt uu____5659
        (fun uu____5683  ->
           match uu____5683 with | (e',bvs) -> (e', (FStar_List.rev bvs)))
  
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
          let uu____5750 =
            let uu____5759 = FStar_Tactics_Types.goal_env g  in
            split_env b1 uu____5759  in
          FStar_Util.map_opt uu____5750
            (fun uu____5774  ->
               match uu____5774 with
               | (e0,bvs) ->
                   let s1 bv =
                     let uu___380_5793 = bv  in
                     let uu____5794 =
                       FStar_Syntax_Subst.subst s bv.FStar_Syntax_Syntax.sort
                        in
                     {
                       FStar_Syntax_Syntax.ppname =
                         (uu___380_5793.FStar_Syntax_Syntax.ppname);
                       FStar_Syntax_Syntax.index =
                         (uu___380_5793.FStar_Syntax_Syntax.index);
                       FStar_Syntax_Syntax.sort = uu____5794
                     }  in
                   let bvs1 = FStar_List.map s1 bvs  in
                   let new_env = push_bvs e0 (b2 :: bvs1)  in
                   let new_goal =
                     let uu___381_5802 = g.FStar_Tactics_Types.goal_ctx_uvar
                        in
                     let uu____5803 =
                       FStar_TypeChecker_Env.all_binders new_env  in
                     let uu____5810 =
                       let uu____5813 = FStar_Tactics_Types.goal_type g  in
                       FStar_Syntax_Subst.subst s uu____5813  in
                     {
                       FStar_Syntax_Syntax.ctx_uvar_head =
                         (uu___381_5802.FStar_Syntax_Syntax.ctx_uvar_head);
                       FStar_Syntax_Syntax.ctx_uvar_gamma =
                         (new_env.FStar_TypeChecker_Env.gamma);
                       FStar_Syntax_Syntax.ctx_uvar_binders = uu____5803;
                       FStar_Syntax_Syntax.ctx_uvar_typ = uu____5810;
                       FStar_Syntax_Syntax.ctx_uvar_reason =
                         (uu___381_5802.FStar_Syntax_Syntax.ctx_uvar_reason);
                       FStar_Syntax_Syntax.ctx_uvar_should_check =
                         (uu___381_5802.FStar_Syntax_Syntax.ctx_uvar_should_check);
                       FStar_Syntax_Syntax.ctx_uvar_range =
                         (uu___381_5802.FStar_Syntax_Syntax.ctx_uvar_range)
                     }  in
                   let uu___382_5814 = g  in
                   {
                     FStar_Tactics_Types.goal_main_env =
                       (uu___382_5814.FStar_Tactics_Types.goal_main_env);
                     FStar_Tactics_Types.goal_ctx_uvar = new_goal;
                     FStar_Tactics_Types.opts =
                       (uu___382_5814.FStar_Tactics_Types.opts);
                     FStar_Tactics_Types.is_guard =
                       (uu___382_5814.FStar_Tactics_Types.is_guard)
                   })
  
let (rewrite : FStar_Syntax_Syntax.binder -> unit tac) =
  fun h  ->
    let uu____5824 =
      let uu____5827 = cur_goal ()  in
      bind uu____5827
        (fun goal  ->
           let uu____5835 = h  in
           match uu____5835 with
           | (bv,uu____5839) ->
               mlog
                 (fun uu____5843  ->
                    let uu____5844 = FStar_Syntax_Print.bv_to_string bv  in
                    let uu____5845 =
                      FStar_Syntax_Print.term_to_string
                        bv.FStar_Syntax_Syntax.sort
                       in
                    FStar_Util.print2 "+++Rewrite %s : %s\n" uu____5844
                      uu____5845)
                 (fun uu____5848  ->
                    let uu____5849 =
                      let uu____5858 = FStar_Tactics_Types.goal_env goal  in
                      split_env bv uu____5858  in
                    match uu____5849 with
                    | FStar_Pervasives_Native.None  ->
                        fail "binder not found in environment"
                    | FStar_Pervasives_Native.Some (e0,bvs) ->
                        let uu____5879 =
                          destruct_eq bv.FStar_Syntax_Syntax.sort  in
                        (match uu____5879 with
                         | FStar_Pervasives_Native.Some (x,e) ->
                             let uu____5894 =
                               let uu____5895 = FStar_Syntax_Subst.compress x
                                  in
                               uu____5895.FStar_Syntax_Syntax.n  in
                             (match uu____5894 with
                              | FStar_Syntax_Syntax.Tm_name x1 ->
                                  let s = [FStar_Syntax_Syntax.NT (x1, e)]
                                     in
                                  let s1 bv1 =
                                    let uu___383_5912 = bv1  in
                                    let uu____5913 =
                                      FStar_Syntax_Subst.subst s
                                        bv1.FStar_Syntax_Syntax.sort
                                       in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___383_5912.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___383_5912.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = uu____5913
                                    }  in
                                  let bvs1 = FStar_List.map s1 bvs  in
                                  let new_env = push_bvs e0 (bv :: bvs1)  in
                                  let new_goal =
                                    let uu___384_5921 =
                                      goal.FStar_Tactics_Types.goal_ctx_uvar
                                       in
                                    let uu____5922 =
                                      FStar_TypeChecker_Env.all_binders
                                        new_env
                                       in
                                    let uu____5929 =
                                      let uu____5932 =
                                        FStar_Tactics_Types.goal_type goal
                                         in
                                      FStar_Syntax_Subst.subst s uu____5932
                                       in
                                    {
                                      FStar_Syntax_Syntax.ctx_uvar_head =
                                        (uu___384_5921.FStar_Syntax_Syntax.ctx_uvar_head);
                                      FStar_Syntax_Syntax.ctx_uvar_gamma =
                                        (new_env.FStar_TypeChecker_Env.gamma);
                                      FStar_Syntax_Syntax.ctx_uvar_binders =
                                        uu____5922;
                                      FStar_Syntax_Syntax.ctx_uvar_typ =
                                        uu____5929;
                                      FStar_Syntax_Syntax.ctx_uvar_reason =
                                        (uu___384_5921.FStar_Syntax_Syntax.ctx_uvar_reason);
                                      FStar_Syntax_Syntax.ctx_uvar_should_check
                                        =
                                        (uu___384_5921.FStar_Syntax_Syntax.ctx_uvar_should_check);
                                      FStar_Syntax_Syntax.ctx_uvar_range =
                                        (uu___384_5921.FStar_Syntax_Syntax.ctx_uvar_range)
                                    }  in
                                  replace_cur
                                    (let uu___385_5935 = goal  in
                                     {
                                       FStar_Tactics_Types.goal_main_env =
                                         (uu___385_5935.FStar_Tactics_Types.goal_main_env);
                                       FStar_Tactics_Types.goal_ctx_uvar =
                                         new_goal;
                                       FStar_Tactics_Types.opts =
                                         (uu___385_5935.FStar_Tactics_Types.opts);
                                       FStar_Tactics_Types.is_guard =
                                         (uu___385_5935.FStar_Tactics_Types.is_guard)
                                     })
                              | uu____5936 ->
                                  fail
                                    "Not an equality hypothesis with a variable on the LHS")
                         | uu____5937 -> fail "Not an equality hypothesis")))
       in
    FStar_All.pipe_left (wrap_err "rewrite") uu____5824
  
let (rename_to : FStar_Syntax_Syntax.binder -> Prims.string -> unit tac) =
  fun b  ->
    fun s  ->
      let uu____5962 =
        let uu____5965 = cur_goal ()  in
        bind uu____5965
          (fun goal  ->
             let uu____5976 = b  in
             match uu____5976 with
             | (bv,uu____5980) ->
                 let bv' =
                   let uu____5982 =
                     let uu___386_5983 = bv  in
                     let uu____5984 =
                       FStar_Ident.mk_ident
                         (s,
                           ((bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange))
                        in
                     {
                       FStar_Syntax_Syntax.ppname = uu____5984;
                       FStar_Syntax_Syntax.index =
                         (uu___386_5983.FStar_Syntax_Syntax.index);
                       FStar_Syntax_Syntax.sort =
                         (uu___386_5983.FStar_Syntax_Syntax.sort)
                     }  in
                   FStar_Syntax_Syntax.freshen_bv uu____5982  in
                 let s1 =
                   let uu____5988 =
                     let uu____5989 =
                       let uu____5996 = FStar_Syntax_Syntax.bv_to_name bv'
                          in
                       (bv, uu____5996)  in
                     FStar_Syntax_Syntax.NT uu____5989  in
                   [uu____5988]  in
                 let uu____6001 = subst_goal bv bv' s1 goal  in
                 (match uu____6001 with
                  | FStar_Pervasives_Native.None  ->
                      fail "binder not found in environment"
                  | FStar_Pervasives_Native.Some goal1 -> replace_cur goal1))
         in
      FStar_All.pipe_left (wrap_err "rename_to") uu____5962
  
let (binder_retype : FStar_Syntax_Syntax.binder -> unit tac) =
  fun b  ->
    let uu____6020 =
      let uu____6023 = cur_goal ()  in
      bind uu____6023
        (fun goal  ->
           let uu____6032 = b  in
           match uu____6032 with
           | (bv,uu____6036) ->
               let uu____6037 =
                 let uu____6046 = FStar_Tactics_Types.goal_env goal  in
                 split_env bv uu____6046  in
               (match uu____6037 with
                | FStar_Pervasives_Native.None  ->
                    fail "binder is not present in environment"
                | FStar_Pervasives_Native.Some (e0,bvs) ->
                    let uu____6067 = FStar_Syntax_Util.type_u ()  in
                    (match uu____6067 with
                     | (ty,u) ->
                         let uu____6076 = new_uvar "binder_retype" e0 ty  in
                         bind uu____6076
                           (fun uu____6094  ->
                              match uu____6094 with
                              | (t',u_t') ->
                                  let bv'' =
                                    let uu___387_6104 = bv  in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___387_6104.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___387_6104.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = t'
                                    }  in
                                  let s =
                                    let uu____6108 =
                                      let uu____6109 =
                                        let uu____6116 =
                                          FStar_Syntax_Syntax.bv_to_name bv''
                                           in
                                        (bv, uu____6116)  in
                                      FStar_Syntax_Syntax.NT uu____6109  in
                                    [uu____6108]  in
                                  let bvs1 =
                                    FStar_List.map
                                      (fun b1  ->
                                         let uu___388_6128 = b1  in
                                         let uu____6129 =
                                           FStar_Syntax_Subst.subst s
                                             b1.FStar_Syntax_Syntax.sort
                                            in
                                         {
                                           FStar_Syntax_Syntax.ppname =
                                             (uu___388_6128.FStar_Syntax_Syntax.ppname);
                                           FStar_Syntax_Syntax.index =
                                             (uu___388_6128.FStar_Syntax_Syntax.index);
                                           FStar_Syntax_Syntax.sort =
                                             uu____6129
                                         }) bvs
                                     in
                                  let env' = push_bvs e0 (bv'' :: bvs1)  in
                                  bind __dismiss
                                    (fun uu____6136  ->
                                       let new_goal =
                                         let uu____6138 =
                                           FStar_Tactics_Types.goal_with_env
                                             goal env'
                                            in
                                         let uu____6139 =
                                           let uu____6140 =
                                             FStar_Tactics_Types.goal_type
                                               goal
                                              in
                                           FStar_Syntax_Subst.subst s
                                             uu____6140
                                            in
                                         FStar_Tactics_Types.goal_with_type
                                           uu____6138 uu____6139
                                          in
                                       let uu____6141 = add_goals [new_goal]
                                          in
                                       bind uu____6141
                                         (fun uu____6146  ->
                                            let uu____6147 =
                                              FStar_Syntax_Util.mk_eq2
                                                (FStar_Syntax_Syntax.U_succ u)
                                                ty
                                                bv.FStar_Syntax_Syntax.sort
                                                t'
                                               in
                                            add_irrelevant_goal
                                              "binder_retype equation" e0
                                              uu____6147
                                              goal.FStar_Tactics_Types.opts))))))
       in
    FStar_All.pipe_left (wrap_err "binder_retype") uu____6020
  
let (norm_binder_type :
  FStar_Syntax_Embeddings.norm_step Prims.list ->
    FStar_Syntax_Syntax.binder -> unit tac)
  =
  fun s  ->
    fun b  ->
      let uu____6170 =
        let uu____6173 = cur_goal ()  in
        bind uu____6173
          (fun goal  ->
             let uu____6182 = b  in
             match uu____6182 with
             | (bv,uu____6186) ->
                 let uu____6187 =
                   let uu____6196 = FStar_Tactics_Types.goal_env goal  in
                   split_env bv uu____6196  in
                 (match uu____6187 with
                  | FStar_Pervasives_Native.None  ->
                      fail "binder is not present in environment"
                  | FStar_Pervasives_Native.Some (e0,bvs) ->
                      let steps =
                        let uu____6220 =
                          FStar_TypeChecker_Normalize.tr_norm_steps s  in
                        FStar_List.append
                          [FStar_TypeChecker_Normalize.Reify;
                          FStar_TypeChecker_Normalize.UnfoldTac] uu____6220
                         in
                      let sort' =
                        normalize steps e0 bv.FStar_Syntax_Syntax.sort  in
                      let bv' =
                        let uu___389_6225 = bv  in
                        {
                          FStar_Syntax_Syntax.ppname =
                            (uu___389_6225.FStar_Syntax_Syntax.ppname);
                          FStar_Syntax_Syntax.index =
                            (uu___389_6225.FStar_Syntax_Syntax.index);
                          FStar_Syntax_Syntax.sort = sort'
                        }  in
                      let env' = push_bvs e0 (bv' :: bvs)  in
                      let uu____6227 =
                        FStar_Tactics_Types.goal_with_env goal env'  in
                      replace_cur uu____6227))
         in
      FStar_All.pipe_left (wrap_err "norm_binder_type") uu____6170
  
let (revert : unit -> unit tac) =
  fun uu____6238  ->
    let uu____6241 = cur_goal ()  in
    bind uu____6241
      (fun goal  ->
         let uu____6247 =
           let uu____6254 = FStar_Tactics_Types.goal_env goal  in
           FStar_TypeChecker_Env.pop_bv uu____6254  in
         match uu____6247 with
         | FStar_Pervasives_Native.None  ->
             fail "Cannot revert; empty context"
         | FStar_Pervasives_Native.Some (x,env') ->
             let typ' =
               let uu____6270 =
                 let uu____6273 = FStar_Tactics_Types.goal_type goal  in
                 FStar_Syntax_Syntax.mk_Total uu____6273  in
               FStar_Syntax_Util.arrow [(x, FStar_Pervasives_Native.None)]
                 uu____6270
                in
             let uu____6282 = new_uvar "revert" env' typ'  in
             bind uu____6282
               (fun uu____6297  ->
                  match uu____6297 with
                  | (r,u_r) ->
                      let uu____6306 =
                        let uu____6309 =
                          let uu____6310 =
                            let uu____6311 =
                              FStar_Tactics_Types.goal_type goal  in
                            uu____6311.FStar_Syntax_Syntax.pos  in
                          let uu____6314 =
                            let uu____6319 =
                              let uu____6320 =
                                let uu____6327 =
                                  FStar_Syntax_Syntax.bv_to_name x  in
                                FStar_Syntax_Syntax.as_arg uu____6327  in
                              [uu____6320]  in
                            FStar_Syntax_Syntax.mk_Tm_app r uu____6319  in
                          uu____6314 FStar_Pervasives_Native.None uu____6310
                           in
                        set_solution goal uu____6309  in
                      bind uu____6306
                        (fun uu____6344  ->
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
      let uu____6356 = FStar_Syntax_Free.names t  in
      FStar_Util.set_mem bv uu____6356
  
let rec (clear : FStar_Syntax_Syntax.binder -> unit tac) =
  fun b  ->
    let bv = FStar_Pervasives_Native.fst b  in
    let uu____6369 = cur_goal ()  in
    bind uu____6369
      (fun goal  ->
         mlog
           (fun uu____6377  ->
              let uu____6378 = FStar_Syntax_Print.binder_to_string b  in
              let uu____6379 =
                let uu____6380 =
                  let uu____6381 =
                    let uu____6388 = FStar_Tactics_Types.goal_env goal  in
                    FStar_TypeChecker_Env.all_binders uu____6388  in
                  FStar_All.pipe_right uu____6381 FStar_List.length  in
                FStar_All.pipe_right uu____6380 FStar_Util.string_of_int  in
              FStar_Util.print2 "Clear of (%s), env has %s binders\n"
                uu____6378 uu____6379)
           (fun uu____6401  ->
              let uu____6402 =
                let uu____6411 = FStar_Tactics_Types.goal_env goal  in
                split_env bv uu____6411  in
              match uu____6402 with
              | FStar_Pervasives_Native.None  ->
                  fail "Cannot clear; binder not in environment"
              | FStar_Pervasives_Native.Some (e',bvs) ->
                  let rec check1 bvs1 =
                    match bvs1 with
                    | [] -> ret ()
                    | bv'::bvs2 ->
                        let uu____6450 =
                          free_in bv bv'.FStar_Syntax_Syntax.sort  in
                        if uu____6450
                        then
                          let uu____6453 =
                            let uu____6454 =
                              FStar_Syntax_Print.bv_to_string bv'  in
                            FStar_Util.format1
                              "Cannot clear; binder present in the type of %s"
                              uu____6454
                             in
                          fail uu____6453
                        else check1 bvs2
                     in
                  let uu____6456 =
                    let uu____6457 = FStar_Tactics_Types.goal_type goal  in
                    free_in bv uu____6457  in
                  if uu____6456
                  then fail "Cannot clear; binder present in goal"
                  else
                    (let uu____6461 = check1 bvs  in
                     bind uu____6461
                       (fun uu____6467  ->
                          let env' = push_bvs e' bvs  in
                          let uu____6469 =
                            let uu____6476 =
                              FStar_Tactics_Types.goal_type goal  in
                            new_uvar "clear.witness" env' uu____6476  in
                          bind uu____6469
                            (fun uu____6485  ->
                               match uu____6485 with
                               | (ut,uvar_ut) ->
                                   let uu____6494 = set_solution goal ut  in
                                   bind uu____6494
                                     (fun uu____6499  ->
                                        let uu____6500 =
                                          FStar_Tactics_Types.mk_goal env'
                                            uvar_ut
                                            goal.FStar_Tactics_Types.opts
                                            goal.FStar_Tactics_Types.is_guard
                                           in
                                        replace_cur uu____6500))))))
  
let (clear_top : unit -> unit tac) =
  fun uu____6507  ->
    let uu____6510 = cur_goal ()  in
    bind uu____6510
      (fun goal  ->
         let uu____6516 =
           let uu____6523 = FStar_Tactics_Types.goal_env goal  in
           FStar_TypeChecker_Env.pop_bv uu____6523  in
         match uu____6516 with
         | FStar_Pervasives_Native.None  ->
             fail "Cannot clear; empty context"
         | FStar_Pervasives_Native.Some (x,uu____6531) ->
             let uu____6536 = FStar_Syntax_Syntax.mk_binder x  in
             clear uu____6536)
  
let (prune : Prims.string -> unit tac) =
  fun s  ->
    let uu____6546 = cur_goal ()  in
    bind uu____6546
      (fun g  ->
         let ctx = FStar_Tactics_Types.goal_env g  in
         let ctx' =
           let uu____6556 = FStar_Ident.path_of_text s  in
           FStar_TypeChecker_Env.rem_proof_ns ctx uu____6556  in
         let g' = FStar_Tactics_Types.goal_with_env g ctx'  in
         bind __dismiss (fun uu____6559  -> add_goals [g']))
  
let (addns : Prims.string -> unit tac) =
  fun s  ->
    let uu____6569 = cur_goal ()  in
    bind uu____6569
      (fun g  ->
         let ctx = FStar_Tactics_Types.goal_env g  in
         let ctx' =
           let uu____6579 = FStar_Ident.path_of_text s  in
           FStar_TypeChecker_Env.add_proof_ns ctx uu____6579  in
         let g' = FStar_Tactics_Types.goal_with_env g ctx'  in
         bind __dismiss (fun uu____6582  -> add_goals [g']))
  
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
            let uu____6622 = FStar_Syntax_Subst.compress t  in
            uu____6622.FStar_Syntax_Syntax.n  in
          let uu____6625 =
            if d = FStar_Tactics_Types.TopDown
            then
              f env
                (let uu___393_6631 = t  in
                 {
                   FStar_Syntax_Syntax.n = tn;
                   FStar_Syntax_Syntax.pos =
                     (uu___393_6631.FStar_Syntax_Syntax.pos);
                   FStar_Syntax_Syntax.vars =
                     (uu___393_6631.FStar_Syntax_Syntax.vars)
                 })
            else ret t  in
          bind uu____6625
            (fun t1  ->
               let ff = tac_fold_env d f env  in
               let tn1 =
                 let uu____6647 =
                   let uu____6648 = FStar_Syntax_Subst.compress t1  in
                   uu____6648.FStar_Syntax_Syntax.n  in
                 match uu____6647 with
                 | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
                     let uu____6675 = ff hd1  in
                     bind uu____6675
                       (fun hd2  ->
                          let fa uu____6697 =
                            match uu____6697 with
                            | (a,q) ->
                                let uu____6710 = ff a  in
                                bind uu____6710 (fun a1  -> ret (a1, q))
                             in
                          let uu____6723 = mapM fa args  in
                          bind uu____6723
                            (fun args1  ->
                               ret (FStar_Syntax_Syntax.Tm_app (hd2, args1))))
                 | FStar_Syntax_Syntax.Tm_abs (bs,t2,k) ->
                     let uu____6789 = FStar_Syntax_Subst.open_term bs t2  in
                     (match uu____6789 with
                      | (bs1,t') ->
                          let uu____6798 =
                            let uu____6801 =
                              FStar_TypeChecker_Env.push_binders env bs1  in
                            tac_fold_env d f uu____6801 t'  in
                          bind uu____6798
                            (fun t''  ->
                               let uu____6805 =
                                 let uu____6806 =
                                   let uu____6823 =
                                     FStar_Syntax_Subst.close_binders bs1  in
                                   let uu____6830 =
                                     FStar_Syntax_Subst.close bs1 t''  in
                                   (uu____6823, uu____6830, k)  in
                                 FStar_Syntax_Syntax.Tm_abs uu____6806  in
                               ret uu____6805))
                 | FStar_Syntax_Syntax.Tm_arrow (bs,k) -> ret tn
                 | FStar_Syntax_Syntax.Tm_match (hd1,brs) ->
                     let uu____6899 = ff hd1  in
                     bind uu____6899
                       (fun hd2  ->
                          let ffb br =
                            let uu____6914 =
                              FStar_Syntax_Subst.open_branch br  in
                            match uu____6914 with
                            | (pat,w,e) ->
                                let bvs = FStar_Syntax_Syntax.pat_bvs pat  in
                                let ff1 =
                                  let uu____6946 =
                                    FStar_TypeChecker_Env.push_bvs env bvs
                                     in
                                  tac_fold_env d f uu____6946  in
                                let uu____6947 = ff1 e  in
                                bind uu____6947
                                  (fun e1  ->
                                     let br1 =
                                       FStar_Syntax_Subst.close_branch
                                         (pat, w, e1)
                                        in
                                     ret br1)
                             in
                          let uu____6962 = mapM ffb brs  in
                          bind uu____6962
                            (fun brs1  ->
                               ret (FStar_Syntax_Syntax.Tm_match (hd2, brs1))))
                 | FStar_Syntax_Syntax.Tm_let
                     ((false
                       ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inl bv;
                          FStar_Syntax_Syntax.lbunivs = uu____7006;
                          FStar_Syntax_Syntax.lbtyp = uu____7007;
                          FStar_Syntax_Syntax.lbeff = uu____7008;
                          FStar_Syntax_Syntax.lbdef = def;
                          FStar_Syntax_Syntax.lbattrs = uu____7010;
                          FStar_Syntax_Syntax.lbpos = uu____7011;_}::[]),e)
                     ->
                     let lb =
                       let uu____7036 =
                         let uu____7037 = FStar_Syntax_Subst.compress t1  in
                         uu____7037.FStar_Syntax_Syntax.n  in
                       match uu____7036 with
                       | FStar_Syntax_Syntax.Tm_let
                           ((false ,lb::[]),uu____7041) -> lb
                       | uu____7054 -> failwith "impossible"  in
                     let fflb lb1 =
                       let uu____7063 = ff lb1.FStar_Syntax_Syntax.lbdef  in
                       bind uu____7063
                         (fun def1  ->
                            ret
                              (let uu___390_7069 = lb1  in
                               {
                                 FStar_Syntax_Syntax.lbname =
                                   (uu___390_7069.FStar_Syntax_Syntax.lbname);
                                 FStar_Syntax_Syntax.lbunivs =
                                   (uu___390_7069.FStar_Syntax_Syntax.lbunivs);
                                 FStar_Syntax_Syntax.lbtyp =
                                   (uu___390_7069.FStar_Syntax_Syntax.lbtyp);
                                 FStar_Syntax_Syntax.lbeff =
                                   (uu___390_7069.FStar_Syntax_Syntax.lbeff);
                                 FStar_Syntax_Syntax.lbdef = def1;
                                 FStar_Syntax_Syntax.lbattrs =
                                   (uu___390_7069.FStar_Syntax_Syntax.lbattrs);
                                 FStar_Syntax_Syntax.lbpos =
                                   (uu___390_7069.FStar_Syntax_Syntax.lbpos)
                               }))
                        in
                     let uu____7070 = fflb lb  in
                     bind uu____7070
                       (fun lb1  ->
                          let uu____7080 =
                            let uu____7085 =
                              let uu____7086 =
                                FStar_Syntax_Syntax.mk_binder bv  in
                              [uu____7086]  in
                            FStar_Syntax_Subst.open_term uu____7085 e  in
                          match uu____7080 with
                          | (bs,e1) ->
                              let ff1 =
                                let uu____7110 =
                                  FStar_TypeChecker_Env.push_binders env bs
                                   in
                                tac_fold_env d f uu____7110  in
                              let uu____7111 = ff1 e1  in
                              bind uu____7111
                                (fun e2  ->
                                   let e3 = FStar_Syntax_Subst.close bs e2
                                      in
                                   ret
                                     (FStar_Syntax_Syntax.Tm_let
                                        ((false, [lb1]), e3))))
                 | FStar_Syntax_Syntax.Tm_let ((true ,lbs),e) ->
                     let fflb lb =
                       let uu____7152 = ff lb.FStar_Syntax_Syntax.lbdef  in
                       bind uu____7152
                         (fun def  ->
                            ret
                              (let uu___391_7158 = lb  in
                               {
                                 FStar_Syntax_Syntax.lbname =
                                   (uu___391_7158.FStar_Syntax_Syntax.lbname);
                                 FStar_Syntax_Syntax.lbunivs =
                                   (uu___391_7158.FStar_Syntax_Syntax.lbunivs);
                                 FStar_Syntax_Syntax.lbtyp =
                                   (uu___391_7158.FStar_Syntax_Syntax.lbtyp);
                                 FStar_Syntax_Syntax.lbeff =
                                   (uu___391_7158.FStar_Syntax_Syntax.lbeff);
                                 FStar_Syntax_Syntax.lbdef = def;
                                 FStar_Syntax_Syntax.lbattrs =
                                   (uu___391_7158.FStar_Syntax_Syntax.lbattrs);
                                 FStar_Syntax_Syntax.lbpos =
                                   (uu___391_7158.FStar_Syntax_Syntax.lbpos)
                               }))
                        in
                     let uu____7159 = FStar_Syntax_Subst.open_let_rec lbs e
                        in
                     (match uu____7159 with
                      | (lbs1,e1) ->
                          let uu____7174 = mapM fflb lbs1  in
                          bind uu____7174
                            (fun lbs2  ->
                               let uu____7186 = ff e1  in
                               bind uu____7186
                                 (fun e2  ->
                                    let uu____7194 =
                                      FStar_Syntax_Subst.close_let_rec lbs2
                                        e2
                                       in
                                    match uu____7194 with
                                    | (lbs3,e3) ->
                                        ret
                                          (FStar_Syntax_Syntax.Tm_let
                                             ((true, lbs3), e3)))))
                 | FStar_Syntax_Syntax.Tm_ascribed (t2,asc,eff) ->
                     let uu____7262 = ff t2  in
                     bind uu____7262
                       (fun t3  ->
                          ret
                            (FStar_Syntax_Syntax.Tm_ascribed (t3, asc, eff)))
                 | FStar_Syntax_Syntax.Tm_meta (t2,m) ->
                     let uu____7293 = ff t2  in
                     bind uu____7293
                       (fun t3  -> ret (FStar_Syntax_Syntax.Tm_meta (t3, m)))
                 | uu____7300 -> ret tn  in
               bind tn1
                 (fun tn2  ->
                    let t' =
                      let uu___392_7307 = t1  in
                      {
                        FStar_Syntax_Syntax.n = tn2;
                        FStar_Syntax_Syntax.pos =
                          (uu___392_7307.FStar_Syntax_Syntax.pos);
                        FStar_Syntax_Syntax.vars =
                          (uu___392_7307.FStar_Syntax_Syntax.vars)
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
            let uu____7344 = FStar_TypeChecker_TcTerm.tc_term env t  in
            match uu____7344 with
            | (t1,lcomp,g) ->
                let uu____7356 =
                  (let uu____7359 =
                     FStar_Syntax_Util.is_pure_or_ghost_lcomp lcomp  in
                   Prims.op_Negation uu____7359) ||
                    (let uu____7361 = FStar_TypeChecker_Rel.is_trivial g  in
                     Prims.op_Negation uu____7361)
                   in
                if uu____7356
                then ret t1
                else
                  (let rewrite_eq =
                     let typ = lcomp.FStar_Syntax_Syntax.res_typ  in
                     let uu____7369 = new_uvar "pointwise_rec" env typ  in
                     bind uu____7369
                       (fun uu____7385  ->
                          match uu____7385 with
                          | (ut,uvar_ut) ->
                              (log ps
                                 (fun uu____7398  ->
                                    let uu____7399 =
                                      FStar_Syntax_Print.term_to_string t1
                                       in
                                    let uu____7400 =
                                      FStar_Syntax_Print.term_to_string ut
                                       in
                                    FStar_Util.print2
                                      "Pointwise_rec: making equality\n\t%s ==\n\t%s\n"
                                      uu____7399 uu____7400);
                               (let uu____7401 =
                                  let uu____7404 =
                                    let uu____7405 =
                                      FStar_TypeChecker_TcTerm.universe_of
                                        env typ
                                       in
                                    FStar_Syntax_Util.mk_eq2 uu____7405 typ
                                      t1 ut
                                     in
                                  add_irrelevant_goal
                                    "pointwise_rec equation" env uu____7404
                                    opts
                                   in
                                bind uu____7401
                                  (fun uu____7408  ->
                                     let uu____7409 =
                                       bind tau
                                         (fun uu____7415  ->
                                            let ut1 =
                                              FStar_TypeChecker_Normalize.reduce_uvar_solutions
                                                env ut
                                               in
                                            log ps
                                              (fun uu____7421  ->
                                                 let uu____7422 =
                                                   FStar_Syntax_Print.term_to_string
                                                     t1
                                                    in
                                                 let uu____7423 =
                                                   FStar_Syntax_Print.term_to_string
                                                     ut1
                                                    in
                                                 FStar_Util.print2
                                                   "Pointwise_rec: succeeded rewriting\n\t%s to\n\t%s\n"
                                                   uu____7422 uu____7423);
                                            ret ut1)
                                        in
                                     focus uu____7409))))
                      in
                   let uu____7424 = trytac' rewrite_eq  in
                   bind uu____7424
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
          let uu____7622 = FStar_Syntax_Subst.compress t  in
          maybe_continue ctrl uu____7622
            (fun t1  ->
               let uu____7630 =
                 f env
                   (let uu___396_7639 = t1  in
                    {
                      FStar_Syntax_Syntax.n = (t1.FStar_Syntax_Syntax.n);
                      FStar_Syntax_Syntax.pos =
                        (uu___396_7639.FStar_Syntax_Syntax.pos);
                      FStar_Syntax_Syntax.vars =
                        (uu___396_7639.FStar_Syntax_Syntax.vars)
                    })
                  in
               bind uu____7630
                 (fun uu____7655  ->
                    match uu____7655 with
                    | (t2,ctrl1) ->
                        maybe_continue ctrl1 t2
                          (fun t3  ->
                             let uu____7678 =
                               let uu____7679 =
                                 FStar_Syntax_Subst.compress t3  in
                               uu____7679.FStar_Syntax_Syntax.n  in
                             match uu____7678 with
                             | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
                                 let uu____7712 =
                                   ctrl_tac_fold f env ctrl1 hd1  in
                                 bind uu____7712
                                   (fun uu____7737  ->
                                      match uu____7737 with
                                      | (hd2,ctrl2) ->
                                          let ctrl3 = keep_going ctrl2  in
                                          let uu____7753 =
                                            ctrl_tac_fold_args f env ctrl3
                                              args
                                             in
                                          bind uu____7753
                                            (fun uu____7780  ->
                                               match uu____7780 with
                                               | (args1,ctrl4) ->
                                                   ret
                                                     ((let uu___394_7810 = t3
                                                          in
                                                       {
                                                         FStar_Syntax_Syntax.n
                                                           =
                                                           (FStar_Syntax_Syntax.Tm_app
                                                              (hd2, args1));
                                                         FStar_Syntax_Syntax.pos
                                                           =
                                                           (uu___394_7810.FStar_Syntax_Syntax.pos);
                                                         FStar_Syntax_Syntax.vars
                                                           =
                                                           (uu___394_7810.FStar_Syntax_Syntax.vars)
                                                       }), ctrl4)))
                             | FStar_Syntax_Syntax.Tm_abs (bs,t4,k) ->
                                 let uu____7846 =
                                   FStar_Syntax_Subst.open_term bs t4  in
                                 (match uu____7846 with
                                  | (bs1,t') ->
                                      let uu____7861 =
                                        let uu____7868 =
                                          FStar_TypeChecker_Env.push_binders
                                            env bs1
                                           in
                                        ctrl_tac_fold f uu____7868 ctrl1 t'
                                         in
                                      bind uu____7861
                                        (fun uu____7886  ->
                                           match uu____7886 with
                                           | (t'',ctrl2) ->
                                               let uu____7901 =
                                                 let uu____7908 =
                                                   let uu___395_7911 = t4  in
                                                   let uu____7914 =
                                                     let uu____7915 =
                                                       let uu____7932 =
                                                         FStar_Syntax_Subst.close_binders
                                                           bs1
                                                          in
                                                       let uu____7939 =
                                                         FStar_Syntax_Subst.close
                                                           bs1 t''
                                                          in
                                                       (uu____7932,
                                                         uu____7939, k)
                                                        in
                                                     FStar_Syntax_Syntax.Tm_abs
                                                       uu____7915
                                                      in
                                                   {
                                                     FStar_Syntax_Syntax.n =
                                                       uu____7914;
                                                     FStar_Syntax_Syntax.pos
                                                       =
                                                       (uu___395_7911.FStar_Syntax_Syntax.pos);
                                                     FStar_Syntax_Syntax.vars
                                                       =
                                                       (uu___395_7911.FStar_Syntax_Syntax.vars)
                                                   }  in
                                                 (uu____7908, ctrl2)  in
                                               ret uu____7901))
                             | FStar_Syntax_Syntax.Tm_arrow (bs,k) ->
                                 ret (t3, ctrl1)
                             | uu____7986 -> ret (t3, ctrl1))))

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
              let uu____8029 = ctrl_tac_fold f env ctrl t  in
              bind uu____8029
                (fun uu____8053  ->
                   match uu____8053 with
                   | (t1,ctrl1) ->
                       let uu____8068 = ctrl_tac_fold_args f env ctrl1 ts1
                          in
                       bind uu____8068
                         (fun uu____8095  ->
                            match uu____8095 with
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
              let uu____8177 =
                let uu____8184 =
                  add_irrelevant_goal "dummy" env FStar_Syntax_Util.t_true
                    opts
                   in
                bind uu____8184
                  (fun uu____8193  ->
                     let uu____8194 = ctrl t1  in
                     bind uu____8194
                       (fun res  ->
                          let uu____8217 = trivial ()  in
                          bind uu____8217 (fun uu____8225  -> ret res)))
                 in
              bind uu____8177
                (fun uu____8241  ->
                   match uu____8241 with
                   | (should_rewrite,ctrl1) ->
                       if Prims.op_Negation should_rewrite
                       then ret (t1, ctrl1)
                       else
                         (let uu____8265 =
                            FStar_TypeChecker_TcTerm.tc_term env t1  in
                          match uu____8265 with
                          | (t2,lcomp,g) ->
                              let uu____8281 =
                                (let uu____8284 =
                                   FStar_Syntax_Util.is_pure_or_ghost_lcomp
                                     lcomp
                                    in
                                 Prims.op_Negation uu____8284) ||
                                  (let uu____8286 =
                                     FStar_TypeChecker_Rel.is_trivial g  in
                                   Prims.op_Negation uu____8286)
                                 in
                              if uu____8281
                              then ret (t2, globalStop)
                              else
                                (let typ = lcomp.FStar_Syntax_Syntax.res_typ
                                    in
                                 let uu____8299 =
                                   new_uvar "pointwise_rec" env typ  in
                                 bind uu____8299
                                   (fun uu____8319  ->
                                      match uu____8319 with
                                      | (ut,uvar_ut) ->
                                          (log ps
                                             (fun uu____8336  ->
                                                let uu____8337 =
                                                  FStar_Syntax_Print.term_to_string
                                                    t2
                                                   in
                                                let uu____8338 =
                                                  FStar_Syntax_Print.term_to_string
                                                    ut
                                                   in
                                                FStar_Util.print2
                                                  "Pointwise_rec: making equality\n\t%s ==\n\t%s\n"
                                                  uu____8337 uu____8338);
                                           (let uu____8339 =
                                              let uu____8342 =
                                                let uu____8343 =
                                                  FStar_TypeChecker_TcTerm.universe_of
                                                    env typ
                                                   in
                                                FStar_Syntax_Util.mk_eq2
                                                  uu____8343 typ t2 ut
                                                 in
                                              add_irrelevant_goal
                                                "rewrite_rec equation" env
                                                uu____8342 opts
                                               in
                                            bind uu____8339
                                              (fun uu____8350  ->
                                                 let uu____8351 =
                                                   bind rewriter
                                                     (fun uu____8365  ->
                                                        let ut1 =
                                                          FStar_TypeChecker_Normalize.reduce_uvar_solutions
                                                            env ut
                                                           in
                                                        log ps
                                                          (fun uu____8371  ->
                                                             let uu____8372 =
                                                               FStar_Syntax_Print.term_to_string
                                                                 t2
                                                                in
                                                             let uu____8373 =
                                                               FStar_Syntax_Print.term_to_string
                                                                 ut1
                                                                in
                                                             FStar_Util.print2
                                                               "rewrite_rec: succeeded rewriting\n\t%s to\n\t%s\n"
                                                               uu____8372
                                                               uu____8373);
                                                        ret (ut1, ctrl1))
                                                    in
                                                 focus uu____8351)))))))
  
let (topdown_rewrite :
  (FStar_Syntax_Syntax.term ->
     (Prims.bool,FStar_BigInt.t) FStar_Pervasives_Native.tuple2 tac)
    -> unit tac -> unit tac)
  =
  fun ctrl  ->
    fun rewriter  ->
      let uu____8414 =
        bind get
          (fun ps  ->
             let uu____8424 =
               match ps.FStar_Tactics_Types.goals with
               | g::gs -> (g, gs)
               | [] -> failwith "no goals"  in
             match uu____8424 with
             | (g,gs) ->
                 let gt1 = FStar_Tactics_Types.goal_type g  in
                 (log ps
                    (fun uu____8461  ->
                       let uu____8462 = FStar_Syntax_Print.term_to_string gt1
                          in
                       FStar_Util.print1 "Topdown_rewrite starting with %s\n"
                         uu____8462);
                  bind dismiss_all
                    (fun uu____8465  ->
                       let uu____8466 =
                         let uu____8473 = FStar_Tactics_Types.goal_env g  in
                         ctrl_tac_fold
                           (rewrite_rec ps ctrl rewriter
                              g.FStar_Tactics_Types.opts) uu____8473
                           keepGoing gt1
                          in
                       bind uu____8466
                         (fun uu____8485  ->
                            match uu____8485 with
                            | (gt',uu____8493) ->
                                (log ps
                                   (fun uu____8497  ->
                                      let uu____8498 =
                                        FStar_Syntax_Print.term_to_string gt'
                                         in
                                      FStar_Util.print1
                                        "Topdown_rewrite seems to have succeded with %s\n"
                                        uu____8498);
                                 (let uu____8499 = push_goals gs  in
                                  bind uu____8499
                                    (fun uu____8504  ->
                                       let uu____8505 =
                                         let uu____8508 =
                                           FStar_Tactics_Types.goal_with_type
                                             g gt'
                                            in
                                         [uu____8508]  in
                                       add_goals uu____8505)))))))
         in
      FStar_All.pipe_left (wrap_err "topdown_rewrite") uu____8414
  
let (pointwise : FStar_Tactics_Types.direction -> unit tac -> unit tac) =
  fun d  ->
    fun tau  ->
      let uu____8531 =
        bind get
          (fun ps  ->
             let uu____8541 =
               match ps.FStar_Tactics_Types.goals with
               | g::gs -> (g, gs)
               | [] -> failwith "no goals"  in
             match uu____8541 with
             | (g,gs) ->
                 let gt1 = FStar_Tactics_Types.goal_type g  in
                 (log ps
                    (fun uu____8578  ->
                       let uu____8579 = FStar_Syntax_Print.term_to_string gt1
                          in
                       FStar_Util.print1 "Pointwise starting with %s\n"
                         uu____8579);
                  bind dismiss_all
                    (fun uu____8582  ->
                       let uu____8583 =
                         let uu____8586 = FStar_Tactics_Types.goal_env g  in
                         tac_fold_env d
                           (pointwise_rec ps tau g.FStar_Tactics_Types.opts)
                           uu____8586 gt1
                          in
                       bind uu____8583
                         (fun gt'  ->
                            log ps
                              (fun uu____8594  ->
                                 let uu____8595 =
                                   FStar_Syntax_Print.term_to_string gt'  in
                                 FStar_Util.print1
                                   "Pointwise seems to have succeded with %s\n"
                                   uu____8595);
                            (let uu____8596 = push_goals gs  in
                             bind uu____8596
                               (fun uu____8601  ->
                                  let uu____8602 =
                                    let uu____8605 =
                                      FStar_Tactics_Types.goal_with_type g
                                        gt'
                                       in
                                    [uu____8605]  in
                                  add_goals uu____8602))))))
         in
      FStar_All.pipe_left (wrap_err "pointwise") uu____8531
  
let (trefl : unit -> unit tac) =
  fun uu____8616  ->
    let uu____8619 =
      let uu____8622 = cur_goal ()  in
      bind uu____8622
        (fun g  ->
           let uu____8640 =
             let uu____8645 = FStar_Tactics_Types.goal_type g  in
             FStar_Syntax_Util.un_squash uu____8645  in
           match uu____8640 with
           | FStar_Pervasives_Native.Some t ->
               let uu____8653 = FStar_Syntax_Util.head_and_args' t  in
               (match uu____8653 with
                | (hd1,args) ->
                    let uu____8686 =
                      let uu____8697 =
                        let uu____8698 = FStar_Syntax_Util.un_uinst hd1  in
                        uu____8698.FStar_Syntax_Syntax.n  in
                      (uu____8697, args)  in
                    (match uu____8686 with
                     | (FStar_Syntax_Syntax.Tm_fvar
                        fv,uu____8710::(l,uu____8712)::(r,uu____8714)::[])
                         when
                         FStar_Syntax_Syntax.fv_eq_lid fv
                           FStar_Parser_Const.eq2_lid
                         ->
                         let uu____8741 =
                           let uu____8744 = FStar_Tactics_Types.goal_env g
                              in
                           do_unify uu____8744 l r  in
                         bind uu____8741
                           (fun b  ->
                              if Prims.op_Negation b
                              then
                                let uu____8751 =
                                  let uu____8752 =
                                    FStar_Tactics_Types.goal_env g  in
                                  tts uu____8752 l  in
                                let uu____8753 =
                                  let uu____8754 =
                                    FStar_Tactics_Types.goal_env g  in
                                  tts uu____8754 r  in
                                fail2 "not a trivial equality (%s vs %s)"
                                  uu____8751 uu____8753
                              else solve' g FStar_Syntax_Util.exp_unit)
                     | (hd2,uu____8757) ->
                         let uu____8770 =
                           let uu____8771 = FStar_Tactics_Types.goal_env g
                              in
                           tts uu____8771 t  in
                         fail1 "trefl: not an equality (%s)" uu____8770))
           | FStar_Pervasives_Native.None  -> fail "not an irrelevant goal")
       in
    FStar_All.pipe_left (wrap_err "trefl") uu____8619
  
let (dup : unit -> unit tac) =
  fun uu____8784  ->
    let uu____8787 = cur_goal ()  in
    bind uu____8787
      (fun g  ->
         let uu____8793 =
           let uu____8800 = FStar_Tactics_Types.goal_env g  in
           let uu____8801 = FStar_Tactics_Types.goal_type g  in
           new_uvar "dup" uu____8800 uu____8801  in
         bind uu____8793
           (fun uu____8810  ->
              match uu____8810 with
              | (u,u_uvar) ->
                  let g' =
                    let uu___397_8820 = g  in
                    {
                      FStar_Tactics_Types.goal_main_env =
                        (uu___397_8820.FStar_Tactics_Types.goal_main_env);
                      FStar_Tactics_Types.goal_ctx_uvar = u_uvar;
                      FStar_Tactics_Types.opts =
                        (uu___397_8820.FStar_Tactics_Types.opts);
                      FStar_Tactics_Types.is_guard =
                        (uu___397_8820.FStar_Tactics_Types.is_guard)
                    }  in
                  bind __dismiss
                    (fun uu____8823  ->
                       let uu____8824 =
                         let uu____8827 = FStar_Tactics_Types.goal_env g  in
                         let uu____8828 =
                           let uu____8829 =
                             let uu____8830 = FStar_Tactics_Types.goal_env g
                                in
                             let uu____8831 = FStar_Tactics_Types.goal_type g
                                in
                             FStar_TypeChecker_TcTerm.universe_of uu____8830
                               uu____8831
                              in
                           let uu____8832 = FStar_Tactics_Types.goal_type g
                              in
                           let uu____8833 =
                             FStar_Tactics_Types.goal_witness g  in
                           FStar_Syntax_Util.mk_eq2 uu____8829 uu____8832 u
                             uu____8833
                            in
                         add_irrelevant_goal "dup equation" uu____8827
                           uu____8828 g.FStar_Tactics_Types.opts
                          in
                       bind uu____8824
                         (fun uu____8836  ->
                            let uu____8837 = add_goals [g']  in
                            bind uu____8837 (fun uu____8841  -> ret ())))))
  
let (flip : unit -> unit tac) =
  fun uu____8848  ->
    bind get
      (fun ps  ->
         match ps.FStar_Tactics_Types.goals with
         | g1::g2::gs ->
             set
               (let uu___398_8865 = ps  in
                {
                  FStar_Tactics_Types.main_context =
                    (uu___398_8865.FStar_Tactics_Types.main_context);
                  FStar_Tactics_Types.main_goal =
                    (uu___398_8865.FStar_Tactics_Types.main_goal);
                  FStar_Tactics_Types.all_implicits =
                    (uu___398_8865.FStar_Tactics_Types.all_implicits);
                  FStar_Tactics_Types.goals = (g2 :: g1 :: gs);
                  FStar_Tactics_Types.smt_goals =
                    (uu___398_8865.FStar_Tactics_Types.smt_goals);
                  FStar_Tactics_Types.depth =
                    (uu___398_8865.FStar_Tactics_Types.depth);
                  FStar_Tactics_Types.__dump =
                    (uu___398_8865.FStar_Tactics_Types.__dump);
                  FStar_Tactics_Types.psc =
                    (uu___398_8865.FStar_Tactics_Types.psc);
                  FStar_Tactics_Types.entry_range =
                    (uu___398_8865.FStar_Tactics_Types.entry_range);
                  FStar_Tactics_Types.guard_policy =
                    (uu___398_8865.FStar_Tactics_Types.guard_policy);
                  FStar_Tactics_Types.freshness =
                    (uu___398_8865.FStar_Tactics_Types.freshness);
                  FStar_Tactics_Types.tac_verb_dbg =
                    (uu___398_8865.FStar_Tactics_Types.tac_verb_dbg)
                })
         | uu____8866 -> fail "flip: less than 2 goals")
  
let (later : unit -> unit tac) =
  fun uu____8875  ->
    bind get
      (fun ps  ->
         match ps.FStar_Tactics_Types.goals with
         | [] -> ret ()
         | g::gs ->
             set
               (let uu___399_8888 = ps  in
                {
                  FStar_Tactics_Types.main_context =
                    (uu___399_8888.FStar_Tactics_Types.main_context);
                  FStar_Tactics_Types.main_goal =
                    (uu___399_8888.FStar_Tactics_Types.main_goal);
                  FStar_Tactics_Types.all_implicits =
                    (uu___399_8888.FStar_Tactics_Types.all_implicits);
                  FStar_Tactics_Types.goals = (FStar_List.append gs [g]);
                  FStar_Tactics_Types.smt_goals =
                    (uu___399_8888.FStar_Tactics_Types.smt_goals);
                  FStar_Tactics_Types.depth =
                    (uu___399_8888.FStar_Tactics_Types.depth);
                  FStar_Tactics_Types.__dump =
                    (uu___399_8888.FStar_Tactics_Types.__dump);
                  FStar_Tactics_Types.psc =
                    (uu___399_8888.FStar_Tactics_Types.psc);
                  FStar_Tactics_Types.entry_range =
                    (uu___399_8888.FStar_Tactics_Types.entry_range);
                  FStar_Tactics_Types.guard_policy =
                    (uu___399_8888.FStar_Tactics_Types.guard_policy);
                  FStar_Tactics_Types.freshness =
                    (uu___399_8888.FStar_Tactics_Types.freshness);
                  FStar_Tactics_Types.tac_verb_dbg =
                    (uu___399_8888.FStar_Tactics_Types.tac_verb_dbg)
                }))
  
let (qed : unit -> unit tac) =
  fun uu____8895  ->
    bind get
      (fun ps  ->
         match ps.FStar_Tactics_Types.goals with
         | [] -> ret ()
         | uu____8902 -> fail "Not done!")
  
let (cases :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 tac)
  =
  fun t  ->
    let uu____8922 =
      let uu____8929 = cur_goal ()  in
      bind uu____8929
        (fun g  ->
           let uu____8939 =
             let uu____8948 = FStar_Tactics_Types.goal_env g  in
             __tc uu____8948 t  in
           bind uu____8939
             (fun uu____8976  ->
                match uu____8976 with
                | (t1,typ,guard) ->
                    let uu____8992 = FStar_Syntax_Util.head_and_args typ  in
                    (match uu____8992 with
                     | (hd1,args) ->
                         let uu____9035 =
                           let uu____9048 =
                             let uu____9049 = FStar_Syntax_Util.un_uinst hd1
                                in
                             uu____9049.FStar_Syntax_Syntax.n  in
                           (uu____9048, args)  in
                         (match uu____9035 with
                          | (FStar_Syntax_Syntax.Tm_fvar
                             fv,(p,uu____9068)::(q,uu____9070)::[]) when
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
                                let uu____9108 =
                                  let uu____9109 =
                                    FStar_Tactics_Types.goal_env g  in
                                  FStar_TypeChecker_Env.push_bv uu____9109
                                    v_p
                                   in
                                FStar_Tactics_Types.goal_with_env g
                                  uu____9108
                                 in
                              let g2 =
                                let uu____9111 =
                                  let uu____9112 =
                                    FStar_Tactics_Types.goal_env g  in
                                  FStar_TypeChecker_Env.push_bv uu____9112
                                    v_q
                                   in
                                FStar_Tactics_Types.goal_with_env g
                                  uu____9111
                                 in
                              bind __dismiss
                                (fun uu____9119  ->
                                   let uu____9120 = add_goals [g1; g2]  in
                                   bind uu____9120
                                     (fun uu____9129  ->
                                        let uu____9130 =
                                          let uu____9135 =
                                            FStar_Syntax_Syntax.bv_to_name
                                              v_p
                                             in
                                          let uu____9136 =
                                            FStar_Syntax_Syntax.bv_to_name
                                              v_q
                                             in
                                          (uu____9135, uu____9136)  in
                                        ret uu____9130))
                          | uu____9141 ->
                              let uu____9154 =
                                let uu____9155 =
                                  FStar_Tactics_Types.goal_env g  in
                                tts uu____9155 typ  in
                              fail1 "Not a disjunction: %s" uu____9154))))
       in
    FStar_All.pipe_left (wrap_err "cases") uu____8922
  
let (set_options : Prims.string -> unit tac) =
  fun s  ->
    let uu____9185 =
      let uu____9188 = cur_goal ()  in
      bind uu____9188
        (fun g  ->
           FStar_Options.push ();
           (let uu____9201 = FStar_Util.smap_copy g.FStar_Tactics_Types.opts
               in
            FStar_Options.set uu____9201);
           (let res = FStar_Options.set_options FStar_Options.Set s  in
            let opts' = FStar_Options.peek ()  in
            FStar_Options.pop ();
            (match res with
             | FStar_Getopt.Success  ->
                 let g' =
                   let uu___400_9208 = g  in
                   {
                     FStar_Tactics_Types.goal_main_env =
                       (uu___400_9208.FStar_Tactics_Types.goal_main_env);
                     FStar_Tactics_Types.goal_ctx_uvar =
                       (uu___400_9208.FStar_Tactics_Types.goal_ctx_uvar);
                     FStar_Tactics_Types.opts = opts';
                     FStar_Tactics_Types.is_guard =
                       (uu___400_9208.FStar_Tactics_Types.is_guard)
                   }  in
                 replace_cur g'
             | FStar_Getopt.Error err ->
                 fail2 "Setting options `%s` failed: %s" s err
             | FStar_Getopt.Help  ->
                 fail1 "Setting options `%s` failed (got `Help`?)" s)))
       in
    FStar_All.pipe_left (wrap_err "set_options") uu____9185
  
let (top_env : unit -> env tac) =
  fun uu____9220  ->
    bind get
      (fun ps  -> FStar_All.pipe_left ret ps.FStar_Tactics_Types.main_context)
  
let (cur_env : unit -> env tac) =
  fun uu____9233  ->
    let uu____9236 = cur_goal ()  in
    bind uu____9236
      (fun g  ->
         let uu____9242 = FStar_Tactics_Types.goal_env g  in
         FStar_All.pipe_left ret uu____9242)
  
let (cur_goal' : unit -> FStar_Syntax_Syntax.term tac) =
  fun uu____9251  ->
    let uu____9254 = cur_goal ()  in
    bind uu____9254
      (fun g  ->
         let uu____9260 = FStar_Tactics_Types.goal_type g  in
         FStar_All.pipe_left ret uu____9260)
  
let (cur_witness : unit -> FStar_Syntax_Syntax.term tac) =
  fun uu____9269  ->
    let uu____9272 = cur_goal ()  in
    bind uu____9272
      (fun g  ->
         let uu____9278 = FStar_Tactics_Types.goal_witness g  in
         FStar_All.pipe_left ret uu____9278)
  
let (unquote :
  FStar_Reflection_Data.typ ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term tac)
  =
  fun ty  ->
    fun tm  ->
      let uu____9295 =
        mlog
          (fun uu____9300  ->
             let uu____9301 = FStar_Syntax_Print.term_to_string tm  in
             FStar_Util.print1 "unquote: tm = %s\n" uu____9301)
          (fun uu____9304  ->
             let uu____9305 = cur_goal ()  in
             bind uu____9305
               (fun goal  ->
                  let env =
                    let uu____9313 = FStar_Tactics_Types.goal_env goal  in
                    FStar_TypeChecker_Env.set_expected_typ uu____9313 ty  in
                  let uu____9314 = __tc env tm  in
                  bind uu____9314
                    (fun uu____9333  ->
                       match uu____9333 with
                       | (tm1,typ,guard) ->
                           mlog
                             (fun uu____9347  ->
                                let uu____9348 =
                                  FStar_Syntax_Print.term_to_string tm1  in
                                FStar_Util.print1 "unquote: tm' = %s\n"
                                  uu____9348)
                             (fun uu____9350  ->
                                mlog
                                  (fun uu____9353  ->
                                     let uu____9354 =
                                       FStar_Syntax_Print.term_to_string typ
                                        in
                                     FStar_Util.print1 "unquote: typ = %s\n"
                                       uu____9354)
                                  (fun uu____9357  ->
                                     let uu____9358 =
                                       proc_guard "unquote" env guard  in
                                     bind uu____9358
                                       (fun uu____9362  -> ret tm1))))))
         in
      FStar_All.pipe_left (wrap_err "unquote") uu____9295
  
let (uvar_env :
  env ->
    FStar_Reflection_Data.typ FStar_Pervasives_Native.option ->
      FStar_Syntax_Syntax.term tac)
  =
  fun env  ->
    fun ty  ->
      let uu____9385 =
        match ty with
        | FStar_Pervasives_Native.Some ty1 -> ret ty1
        | FStar_Pervasives_Native.None  ->
            let uu____9391 =
              let uu____9398 =
                let uu____9399 = FStar_Syntax_Util.type_u ()  in
                FStar_All.pipe_left FStar_Pervasives_Native.fst uu____9399
                 in
              new_uvar "uvar_env.2" env uu____9398  in
            bind uu____9391
              (fun uu____9415  ->
                 match uu____9415 with | (typ,uvar_typ) -> ret typ)
         in
      bind uu____9385
        (fun typ  ->
           let uu____9427 = new_uvar "uvar_env" env typ  in
           bind uu____9427
             (fun uu____9441  -> match uu____9441 with | (t,uvar_t) -> ret t))
  
let (unshelve : FStar_Syntax_Syntax.term -> unit tac) =
  fun t  ->
    let uu____9459 =
      bind get
        (fun ps  ->
           let env = ps.FStar_Tactics_Types.main_context  in
           let opts =
             match ps.FStar_Tactics_Types.goals with
             | g::uu____9478 -> g.FStar_Tactics_Types.opts
             | uu____9481 -> FStar_Options.peek ()  in
           let uu____9484 = FStar_Syntax_Util.head_and_args t  in
           match uu____9484 with
           | ({
                FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                  (ctx_uvar,uu____9502);
                FStar_Syntax_Syntax.pos = uu____9503;
                FStar_Syntax_Syntax.vars = uu____9504;_},uu____9505)
               ->
               let env1 =
                 let uu___401_9543 = env  in
                 {
                   FStar_TypeChecker_Env.solver =
                     (uu___401_9543.FStar_TypeChecker_Env.solver);
                   FStar_TypeChecker_Env.range =
                     (uu___401_9543.FStar_TypeChecker_Env.range);
                   FStar_TypeChecker_Env.curmodule =
                     (uu___401_9543.FStar_TypeChecker_Env.curmodule);
                   FStar_TypeChecker_Env.gamma =
                     (ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_gamma);
                   FStar_TypeChecker_Env.gamma_sig =
                     (uu___401_9543.FStar_TypeChecker_Env.gamma_sig);
                   FStar_TypeChecker_Env.gamma_cache =
                     (uu___401_9543.FStar_TypeChecker_Env.gamma_cache);
                   FStar_TypeChecker_Env.modules =
                     (uu___401_9543.FStar_TypeChecker_Env.modules);
                   FStar_TypeChecker_Env.expected_typ =
                     (uu___401_9543.FStar_TypeChecker_Env.expected_typ);
                   FStar_TypeChecker_Env.sigtab =
                     (uu___401_9543.FStar_TypeChecker_Env.sigtab);
                   FStar_TypeChecker_Env.is_pattern =
                     (uu___401_9543.FStar_TypeChecker_Env.is_pattern);
                   FStar_TypeChecker_Env.instantiate_imp =
                     (uu___401_9543.FStar_TypeChecker_Env.instantiate_imp);
                   FStar_TypeChecker_Env.effects =
                     (uu___401_9543.FStar_TypeChecker_Env.effects);
                   FStar_TypeChecker_Env.generalize =
                     (uu___401_9543.FStar_TypeChecker_Env.generalize);
                   FStar_TypeChecker_Env.letrecs =
                     (uu___401_9543.FStar_TypeChecker_Env.letrecs);
                   FStar_TypeChecker_Env.top_level =
                     (uu___401_9543.FStar_TypeChecker_Env.top_level);
                   FStar_TypeChecker_Env.check_uvars =
                     (uu___401_9543.FStar_TypeChecker_Env.check_uvars);
                   FStar_TypeChecker_Env.use_eq =
                     (uu___401_9543.FStar_TypeChecker_Env.use_eq);
                   FStar_TypeChecker_Env.is_iface =
                     (uu___401_9543.FStar_TypeChecker_Env.is_iface);
                   FStar_TypeChecker_Env.admit =
                     (uu___401_9543.FStar_TypeChecker_Env.admit);
                   FStar_TypeChecker_Env.lax =
                     (uu___401_9543.FStar_TypeChecker_Env.lax);
                   FStar_TypeChecker_Env.lax_universes =
                     (uu___401_9543.FStar_TypeChecker_Env.lax_universes);
                   FStar_TypeChecker_Env.failhard =
                     (uu___401_9543.FStar_TypeChecker_Env.failhard);
                   FStar_TypeChecker_Env.nosynth =
                     (uu___401_9543.FStar_TypeChecker_Env.nosynth);
                   FStar_TypeChecker_Env.uvar_subtyping =
                     (uu___401_9543.FStar_TypeChecker_Env.uvar_subtyping);
                   FStar_TypeChecker_Env.tc_term =
                     (uu___401_9543.FStar_TypeChecker_Env.tc_term);
                   FStar_TypeChecker_Env.type_of =
                     (uu___401_9543.FStar_TypeChecker_Env.type_of);
                   FStar_TypeChecker_Env.universe_of =
                     (uu___401_9543.FStar_TypeChecker_Env.universe_of);
                   FStar_TypeChecker_Env.check_type_of =
                     (uu___401_9543.FStar_TypeChecker_Env.check_type_of);
                   FStar_TypeChecker_Env.use_bv_sorts =
                     (uu___401_9543.FStar_TypeChecker_Env.use_bv_sorts);
                   FStar_TypeChecker_Env.qtbl_name_and_index =
                     (uu___401_9543.FStar_TypeChecker_Env.qtbl_name_and_index);
                   FStar_TypeChecker_Env.normalized_eff_names =
                     (uu___401_9543.FStar_TypeChecker_Env.normalized_eff_names);
                   FStar_TypeChecker_Env.proof_ns =
                     (uu___401_9543.FStar_TypeChecker_Env.proof_ns);
                   FStar_TypeChecker_Env.synth_hook =
                     (uu___401_9543.FStar_TypeChecker_Env.synth_hook);
                   FStar_TypeChecker_Env.splice =
                     (uu___401_9543.FStar_TypeChecker_Env.splice);
                   FStar_TypeChecker_Env.is_native_tactic =
                     (uu___401_9543.FStar_TypeChecker_Env.is_native_tactic);
                   FStar_TypeChecker_Env.identifier_info =
                     (uu___401_9543.FStar_TypeChecker_Env.identifier_info);
                   FStar_TypeChecker_Env.tc_hooks =
                     (uu___401_9543.FStar_TypeChecker_Env.tc_hooks);
                   FStar_TypeChecker_Env.dsenv =
                     (uu___401_9543.FStar_TypeChecker_Env.dsenv);
                   FStar_TypeChecker_Env.dep_graph =
                     (uu___401_9543.FStar_TypeChecker_Env.dep_graph)
                 }  in
               let g = FStar_Tactics_Types.mk_goal env1 ctx_uvar opts false
                  in
               let uu____9545 =
                 let uu____9548 = bnorm_goal g  in [uu____9548]  in
               add_goals uu____9545
           | uu____9549 -> fail "not a uvar")
       in
    FStar_All.pipe_left (wrap_err "unshelve") uu____9459
  
let (tac_and : Prims.bool tac -> Prims.bool tac -> Prims.bool tac) =
  fun t1  ->
    fun t2  ->
      let comp =
        bind t1
          (fun b  ->
             let uu____9596 = if b then t2 else ret false  in
             bind uu____9596 (fun b'  -> if b' then ret b' else fail ""))
         in
      let uu____9607 = trytac comp  in
      bind uu____9607
        (fun uu___341_9615  ->
           match uu___341_9615 with
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
        let uu____9641 =
          bind get
            (fun ps  ->
               let uu____9647 = __tc e t1  in
               bind uu____9647
                 (fun uu____9667  ->
                    match uu____9667 with
                    | (t11,ty1,g1) ->
                        let uu____9679 = __tc e t2  in
                        bind uu____9679
                          (fun uu____9699  ->
                             match uu____9699 with
                             | (t21,ty2,g2) ->
                                 let uu____9711 =
                                   proc_guard "unify_env g1" e g1  in
                                 bind uu____9711
                                   (fun uu____9716  ->
                                      let uu____9717 =
                                        proc_guard "unify_env g2" e g2  in
                                      bind uu____9717
                                        (fun uu____9723  ->
                                           let uu____9724 =
                                             do_unify e ty1 ty2  in
                                           let uu____9727 =
                                             do_unify e t11 t21  in
                                           tac_and uu____9724 uu____9727)))))
           in
        FStar_All.pipe_left (wrap_err "unify_env") uu____9641
  
let (launch_process :
  Prims.string -> Prims.string Prims.list -> Prims.string -> Prims.string tac)
  =
  fun prog  ->
    fun args  ->
      fun input  ->
        bind idtac
          (fun uu____9760  ->
             let uu____9761 = FStar_Options.unsafe_tactic_exec ()  in
             if uu____9761
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
        (fun uu____9782  ->
           let uu____9783 =
             FStar_Syntax_Syntax.gen_bv nm FStar_Pervasives_Native.None t  in
           ret uu____9783)
  
let (change : FStar_Reflection_Data.typ -> unit tac) =
  fun ty  ->
    let uu____9793 =
      mlog
        (fun uu____9798  ->
           let uu____9799 = FStar_Syntax_Print.term_to_string ty  in
           FStar_Util.print1 "change: ty = %s\n" uu____9799)
        (fun uu____9802  ->
           let uu____9803 = cur_goal ()  in
           bind uu____9803
             (fun g  ->
                let uu____9809 =
                  let uu____9818 = FStar_Tactics_Types.goal_env g  in
                  __tc uu____9818 ty  in
                bind uu____9809
                  (fun uu____9830  ->
                     match uu____9830 with
                     | (ty1,uu____9840,guard) ->
                         let uu____9842 =
                           let uu____9845 = FStar_Tactics_Types.goal_env g
                              in
                           proc_guard "change" uu____9845 guard  in
                         bind uu____9842
                           (fun uu____9848  ->
                              let uu____9849 =
                                let uu____9852 =
                                  FStar_Tactics_Types.goal_env g  in
                                let uu____9853 =
                                  FStar_Tactics_Types.goal_type g  in
                                do_unify uu____9852 uu____9853 ty1  in
                              bind uu____9849
                                (fun bb  ->
                                   if bb
                                   then
                                     let uu____9859 =
                                       FStar_Tactics_Types.goal_with_type g
                                         ty1
                                        in
                                     replace_cur uu____9859
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
                                        let uu____9865 =
                                          FStar_Tactics_Types.goal_env g  in
                                        let uu____9866 =
                                          FStar_Tactics_Types.goal_type g  in
                                        normalize steps uu____9865 uu____9866
                                         in
                                      let nty =
                                        let uu____9868 =
                                          FStar_Tactics_Types.goal_env g  in
                                        normalize steps uu____9868 ty1  in
                                      let uu____9869 =
                                        let uu____9872 =
                                          FStar_Tactics_Types.goal_env g  in
                                        do_unify uu____9872 ng nty  in
                                      bind uu____9869
                                        (fun b  ->
                                           if b
                                           then
                                             let uu____9878 =
                                               FStar_Tactics_Types.goal_with_type
                                                 g ty1
                                                in
                                             replace_cur uu____9878
                                           else fail "not convertible")))))))
       in
    FStar_All.pipe_left (wrap_err "change") uu____9793
  
let rec last : 'a . 'a Prims.list -> 'a =
  fun l  ->
    match l with
    | [] -> failwith "last: empty list"
    | x::[] -> x
    | uu____9900::xs -> last xs
  
let rec init : 'a . 'a Prims.list -> 'a Prims.list =
  fun l  ->
    match l with
    | [] -> failwith "init: empty list"
    | x::[] -> []
    | x::xs -> let uu____9928 = init xs  in x :: uu____9928
  
let rec (inspect :
  FStar_Syntax_Syntax.term -> FStar_Reflection_Data.term_view tac) =
  fun t  ->
    let uu____9940 =
      let t1 = FStar_Syntax_Util.unascribe t  in
      let t2 = FStar_Syntax_Util.un_uinst t1  in
      match t2.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_meta (t3,uu____9948) -> inspect t3
      | FStar_Syntax_Syntax.Tm_name bv ->
          FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_Var bv)
      | FStar_Syntax_Syntax.Tm_bvar bv ->
          FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_BVar bv)
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_FVar fv)
      | FStar_Syntax_Syntax.Tm_app (hd1,[]) ->
          failwith "empty arguments on Tm_app"
      | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
          let uu____10005 = last args  in
          (match uu____10005 with
           | (a,q) ->
               let q' = FStar_Reflection_Basic.inspect_aqual q  in
               let uu____10027 =
                 let uu____10028 =
                   let uu____10033 =
                     let uu____10034 =
                       let uu____10039 = init args  in
                       FStar_Syntax_Syntax.mk_Tm_app hd1 uu____10039  in
                     uu____10034 FStar_Pervasives_Native.None
                       t2.FStar_Syntax_Syntax.pos
                      in
                   (uu____10033, (a, q'))  in
                 FStar_Reflection_Data.Tv_App uu____10028  in
               FStar_All.pipe_left ret uu____10027)
      | FStar_Syntax_Syntax.Tm_abs ([],uu____10050,uu____10051) ->
          failwith "empty arguments on Tm_abs"
      | FStar_Syntax_Syntax.Tm_abs (bs,t3,k) ->
          let uu____10095 = FStar_Syntax_Subst.open_term bs t3  in
          (match uu____10095 with
           | (bs1,t4) ->
               (match bs1 with
                | [] -> failwith "impossible"
                | b::bs2 ->
                    let uu____10128 =
                      let uu____10129 =
                        let uu____10134 = FStar_Syntax_Util.abs bs2 t4 k  in
                        (b, uu____10134)  in
                      FStar_Reflection_Data.Tv_Abs uu____10129  in
                    FStar_All.pipe_left ret uu____10128))
      | FStar_Syntax_Syntax.Tm_type uu____10137 ->
          FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_Type ())
      | FStar_Syntax_Syntax.Tm_arrow ([],k) ->
          failwith "empty binders on arrow"
      | FStar_Syntax_Syntax.Tm_arrow uu____10157 ->
          let uu____10170 = FStar_Syntax_Util.arrow_one t2  in
          (match uu____10170 with
           | FStar_Pervasives_Native.Some (b,c) ->
               FStar_All.pipe_left ret
                 (FStar_Reflection_Data.Tv_Arrow (b, c))
           | FStar_Pervasives_Native.None  -> failwith "impossible")
      | FStar_Syntax_Syntax.Tm_refine (bv,t3) ->
          let b = FStar_Syntax_Syntax.mk_binder bv  in
          let uu____10200 = FStar_Syntax_Subst.open_term [b] t3  in
          (match uu____10200 with
           | (b',t4) ->
               let b1 =
                 match b' with
                 | b'1::[] -> b'1
                 | uu____10239 -> failwith "impossible"  in
               FStar_All.pipe_left ret
                 (FStar_Reflection_Data.Tv_Refine
                    ((FStar_Pervasives_Native.fst b1), t4)))
      | FStar_Syntax_Syntax.Tm_constant c ->
          let uu____10247 =
            let uu____10248 = FStar_Reflection_Basic.inspect_const c  in
            FStar_Reflection_Data.Tv_Const uu____10248  in
          FStar_All.pipe_left ret uu____10247
      | FStar_Syntax_Syntax.Tm_uvar (ctx_u,s) ->
          let uu____10269 =
            let uu____10270 =
              let uu____10275 =
                let uu____10276 =
                  FStar_Syntax_Unionfind.uvar_id
                    ctx_u.FStar_Syntax_Syntax.ctx_uvar_head
                   in
                FStar_BigInt.of_int_fs uu____10276  in
              (uu____10275, (ctx_u, s))  in
            FStar_Reflection_Data.Tv_Uvar uu____10270  in
          FStar_All.pipe_left ret uu____10269
      | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),t21) ->
          if lb.FStar_Syntax_Syntax.lbunivs <> []
          then FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown
          else
            (match lb.FStar_Syntax_Syntax.lbname with
             | FStar_Util.Inr uu____10310 ->
                 FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown
             | FStar_Util.Inl bv ->
                 let b = FStar_Syntax_Syntax.mk_binder bv  in
                 let uu____10315 = FStar_Syntax_Subst.open_term [b] t21  in
                 (match uu____10315 with
                  | (bs,t22) ->
                      let b1 =
                        match bs with
                        | b1::[] -> b1
                        | uu____10354 ->
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
             | FStar_Util.Inr uu____10384 ->
                 FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown
             | FStar_Util.Inl bv ->
                 let uu____10388 = FStar_Syntax_Subst.open_let_rec [lb] t21
                    in
                 (match uu____10388 with
                  | (lbs,t22) ->
                      (match lbs with
                       | lb1::[] ->
                           (match lb1.FStar_Syntax_Syntax.lbname with
                            | FStar_Util.Inr uu____10408 ->
                                ret FStar_Reflection_Data.Tv_Unknown
                            | FStar_Util.Inl bv1 ->
                                FStar_All.pipe_left ret
                                  (FStar_Reflection_Data.Tv_Let
                                     (true, bv1,
                                       (lb1.FStar_Syntax_Syntax.lbdef), t22)))
                       | uu____10412 ->
                           failwith
                             "impossible: open_term returned different amount of binders")))
      | FStar_Syntax_Syntax.Tm_match (t3,brs) ->
          let rec inspect_pat p =
            match p.FStar_Syntax_Syntax.v with
            | FStar_Syntax_Syntax.Pat_constant c ->
                let uu____10466 = FStar_Reflection_Basic.inspect_const c  in
                FStar_Reflection_Data.Pat_Constant uu____10466
            | FStar_Syntax_Syntax.Pat_cons (fv,ps) ->
                let uu____10485 =
                  let uu____10492 =
                    FStar_List.map
                      (fun uu____10504  ->
                         match uu____10504 with
                         | (p1,uu____10512) -> inspect_pat p1) ps
                     in
                  (fv, uu____10492)  in
                FStar_Reflection_Data.Pat_Cons uu____10485
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
              (fun uu___342_10606  ->
                 match uu___342_10606 with
                 | (pat,uu____10628,t4) ->
                     let uu____10646 = inspect_pat pat  in (uu____10646, t4))
              brs1
             in
          FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_Match (t3, brs2))
      | FStar_Syntax_Syntax.Tm_unknown  ->
          FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown
      | uu____10655 ->
          ((let uu____10657 =
              let uu____10662 =
                let uu____10663 = FStar_Syntax_Print.tag_of_term t2  in
                let uu____10664 = FStar_Syntax_Print.term_to_string t2  in
                FStar_Util.format2
                  "inspect: outside of expected syntax (%s, %s)\n"
                  uu____10663 uu____10664
                 in
              (FStar_Errors.Warning_CantInspect, uu____10662)  in
            FStar_Errors.log_issue t2.FStar_Syntax_Syntax.pos uu____10657);
           FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown)
       in
    wrap_err "inspect" uu____9940
  
let (pack : FStar_Reflection_Data.term_view -> FStar_Syntax_Syntax.term tac)
  =
  fun tv  ->
    match tv with
    | FStar_Reflection_Data.Tv_Var bv ->
        let uu____10677 = FStar_Syntax_Syntax.bv_to_name bv  in
        FStar_All.pipe_left ret uu____10677
    | FStar_Reflection_Data.Tv_BVar bv ->
        let uu____10681 = FStar_Syntax_Syntax.bv_to_tm bv  in
        FStar_All.pipe_left ret uu____10681
    | FStar_Reflection_Data.Tv_FVar fv ->
        let uu____10685 = FStar_Syntax_Syntax.fv_to_tm fv  in
        FStar_All.pipe_left ret uu____10685
    | FStar_Reflection_Data.Tv_App (l,(r,q)) ->
        let q' = FStar_Reflection_Basic.pack_aqual q  in
        let uu____10692 = FStar_Syntax_Util.mk_app l [(r, q')]  in
        FStar_All.pipe_left ret uu____10692
    | FStar_Reflection_Data.Tv_Abs (b,t) ->
        let uu____10711 =
          FStar_Syntax_Util.abs [b] t FStar_Pervasives_Native.None  in
        FStar_All.pipe_left ret uu____10711
    | FStar_Reflection_Data.Tv_Arrow (b,c) ->
        let uu____10724 = FStar_Syntax_Util.arrow [b] c  in
        FStar_All.pipe_left ret uu____10724
    | FStar_Reflection_Data.Tv_Type () ->
        FStar_All.pipe_left ret FStar_Syntax_Util.ktype
    | FStar_Reflection_Data.Tv_Refine (bv,t) ->
        let uu____10739 = FStar_Syntax_Util.refine bv t  in
        FStar_All.pipe_left ret uu____10739
    | FStar_Reflection_Data.Tv_Const c ->
        let uu____10743 =
          let uu____10744 =
            let uu____10751 =
              let uu____10752 = FStar_Reflection_Basic.pack_const c  in
              FStar_Syntax_Syntax.Tm_constant uu____10752  in
            FStar_Syntax_Syntax.mk uu____10751  in
          uu____10744 FStar_Pervasives_Native.None FStar_Range.dummyRange  in
        FStar_All.pipe_left ret uu____10743
    | FStar_Reflection_Data.Tv_Uvar (_u,ctx_u_s) ->
        let uu____10760 =
          FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_uvar ctx_u_s)
            FStar_Pervasives_Native.None FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____10760
    | FStar_Reflection_Data.Tv_Let (false ,bv,t1,t2) ->
        let lb =
          FStar_Syntax_Util.mk_letbinding (FStar_Util.Inl bv) []
            bv.FStar_Syntax_Syntax.sort FStar_Parser_Const.effect_Tot_lid t1
            [] FStar_Range.dummyRange
           in
        let uu____10769 =
          let uu____10770 =
            let uu____10777 =
              let uu____10778 =
                let uu____10791 =
                  let uu____10794 =
                    let uu____10795 = FStar_Syntax_Syntax.mk_binder bv  in
                    [uu____10795]  in
                  FStar_Syntax_Subst.close uu____10794 t2  in
                ((false, [lb]), uu____10791)  in
              FStar_Syntax_Syntax.Tm_let uu____10778  in
            FStar_Syntax_Syntax.mk uu____10777  in
          uu____10770 FStar_Pervasives_Native.None FStar_Range.dummyRange  in
        FStar_All.pipe_left ret uu____10769
    | FStar_Reflection_Data.Tv_Let (true ,bv,t1,t2) ->
        let lb =
          FStar_Syntax_Util.mk_letbinding (FStar_Util.Inl bv) []
            bv.FStar_Syntax_Syntax.sort FStar_Parser_Const.effect_Tot_lid t1
            [] FStar_Range.dummyRange
           in
        let uu____10829 = FStar_Syntax_Subst.close_let_rec [lb] t2  in
        (match uu____10829 with
         | (lbs,body) ->
             let uu____10844 =
               FStar_Syntax_Syntax.mk
                 (FStar_Syntax_Syntax.Tm_let ((true, lbs), body))
                 FStar_Pervasives_Native.None FStar_Range.dummyRange
                in
             FStar_All.pipe_left ret uu____10844)
    | FStar_Reflection_Data.Tv_Match (t,brs) ->
        let wrap v1 =
          {
            FStar_Syntax_Syntax.v = v1;
            FStar_Syntax_Syntax.p = FStar_Range.dummyRange
          }  in
        let rec pack_pat p =
          match p with
          | FStar_Reflection_Data.Pat_Constant c ->
              let uu____10878 =
                let uu____10879 = FStar_Reflection_Basic.pack_const c  in
                FStar_Syntax_Syntax.Pat_constant uu____10879  in
              FStar_All.pipe_left wrap uu____10878
          | FStar_Reflection_Data.Pat_Cons (fv,ps) ->
              let uu____10886 =
                let uu____10887 =
                  let uu____10900 =
                    FStar_List.map
                      (fun p1  ->
                         let uu____10916 = pack_pat p1  in
                         (uu____10916, false)) ps
                     in
                  (fv, uu____10900)  in
                FStar_Syntax_Syntax.Pat_cons uu____10887  in
              FStar_All.pipe_left wrap uu____10886
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
            (fun uu___343_10962  ->
               match uu___343_10962 with
               | (pat,t1) ->
                   let uu____10979 = pack_pat pat  in
                   (uu____10979, FStar_Pervasives_Native.None, t1)) brs
           in
        let brs2 = FStar_List.map FStar_Syntax_Subst.close_branch brs1  in
        let uu____11027 =
          FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_match (t, brs2))
            FStar_Pervasives_Native.None FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____11027
    | FStar_Reflection_Data.Tv_AscribedT (e,t,tacopt) ->
        let uu____11055 =
          FStar_Syntax_Syntax.mk
            (FStar_Syntax_Syntax.Tm_ascribed
               (e, ((FStar_Util.Inl t), tacopt),
                 FStar_Pervasives_Native.None)) FStar_Pervasives_Native.None
            FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____11055
    | FStar_Reflection_Data.Tv_AscribedC (e,c,tacopt) ->
        let uu____11101 =
          FStar_Syntax_Syntax.mk
            (FStar_Syntax_Syntax.Tm_ascribed
               (e, ((FStar_Util.Inr c), tacopt),
                 FStar_Pervasives_Native.None)) FStar_Pervasives_Native.None
            FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____11101
    | FStar_Reflection_Data.Tv_Unknown  ->
        let uu____11140 =
          FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown
            FStar_Pervasives_Native.None FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____11140
  
let (goal_of_goal_ty :
  env ->
    FStar_Reflection_Data.typ ->
      (FStar_Tactics_Types.goal,FStar_TypeChecker_Env.guard_t)
        FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun typ  ->
      let uu____11161 =
        FStar_TypeChecker_Util.new_implicit_var "proofstate_of_goal_ty"
          typ.FStar_Syntax_Syntax.pos env typ
         in
      match uu____11161 with
      | (u,ctx_uvars,g_u) ->
          let uu____11193 = FStar_List.hd ctx_uvars  in
          (match uu____11193 with
           | (ctx_uvar,uu____11207) ->
               let g =
                 let uu____11209 = FStar_Options.peek ()  in
                 FStar_Tactics_Types.mk_goal env ctx_uvar uu____11209 false
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
        let uu____11229 = goal_of_goal_ty env typ  in
        match uu____11229 with
        | (g,g_u) ->
            let ps =
              let uu____11241 =
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
                FStar_Tactics_Types.tac_verb_dbg = uu____11241
              }  in
            let uu____11246 = FStar_Tactics_Types.goal_witness g  in
            (ps, uu____11246)
  