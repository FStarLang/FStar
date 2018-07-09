open Prims
type goal = FStar_Tactics_Types.goal
type name = FStar_Syntax_Syntax.bv
type env = FStar_TypeChecker_Env.env
type implicits = FStar_TypeChecker_Env.implicits
let (normalize :
  FStar_TypeChecker_Env.steps ->
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
    let uu____39 =
      let uu____40 = FStar_Tactics_Types.goal_env g  in
      let uu____41 = FStar_Tactics_Types.goal_type g  in
      bnorm uu____40 uu____41  in
    FStar_Tactics_Types.goal_with_type g uu____39
  
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
      let uu____151 = FStar_Options.tactics_failhard ()  in
      if uu____151
      then run t p
      else
        (try (fun uu___355_158  -> match () with | () -> run t p) ()
         with
         | FStar_Errors.Err (uu____167,msg) ->
             FStar_Tactics_Result.Failed (msg, p)
         | FStar_Errors.Error (uu____169,msg,uu____171) ->
             FStar_Tactics_Result.Failed (msg, p)
         | e ->
             let uu____173 =
               let uu____178 = FStar_Util.message_of_exn e  in (uu____178, p)
                in
             FStar_Tactics_Result.Failed uu____173)
  
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
           let uu____250 = run t1 p  in
           match uu____250 with
           | FStar_Tactics_Result.Success (a,q) ->
               let uu____257 = t2 a  in run uu____257 q
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
    let uu____277 =
      FStar_Syntax_Unionfind.find uv.FStar_Syntax_Syntax.ctx_uvar_head  in
    match uu____277 with
    | FStar_Pervasives_Native.Some t -> FStar_Pervasives_Native.Some t
    | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
  
let (check_goal_solved :
  FStar_Tactics_Types.goal ->
    FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  = fun goal  -> get_uvar_solved goal.FStar_Tactics_Types.goal_ctx_uvar 
let (goal_to_string_verbose : FStar_Tactics_Types.goal -> Prims.string) =
  fun g  ->
    let uu____295 =
      FStar_Syntax_Print.ctx_uvar_to_string
        g.FStar_Tactics_Types.goal_ctx_uvar
       in
    let uu____296 =
      let uu____297 = check_goal_solved g  in
      match uu____297 with
      | FStar_Pervasives_Native.None  -> ""
      | FStar_Pervasives_Native.Some t ->
          let uu____301 = FStar_Syntax_Print.term_to_string t  in
          FStar_Util.format1 "\tGOAL ALREADY SOLVED!: %s" uu____301
       in
    FStar_Util.format2 "%s%s" uu____295 uu____296
  
let (goal_to_string :
  FStar_Tactics_Types.proofstate -> FStar_Tactics_Types.goal -> Prims.string)
  =
  fun ps  ->
    fun g  ->
      let uu____312 =
        (FStar_Options.print_implicits ()) ||
          ps.FStar_Tactics_Types.tac_verb_dbg
         in
      if uu____312
      then goal_to_string_verbose g
      else
        (let w =
           let uu____315 =
             get_uvar_solved g.FStar_Tactics_Types.goal_ctx_uvar  in
           match uu____315 with
           | FStar_Pervasives_Native.None  -> "_"
           | FStar_Pervasives_Native.Some t ->
               let uu____319 = FStar_Tactics_Types.goal_env g  in
               tts uu____319 t
            in
         let uu____320 =
           FStar_Syntax_Print.binders_to_string ", "
             (g.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_binders
            in
         let uu____321 =
           let uu____322 = FStar_Tactics_Types.goal_env g  in
           tts uu____322
             (g.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_typ
            in
         FStar_Util.format3 "%s |- %s : %s" uu____320 w uu____321)
  
let (tacprint : Prims.string -> unit) =
  fun s  -> FStar_Util.print1 "TAC>> %s\n" s 
let (tacprint1 : Prims.string -> Prims.string -> unit) =
  fun s  ->
    fun x  ->
      let uu____338 = FStar_Util.format1 s x  in
      FStar_Util.print1 "TAC>> %s\n" uu____338
  
let (tacprint2 : Prims.string -> Prims.string -> Prims.string -> unit) =
  fun s  ->
    fun x  ->
      fun y  ->
        let uu____354 = FStar_Util.format2 s x y  in
        FStar_Util.print1 "TAC>> %s\n" uu____354
  
let (tacprint3 :
  Prims.string -> Prims.string -> Prims.string -> Prims.string -> unit) =
  fun s  ->
    fun x  ->
      fun y  ->
        fun z  ->
          let uu____375 = FStar_Util.format3 s x y z  in
          FStar_Util.print1 "TAC>> %s\n" uu____375
  
let (comp_to_typ : FStar_Syntax_Syntax.comp -> FStar_Reflection_Data.typ) =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Total (t,uu____382) -> t
    | FStar_Syntax_Syntax.GTotal (t,uu____392) -> t
    | FStar_Syntax_Syntax.Comp ct -> ct.FStar_Syntax_Syntax.result_typ
  
let (get_phi :
  FStar_Tactics_Types.goal ->
    FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun g  ->
    let uu____411 =
      let uu____412 = FStar_Tactics_Types.goal_env g  in
      let uu____413 = FStar_Tactics_Types.goal_type g  in
      FStar_TypeChecker_Normalize.unfold_whnf uu____412 uu____413  in
    FStar_Syntax_Util.un_squash uu____411
  
let (is_irrelevant : FStar_Tactics_Types.goal -> Prims.bool) =
  fun g  -> let uu____419 = get_phi g  in FStar_Option.isSome uu____419 
let (print : Prims.string -> unit tac) = fun msg  -> tacprint msg; ret () 
let (debug : Prims.string -> unit tac) =
  fun msg  ->
    bind get
      (fun ps  ->
         (let uu____445 =
            let uu____446 =
              FStar_Ident.string_of_lid
                (ps.FStar_Tactics_Types.main_context).FStar_TypeChecker_Env.curmodule
               in
            FStar_Options.debug_module uu____446  in
          if uu____445 then tacprint msg else ());
         ret ())
  
let (dump_goal :
  FStar_Tactics_Types.proofstate -> FStar_Tactics_Types.goal -> unit) =
  fun ps  ->
    fun goal  ->
      let uu____459 = goal_to_string ps goal  in tacprint uu____459
  
let (dump_cur : FStar_Tactics_Types.proofstate -> Prims.string -> unit) =
  fun ps  ->
    fun msg  ->
      match ps.FStar_Tactics_Types.goals with
      | [] -> tacprint1 "No more goals (%s)" msg
      | h::uu____471 ->
          (tacprint1 "Current goal (%s):" msg;
           (let uu____475 = FStar_List.hd ps.FStar_Tactics_Types.goals  in
            dump_goal ps uu____475))
  
let (ps_to_string :
  (Prims.string,FStar_Tactics_Types.proofstate)
    FStar_Pervasives_Native.tuple2 -> Prims.string)
  =
  fun uu____484  ->
    match uu____484 with
    | (msg,ps) ->
        let p_imp imp =
          FStar_Syntax_Print.uvar_to_string
            (imp.FStar_TypeChecker_Env.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_head
           in
        let uu____497 =
          let uu____500 =
            let uu____501 =
              FStar_Util.string_of_int ps.FStar_Tactics_Types.depth  in
            FStar_Util.format2 "State dump @ depth %s (%s):\n" uu____501 msg
             in
          let uu____502 =
            let uu____505 =
              if ps.FStar_Tactics_Types.entry_range <> FStar_Range.dummyRange
              then
                let uu____506 =
                  FStar_Range.string_of_def_range
                    ps.FStar_Tactics_Types.entry_range
                   in
                FStar_Util.format1 "Location: %s\n" uu____506
              else ""  in
            let uu____508 =
              let uu____511 =
                let uu____512 =
                  FStar_TypeChecker_Env.debug
                    ps.FStar_Tactics_Types.main_context
                    (FStar_Options.Other "Imp")
                   in
                if uu____512
                then
                  let uu____513 =
                    FStar_Common.string_of_list p_imp
                      ps.FStar_Tactics_Types.all_implicits
                     in
                  FStar_Util.format1 "Imps: %s\n" uu____513
                else ""  in
              let uu____515 =
                let uu____518 =
                  let uu____519 =
                    FStar_Util.string_of_int
                      (FStar_List.length ps.FStar_Tactics_Types.goals)
                     in
                  let uu____520 =
                    let uu____521 =
                      FStar_List.map (goal_to_string ps)
                        ps.FStar_Tactics_Types.goals
                       in
                    FStar_String.concat "\n" uu____521  in
                  FStar_Util.format2 "ACTIVE goals (%s):\n%s\n" uu____519
                    uu____520
                   in
                let uu____524 =
                  let uu____527 =
                    let uu____528 =
                      FStar_Util.string_of_int
                        (FStar_List.length ps.FStar_Tactics_Types.smt_goals)
                       in
                    let uu____529 =
                      let uu____530 =
                        FStar_List.map (goal_to_string ps)
                          ps.FStar_Tactics_Types.smt_goals
                         in
                      FStar_String.concat "\n" uu____530  in
                    FStar_Util.format2 "SMT goals (%s):\n%s\n" uu____528
                      uu____529
                     in
                  [uu____527]  in
                uu____518 :: uu____524  in
              uu____511 :: uu____515  in
            uu____505 :: uu____508  in
          uu____500 :: uu____502  in
        FStar_String.concat "" uu____497
  
let (goal_to_json : FStar_Tactics_Types.goal -> FStar_Util.json) =
  fun g  ->
    let g_binders =
      let uu____539 =
        let uu____540 = FStar_Tactics_Types.goal_env g  in
        FStar_TypeChecker_Env.all_binders uu____540  in
      let uu____541 =
        let uu____546 =
          let uu____547 = FStar_Tactics_Types.goal_env g  in
          FStar_TypeChecker_Env.dsenv uu____547  in
        FStar_Syntax_Print.binders_to_json uu____546  in
      FStar_All.pipe_right uu____539 uu____541  in
    let uu____548 =
      let uu____555 =
        let uu____562 =
          let uu____567 =
            let uu____568 =
              let uu____575 =
                let uu____580 =
                  let uu____581 =
                    let uu____582 = FStar_Tactics_Types.goal_env g  in
                    let uu____583 = FStar_Tactics_Types.goal_witness g  in
                    tts uu____582 uu____583  in
                  FStar_Util.JsonStr uu____581  in
                ("witness", uu____580)  in
              let uu____584 =
                let uu____591 =
                  let uu____596 =
                    let uu____597 =
                      let uu____598 = FStar_Tactics_Types.goal_env g  in
                      let uu____599 = FStar_Tactics_Types.goal_type g  in
                      tts uu____598 uu____599  in
                    FStar_Util.JsonStr uu____597  in
                  ("type", uu____596)  in
                [uu____591]  in
              uu____575 :: uu____584  in
            FStar_Util.JsonAssoc uu____568  in
          ("goal", uu____567)  in
        [uu____562]  in
      ("hyps", g_binders) :: uu____555  in
    FStar_Util.JsonAssoc uu____548
  
let (ps_to_json :
  (Prims.string,FStar_Tactics_Types.proofstate)
    FStar_Pervasives_Native.tuple2 -> FStar_Util.json)
  =
  fun uu____632  ->
    match uu____632 with
    | (msg,ps) ->
        let uu____639 =
          let uu____646 =
            let uu____653 =
              let uu____660 =
                let uu____667 =
                  let uu____672 =
                    let uu____673 =
                      FStar_List.map goal_to_json
                        ps.FStar_Tactics_Types.goals
                       in
                    FStar_Util.JsonList uu____673  in
                  ("goals", uu____672)  in
                let uu____676 =
                  let uu____683 =
                    let uu____688 =
                      let uu____689 =
                        FStar_List.map goal_to_json
                          ps.FStar_Tactics_Types.smt_goals
                         in
                      FStar_Util.JsonList uu____689  in
                    ("smt-goals", uu____688)  in
                  [uu____683]  in
                uu____667 :: uu____676  in
              ("depth", (FStar_Util.JsonInt (ps.FStar_Tactics_Types.depth)))
                :: uu____660
               in
            ("label", (FStar_Util.JsonStr msg)) :: uu____653  in
          let uu____712 =
            if ps.FStar_Tactics_Types.entry_range <> FStar_Range.dummyRange
            then
              let uu____725 =
                let uu____730 =
                  FStar_Range.json_of_def_range
                    ps.FStar_Tactics_Types.entry_range
                   in
                ("location", uu____730)  in
              [uu____725]
            else []  in
          FStar_List.append uu____646 uu____712  in
        FStar_Util.JsonAssoc uu____639
  
let (dump_proofstate :
  FStar_Tactics_Types.proofstate -> Prims.string -> unit) =
  fun ps  ->
    fun msg  ->
      FStar_Options.with_saved_options
        (fun uu____760  ->
           FStar_Options.set_option "print_effect_args"
             (FStar_Options.Bool true);
           FStar_Util.print_generic "proof-state" ps_to_string ps_to_json
             (msg, ps))
  
let (print_proof_state1 : Prims.string -> unit tac) =
  fun msg  ->
    mk_tac
      (fun ps  ->
         let psc = ps.FStar_Tactics_Types.psc  in
         let subst1 = FStar_TypeChecker_Cfg.psc_subst psc  in
         (let uu____783 = FStar_Tactics_Types.subst_proof_state subst1 ps  in
          dump_cur uu____783 msg);
         FStar_Tactics_Result.Success ((), ps))
  
let (print_proof_state : Prims.string -> unit tac) =
  fun msg  ->
    mk_tac
      (fun ps  ->
         let psc = ps.FStar_Tactics_Types.psc  in
         let subst1 = FStar_TypeChecker_Cfg.psc_subst psc  in
         (let uu____801 = FStar_Tactics_Types.subst_proof_state subst1 ps  in
          dump_proofstate uu____801 msg);
         FStar_Tactics_Result.Success ((), ps))
  
let mlog : 'a . (unit -> unit) -> (unit -> 'a tac) -> 'a tac =
  fun f  -> fun cont  -> bind get (fun ps  -> log ps f; cont ()) 
let fail : 'a . Prims.string -> 'a tac =
  fun msg  ->
    mk_tac
      (fun ps  ->
         (let uu____855 =
            FStar_TypeChecker_Env.debug ps.FStar_Tactics_Types.main_context
              (FStar_Options.Other "TacFail")
             in
          if uu____855
          then dump_proofstate ps (Prims.strcat "TACTIC FAILING: " msg)
          else ());
         FStar_Tactics_Result.Failed (msg, ps))
  
let fail1 : 'Auu____863 . Prims.string -> Prims.string -> 'Auu____863 tac =
  fun msg  ->
    fun x  -> let uu____876 = FStar_Util.format1 msg x  in fail uu____876
  
let fail2 :
  'Auu____885 .
    Prims.string -> Prims.string -> Prims.string -> 'Auu____885 tac
  =
  fun msg  ->
    fun x  ->
      fun y  -> let uu____903 = FStar_Util.format2 msg x y  in fail uu____903
  
let fail3 :
  'Auu____914 .
    Prims.string ->
      Prims.string -> Prims.string -> Prims.string -> 'Auu____914 tac
  =
  fun msg  ->
    fun x  ->
      fun y  ->
        fun z  ->
          let uu____937 = FStar_Util.format3 msg x y z  in fail uu____937
  
let fail4 :
  'Auu____950 .
    Prims.string ->
      Prims.string ->
        Prims.string -> Prims.string -> Prims.string -> 'Auu____950 tac
  =
  fun msg  ->
    fun x  ->
      fun y  ->
        fun z  ->
          fun w  ->
            let uu____978 = FStar_Util.format4 msg x y z w  in fail uu____978
  
let catch : 'a . 'a tac -> (Prims.string,'a) FStar_Util.either tac =
  fun t  ->
    mk_tac
      (fun ps  ->
         let tx = FStar_Syntax_Unionfind.new_transaction ()  in
         let uu____1011 = run t ps  in
         match uu____1011 with
         | FStar_Tactics_Result.Success (a,q) ->
             (FStar_Syntax_Unionfind.commit tx;
              FStar_Tactics_Result.Success ((FStar_Util.Inr a), q))
         | FStar_Tactics_Result.Failed (m,q) ->
             (FStar_Syntax_Unionfind.rollback tx;
              (let ps1 =
                 let uu___356_1035 = ps  in
                 {
                   FStar_Tactics_Types.main_context =
                     (uu___356_1035.FStar_Tactics_Types.main_context);
                   FStar_Tactics_Types.main_goal =
                     (uu___356_1035.FStar_Tactics_Types.main_goal);
                   FStar_Tactics_Types.all_implicits =
                     (uu___356_1035.FStar_Tactics_Types.all_implicits);
                   FStar_Tactics_Types.goals =
                     (uu___356_1035.FStar_Tactics_Types.goals);
                   FStar_Tactics_Types.smt_goals =
                     (uu___356_1035.FStar_Tactics_Types.smt_goals);
                   FStar_Tactics_Types.depth =
                     (uu___356_1035.FStar_Tactics_Types.depth);
                   FStar_Tactics_Types.__dump =
                     (uu___356_1035.FStar_Tactics_Types.__dump);
                   FStar_Tactics_Types.psc =
                     (uu___356_1035.FStar_Tactics_Types.psc);
                   FStar_Tactics_Types.entry_range =
                     (uu___356_1035.FStar_Tactics_Types.entry_range);
                   FStar_Tactics_Types.guard_policy =
                     (uu___356_1035.FStar_Tactics_Types.guard_policy);
                   FStar_Tactics_Types.freshness =
                     (q.FStar_Tactics_Types.freshness);
                   FStar_Tactics_Types.tac_verb_dbg =
                     (uu___356_1035.FStar_Tactics_Types.tac_verb_dbg);
                   FStar_Tactics_Types.local_state =
                     (uu___356_1035.FStar_Tactics_Types.local_state)
                 }  in
               FStar_Tactics_Result.Success ((FStar_Util.Inl m), ps1))))
  
let trytac : 'a . 'a tac -> 'a FStar_Pervasives_Native.option tac =
  fun t  ->
    let uu____1062 = catch t  in
    bind uu____1062
      (fun r  ->
         match r with
         | FStar_Util.Inr v1 -> ret (FStar_Pervasives_Native.Some v1)
         | FStar_Util.Inl uu____1089 -> ret FStar_Pervasives_Native.None)
  
let trytac_exn : 'a . 'a tac -> 'a FStar_Pervasives_Native.option tac =
  fun t  ->
    mk_tac
      (fun ps  ->
         try
           (fun uu___358_1120  ->
              match () with
              | () -> let uu____1125 = trytac t  in run uu____1125 ps) ()
         with
         | FStar_Errors.Err (uu____1141,msg) ->
             (log ps
                (fun uu____1145  ->
                   FStar_Util.print1 "trytac_exn error: (%s)" msg);
              FStar_Tactics_Result.Success (FStar_Pervasives_Native.None, ps))
         | FStar_Errors.Error (uu____1150,msg,uu____1152) ->
             (log ps
                (fun uu____1155  ->
                   FStar_Util.print1 "trytac_exn error: (%s)" msg);
              FStar_Tactics_Result.Success (FStar_Pervasives_Native.None, ps)))
  
let wrap_err : 'a . Prims.string -> 'a tac -> 'a tac =
  fun pref  ->
    fun t  ->
      mk_tac
        (fun ps  ->
           let uu____1188 = run t ps  in
           match uu____1188 with
           | FStar_Tactics_Result.Success (a,q) ->
               FStar_Tactics_Result.Success (a, q)
           | FStar_Tactics_Result.Failed (msg,q) ->
               FStar_Tactics_Result.Failed
                 ((Prims.strcat pref (Prims.strcat ": " msg)), q))
  
let (set : FStar_Tactics_Types.proofstate -> unit tac) =
  fun p  -> mk_tac (fun uu____1207  -> FStar_Tactics_Result.Success ((), p)) 
let (add_implicits : implicits -> unit tac) =
  fun i  ->
    bind get
      (fun p  ->
         set
           (let uu___359_1221 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___359_1221.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___359_1221.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (FStar_List.append i p.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___359_1221.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (uu___359_1221.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___359_1221.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___359_1221.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___359_1221.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___359_1221.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___359_1221.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___359_1221.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___359_1221.FStar_Tactics_Types.tac_verb_dbg);
              FStar_Tactics_Types.local_state =
                (uu___359_1221.FStar_Tactics_Types.local_state)
            }))
  
let (__do_unify :
  env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.bool tac)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        (let uu____1242 =
           FStar_TypeChecker_Env.debug env (FStar_Options.Other "1346")  in
         if uu____1242
         then
           let uu____1243 = FStar_Syntax_Print.term_to_string t1  in
           let uu____1244 = FStar_Syntax_Print.term_to_string t2  in
           FStar_Util.print2 "%%%%%%%%do_unify %s =? %s\n" uu____1243
             uu____1244
         else ());
        (try
           (fun uu___361_1251  ->
              match () with
              | () ->
                  let res = FStar_TypeChecker_Rel.teq_nosmt env t1 t2  in
                  ((let uu____1258 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "1346")
                       in
                    if uu____1258
                    then
                      let uu____1259 =
                        FStar_Common.string_of_option
                          (FStar_TypeChecker_Rel.guard_to_string env) res
                         in
                      let uu____1260 = FStar_Syntax_Print.term_to_string t1
                         in
                      let uu____1261 = FStar_Syntax_Print.term_to_string t2
                         in
                      FStar_Util.print3
                        "%%%%%%%%do_unify (RESULT %s) %s =? %s\n" uu____1259
                        uu____1260 uu____1261
                    else ());
                   (match res with
                    | FStar_Pervasives_Native.None  -> ret false
                    | FStar_Pervasives_Native.Some g ->
                        let uu____1266 =
                          add_implicits g.FStar_TypeChecker_Env.implicits  in
                        bind uu____1266 (fun uu____1270  -> ret true)))) ()
         with
         | FStar_Errors.Err (uu____1277,msg) ->
             mlog
               (fun uu____1280  ->
                  FStar_Util.print1 ">> do_unify error, (%s)\n" msg)
               (fun uu____1282  -> ret false)
         | FStar_Errors.Error (uu____1283,msg,r) ->
             mlog
               (fun uu____1288  ->
                  let uu____1289 = FStar_Range.string_of_range r  in
                  FStar_Util.print2 ">> do_unify error, (%s) at (%s)\n" msg
                    uu____1289) (fun uu____1291  -> ret false))
  
let (compress_implicits : unit tac) =
  bind get
    (fun ps  ->
       let imps = ps.FStar_Tactics_Types.all_implicits  in
       let g =
         let uu___362_1302 = FStar_TypeChecker_Env.trivial_guard  in
         {
           FStar_TypeChecker_Env.guard_f =
             (uu___362_1302.FStar_TypeChecker_Env.guard_f);
           FStar_TypeChecker_Env.deferred =
             (uu___362_1302.FStar_TypeChecker_Env.deferred);
           FStar_TypeChecker_Env.univ_ineqs =
             (uu___362_1302.FStar_TypeChecker_Env.univ_ineqs);
           FStar_TypeChecker_Env.implicits = imps
         }  in
       let g1 =
         FStar_TypeChecker_Rel.resolve_implicits_tac
           ps.FStar_Tactics_Types.main_context g
          in
       let ps' =
         let uu___363_1305 = ps  in
         {
           FStar_Tactics_Types.main_context =
             (uu___363_1305.FStar_Tactics_Types.main_context);
           FStar_Tactics_Types.main_goal =
             (uu___363_1305.FStar_Tactics_Types.main_goal);
           FStar_Tactics_Types.all_implicits =
             (g1.FStar_TypeChecker_Env.implicits);
           FStar_Tactics_Types.goals =
             (uu___363_1305.FStar_Tactics_Types.goals);
           FStar_Tactics_Types.smt_goals =
             (uu___363_1305.FStar_Tactics_Types.smt_goals);
           FStar_Tactics_Types.depth =
             (uu___363_1305.FStar_Tactics_Types.depth);
           FStar_Tactics_Types.__dump =
             (uu___363_1305.FStar_Tactics_Types.__dump);
           FStar_Tactics_Types.psc = (uu___363_1305.FStar_Tactics_Types.psc);
           FStar_Tactics_Types.entry_range =
             (uu___363_1305.FStar_Tactics_Types.entry_range);
           FStar_Tactics_Types.guard_policy =
             (uu___363_1305.FStar_Tactics_Types.guard_policy);
           FStar_Tactics_Types.freshness =
             (uu___363_1305.FStar_Tactics_Types.freshness);
           FStar_Tactics_Types.tac_verb_dbg =
             (uu___363_1305.FStar_Tactics_Types.tac_verb_dbg);
           FStar_Tactics_Types.local_state =
             (uu___363_1305.FStar_Tactics_Types.local_state)
         }  in
       set ps')
  
let (do_unify :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.bool tac)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        bind idtac
          (fun uu____1328  ->
             (let uu____1330 =
                FStar_TypeChecker_Env.debug env (FStar_Options.Other "1346")
                 in
              if uu____1330
              then
                (FStar_Options.push ();
                 (let uu____1332 =
                    FStar_Options.set_options FStar_Options.Set
                      "--debug_level Rel --debug_level RelCheck"
                     in
                  ()))
              else ());
             (let uu____1334 = __do_unify env t1 t2  in
              bind uu____1334
                (fun r  ->
                   (let uu____1341 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "1346")
                       in
                    if uu____1341 then FStar_Options.pop () else ());
                   bind compress_implicits (fun uu____1344  -> ret r))))
  
let (remove_solved_goals : unit tac) =
  bind get
    (fun ps  ->
       let ps' =
         let uu___364_1351 = ps  in
         let uu____1352 =
           FStar_List.filter
             (fun g  ->
                let uu____1358 = check_goal_solved g  in
                FStar_Option.isNone uu____1358) ps.FStar_Tactics_Types.goals
            in
         {
           FStar_Tactics_Types.main_context =
             (uu___364_1351.FStar_Tactics_Types.main_context);
           FStar_Tactics_Types.main_goal =
             (uu___364_1351.FStar_Tactics_Types.main_goal);
           FStar_Tactics_Types.all_implicits =
             (uu___364_1351.FStar_Tactics_Types.all_implicits);
           FStar_Tactics_Types.goals = uu____1352;
           FStar_Tactics_Types.smt_goals =
             (uu___364_1351.FStar_Tactics_Types.smt_goals);
           FStar_Tactics_Types.depth =
             (uu___364_1351.FStar_Tactics_Types.depth);
           FStar_Tactics_Types.__dump =
             (uu___364_1351.FStar_Tactics_Types.__dump);
           FStar_Tactics_Types.psc = (uu___364_1351.FStar_Tactics_Types.psc);
           FStar_Tactics_Types.entry_range =
             (uu___364_1351.FStar_Tactics_Types.entry_range);
           FStar_Tactics_Types.guard_policy =
             (uu___364_1351.FStar_Tactics_Types.guard_policy);
           FStar_Tactics_Types.freshness =
             (uu___364_1351.FStar_Tactics_Types.freshness);
           FStar_Tactics_Types.tac_verb_dbg =
             (uu___364_1351.FStar_Tactics_Types.tac_verb_dbg);
           FStar_Tactics_Types.local_state =
             (uu___364_1351.FStar_Tactics_Types.local_state)
         }  in
       set ps')
  
let (set_solution :
  FStar_Tactics_Types.goal -> FStar_Syntax_Syntax.term -> unit tac) =
  fun goal  ->
    fun solution  ->
      let uu____1375 =
        FStar_Syntax_Unionfind.find
          (goal.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_head
         in
      match uu____1375 with
      | FStar_Pervasives_Native.Some uu____1380 ->
          let uu____1381 =
            let uu____1382 = goal_to_string_verbose goal  in
            FStar_Util.format1 "Goal %s is already solved" uu____1382  in
          fail uu____1381
      | FStar_Pervasives_Native.None  ->
          (FStar_Syntax_Unionfind.change
             (goal.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_head
             solution;
           ret ())
  
let (trysolve :
  FStar_Tactics_Types.goal -> FStar_Syntax_Syntax.term -> Prims.bool tac) =
  fun goal  ->
    fun solution  ->
      let uu____1398 = FStar_Tactics_Types.goal_env goal  in
      let uu____1399 = FStar_Tactics_Types.goal_witness goal  in
      do_unify uu____1398 solution uu____1399
  
let (__dismiss : unit tac) =
  bind get
    (fun p  ->
       let uu____1405 =
         let uu___365_1406 = p  in
         let uu____1407 = FStar_List.tl p.FStar_Tactics_Types.goals  in
         {
           FStar_Tactics_Types.main_context =
             (uu___365_1406.FStar_Tactics_Types.main_context);
           FStar_Tactics_Types.main_goal =
             (uu___365_1406.FStar_Tactics_Types.main_goal);
           FStar_Tactics_Types.all_implicits =
             (uu___365_1406.FStar_Tactics_Types.all_implicits);
           FStar_Tactics_Types.goals = uu____1407;
           FStar_Tactics_Types.smt_goals =
             (uu___365_1406.FStar_Tactics_Types.smt_goals);
           FStar_Tactics_Types.depth =
             (uu___365_1406.FStar_Tactics_Types.depth);
           FStar_Tactics_Types.__dump =
             (uu___365_1406.FStar_Tactics_Types.__dump);
           FStar_Tactics_Types.psc = (uu___365_1406.FStar_Tactics_Types.psc);
           FStar_Tactics_Types.entry_range =
             (uu___365_1406.FStar_Tactics_Types.entry_range);
           FStar_Tactics_Types.guard_policy =
             (uu___365_1406.FStar_Tactics_Types.guard_policy);
           FStar_Tactics_Types.freshness =
             (uu___365_1406.FStar_Tactics_Types.freshness);
           FStar_Tactics_Types.tac_verb_dbg =
             (uu___365_1406.FStar_Tactics_Types.tac_verb_dbg);
           FStar_Tactics_Types.local_state =
             (uu___365_1406.FStar_Tactics_Types.local_state)
         }  in
       set uu____1405)
  
let (solve :
  FStar_Tactics_Types.goal -> FStar_Syntax_Syntax.term -> unit tac) =
  fun goal  ->
    fun solution  ->
      let e = FStar_Tactics_Types.goal_env goal  in
      mlog
        (fun uu____1428  ->
           let uu____1429 =
             let uu____1430 = FStar_Tactics_Types.goal_witness goal  in
             FStar_Syntax_Print.term_to_string uu____1430  in
           let uu____1431 = FStar_Syntax_Print.term_to_string solution  in
           FStar_Util.print2 "solve %s := %s\n" uu____1429 uu____1431)
        (fun uu____1434  ->
           let uu____1435 = trysolve goal solution  in
           bind uu____1435
             (fun b  ->
                if b
                then bind __dismiss (fun uu____1443  -> remove_solved_goals)
                else
                  (let uu____1445 =
                     let uu____1446 =
                       let uu____1447 = FStar_Tactics_Types.goal_env goal  in
                       tts uu____1447 solution  in
                     let uu____1448 =
                       let uu____1449 = FStar_Tactics_Types.goal_env goal  in
                       let uu____1450 = FStar_Tactics_Types.goal_witness goal
                          in
                       tts uu____1449 uu____1450  in
                     let uu____1451 =
                       let uu____1452 = FStar_Tactics_Types.goal_env goal  in
                       let uu____1453 = FStar_Tactics_Types.goal_type goal
                          in
                       tts uu____1452 uu____1453  in
                     FStar_Util.format3 "%s does not solve %s : %s"
                       uu____1446 uu____1448 uu____1451
                      in
                   fail uu____1445)))
  
let (solve' :
  FStar_Tactics_Types.goal -> FStar_Syntax_Syntax.term -> unit tac) =
  fun goal  ->
    fun solution  ->
      let uu____1468 = set_solution goal solution  in
      bind uu____1468
        (fun uu____1472  ->
           bind __dismiss (fun uu____1474  -> remove_solved_goals))
  
let (set_goals : FStar_Tactics_Types.goal Prims.list -> unit tac) =
  fun gs  ->
    bind get
      (fun ps  ->
         set
           (let uu___366_1492 = ps  in
            {
              FStar_Tactics_Types.main_context =
                (uu___366_1492.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___366_1492.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___366_1492.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals = gs;
              FStar_Tactics_Types.smt_goals =
                (uu___366_1492.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___366_1492.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___366_1492.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___366_1492.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___366_1492.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___366_1492.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___366_1492.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___366_1492.FStar_Tactics_Types.tac_verb_dbg);
              FStar_Tactics_Types.local_state =
                (uu___366_1492.FStar_Tactics_Types.local_state)
            }))
  
let (set_smt_goals : FStar_Tactics_Types.goal Prims.list -> unit tac) =
  fun gs  ->
    bind get
      (fun ps  ->
         set
           (let uu___367_1510 = ps  in
            {
              FStar_Tactics_Types.main_context =
                (uu___367_1510.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___367_1510.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___367_1510.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___367_1510.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals = gs;
              FStar_Tactics_Types.depth =
                (uu___367_1510.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___367_1510.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___367_1510.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___367_1510.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___367_1510.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___367_1510.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___367_1510.FStar_Tactics_Types.tac_verb_dbg);
              FStar_Tactics_Types.local_state =
                (uu___367_1510.FStar_Tactics_Types.local_state)
            }))
  
let (dismiss_all : unit tac) = set_goals [] 
let (nwarn : Prims.int FStar_ST.ref) =
  FStar_Util.mk_ref (Prims.parse_int "0") 
let (check_valid_goal : FStar_Tactics_Types.goal -> unit) =
  fun g  ->
    let uu____1531 = FStar_Options.defensive ()  in
    if uu____1531
    then
      let b = true  in
      let env = FStar_Tactics_Types.goal_env g  in
      let b1 =
        b &&
          (let uu____1536 = FStar_Tactics_Types.goal_witness g  in
           FStar_TypeChecker_Env.closed env uu____1536)
         in
      let b2 =
        b1 &&
          (let uu____1539 = FStar_Tactics_Types.goal_type g  in
           FStar_TypeChecker_Env.closed env uu____1539)
         in
      let rec aux b3 e =
        let uu____1551 = FStar_TypeChecker_Env.pop_bv e  in
        match uu____1551 with
        | FStar_Pervasives_Native.None  -> b3
        | FStar_Pervasives_Native.Some (bv,e1) ->
            let b4 =
              b3 &&
                (FStar_TypeChecker_Env.closed e1 bv.FStar_Syntax_Syntax.sort)
               in
            aux b4 e1
         in
      let uu____1569 =
        (let uu____1572 = aux b2 env  in Prims.op_Negation uu____1572) &&
          (let uu____1574 = FStar_ST.op_Bang nwarn  in
           uu____1574 < (Prims.parse_int "5"))
         in
      (if uu____1569
       then
         ((let uu____1595 =
             let uu____1596 = FStar_Tactics_Types.goal_type g  in
             uu____1596.FStar_Syntax_Syntax.pos  in
           let uu____1599 =
             let uu____1604 =
               let uu____1605 = goal_to_string_verbose g  in
               FStar_Util.format1
                 "The following goal is ill-formed. Keeping calm and carrying on...\n<%s>\n\n"
                 uu____1605
                in
             (FStar_Errors.Warning_IllFormedGoal, uu____1604)  in
           FStar_Errors.log_issue uu____1595 uu____1599);
          (let uu____1606 =
             let uu____1607 = FStar_ST.op_Bang nwarn  in
             uu____1607 + (Prims.parse_int "1")  in
           FStar_ST.op_Colon_Equals nwarn uu____1606))
       else ())
    else ()
  
let (add_goals : FStar_Tactics_Types.goal Prims.list -> unit tac) =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___368_1667 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___368_1667.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___368_1667.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___368_1667.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (FStar_List.append gs p.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (uu___368_1667.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___368_1667.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___368_1667.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___368_1667.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___368_1667.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___368_1667.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___368_1667.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___368_1667.FStar_Tactics_Types.tac_verb_dbg);
              FStar_Tactics_Types.local_state =
                (uu___368_1667.FStar_Tactics_Types.local_state)
            }))
  
let (add_smt_goals : FStar_Tactics_Types.goal Prims.list -> unit tac) =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___369_1687 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___369_1687.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___369_1687.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___369_1687.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___369_1687.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (FStar_List.append gs p.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___369_1687.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___369_1687.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___369_1687.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___369_1687.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___369_1687.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___369_1687.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___369_1687.FStar_Tactics_Types.tac_verb_dbg);
              FStar_Tactics_Types.local_state =
                (uu___369_1687.FStar_Tactics_Types.local_state)
            }))
  
let (push_goals : FStar_Tactics_Types.goal Prims.list -> unit tac) =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___370_1707 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___370_1707.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___370_1707.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___370_1707.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (FStar_List.append p.FStar_Tactics_Types.goals gs);
              FStar_Tactics_Types.smt_goals =
                (uu___370_1707.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___370_1707.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___370_1707.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___370_1707.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___370_1707.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___370_1707.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___370_1707.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___370_1707.FStar_Tactics_Types.tac_verb_dbg);
              FStar_Tactics_Types.local_state =
                (uu___370_1707.FStar_Tactics_Types.local_state)
            }))
  
let (push_smt_goals : FStar_Tactics_Types.goal Prims.list -> unit tac) =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___371_1727 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___371_1727.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___371_1727.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___371_1727.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___371_1727.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (FStar_List.append p.FStar_Tactics_Types.smt_goals gs);
              FStar_Tactics_Types.depth =
                (uu___371_1727.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___371_1727.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___371_1727.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___371_1727.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___371_1727.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___371_1727.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___371_1727.FStar_Tactics_Types.tac_verb_dbg);
              FStar_Tactics_Types.local_state =
                (uu___371_1727.FStar_Tactics_Types.local_state)
            }))
  
let (replace_cur : FStar_Tactics_Types.goal -> unit tac) =
  fun g  -> bind __dismiss (fun uu____1738  -> add_goals [g]) 
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
        let uu____1766 =
          FStar_TypeChecker_Env.new_implicit_var_aux reason
            typ.FStar_Syntax_Syntax.pos env typ
            FStar_Syntax_Syntax.Allow_untyped
           in
        match uu____1766 with
        | (u,ctx_uvar,g_u) ->
            let uu____1800 =
              add_implicits g_u.FStar_TypeChecker_Env.implicits  in
            bind uu____1800
              (fun uu____1809  ->
                 let uu____1810 =
                   let uu____1815 =
                     let uu____1816 = FStar_List.hd ctx_uvar  in
                     FStar_Pervasives_Native.fst uu____1816  in
                   (u, uu____1815)  in
                 ret uu____1810)
  
let (is_true : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____1834 = FStar_Syntax_Util.un_squash t  in
    match uu____1834 with
    | FStar_Pervasives_Native.Some t' ->
        let uu____1844 =
          let uu____1845 = FStar_Syntax_Subst.compress t'  in
          uu____1845.FStar_Syntax_Syntax.n  in
        (match uu____1844 with
         | FStar_Syntax_Syntax.Tm_fvar fv ->
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.true_lid
         | uu____1849 -> false)
    | uu____1850 -> false
  
let (is_false : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____1860 = FStar_Syntax_Util.un_squash t  in
    match uu____1860 with
    | FStar_Pervasives_Native.Some t' ->
        let uu____1870 =
          let uu____1871 = FStar_Syntax_Subst.compress t'  in
          uu____1871.FStar_Syntax_Syntax.n  in
        (match uu____1870 with
         | FStar_Syntax_Syntax.Tm_fvar fv ->
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.false_lid
         | uu____1875 -> false)
    | uu____1876 -> false
  
let (cur_goal : unit -> FStar_Tactics_Types.goal tac) =
  fun uu____1887  ->
    bind get
      (fun p  ->
         match p.FStar_Tactics_Types.goals with
         | [] -> fail "No more goals (1)"
         | hd1::tl1 ->
             let uu____1898 =
               FStar_Syntax_Unionfind.find
                 (hd1.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_head
                in
             (match uu____1898 with
              | FStar_Pervasives_Native.None  -> ret hd1
              | FStar_Pervasives_Native.Some t ->
                  ((let uu____1905 = goal_to_string_verbose hd1  in
                    let uu____1906 = FStar_Syntax_Print.term_to_string t  in
                    FStar_Util.print2
                      "!!!!!!!!!!!! GOAL IS ALREADY SOLVED! %s\nsol is %s\n"
                      uu____1905 uu____1906);
                   ret hd1)))
  
let (tadmit : unit -> unit tac) =
  fun uu____1913  ->
    let uu____1916 =
      bind get
        (fun ps  ->
           let uu____1922 = cur_goal ()  in
           bind uu____1922
             (fun g  ->
                (let uu____1929 =
                   let uu____1930 = FStar_Tactics_Types.goal_type g  in
                   uu____1930.FStar_Syntax_Syntax.pos  in
                 let uu____1933 =
                   let uu____1938 =
                     let uu____1939 = goal_to_string ps g  in
                     FStar_Util.format1 "Tactics admitted goal <%s>\n\n"
                       uu____1939
                      in
                   (FStar_Errors.Warning_TacAdmit, uu____1938)  in
                 FStar_Errors.log_issue uu____1929 uu____1933);
                solve' g FStar_Syntax_Util.exp_unit))
       in
    FStar_All.pipe_left (wrap_err "tadmit") uu____1916
  
let (fresh : unit -> FStar_BigInt.t tac) =
  fun uu____1950  ->
    bind get
      (fun ps  ->
         let n1 = ps.FStar_Tactics_Types.freshness  in
         let ps1 =
           let uu___372_1960 = ps  in
           {
             FStar_Tactics_Types.main_context =
               (uu___372_1960.FStar_Tactics_Types.main_context);
             FStar_Tactics_Types.main_goal =
               (uu___372_1960.FStar_Tactics_Types.main_goal);
             FStar_Tactics_Types.all_implicits =
               (uu___372_1960.FStar_Tactics_Types.all_implicits);
             FStar_Tactics_Types.goals =
               (uu___372_1960.FStar_Tactics_Types.goals);
             FStar_Tactics_Types.smt_goals =
               (uu___372_1960.FStar_Tactics_Types.smt_goals);
             FStar_Tactics_Types.depth =
               (uu___372_1960.FStar_Tactics_Types.depth);
             FStar_Tactics_Types.__dump =
               (uu___372_1960.FStar_Tactics_Types.__dump);
             FStar_Tactics_Types.psc =
               (uu___372_1960.FStar_Tactics_Types.psc);
             FStar_Tactics_Types.entry_range =
               (uu___372_1960.FStar_Tactics_Types.entry_range);
             FStar_Tactics_Types.guard_policy =
               (uu___372_1960.FStar_Tactics_Types.guard_policy);
             FStar_Tactics_Types.freshness = (n1 + (Prims.parse_int "1"));
             FStar_Tactics_Types.tac_verb_dbg =
               (uu___372_1960.FStar_Tactics_Types.tac_verb_dbg);
             FStar_Tactics_Types.local_state =
               (uu___372_1960.FStar_Tactics_Types.local_state)
           }  in
         let uu____1961 = set ps1  in
         bind uu____1961
           (fun uu____1966  ->
              let uu____1967 = FStar_BigInt.of_int_fs n1  in ret uu____1967))
  
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
            let uu____1995 = env.FStar_TypeChecker_Env.universe_of env phi
               in
            FStar_Syntax_Util.mk_squash uu____1995 phi  in
          let uu____1996 = new_uvar reason env typ  in
          bind uu____1996
            (fun uu____2011  ->
               match uu____2011 with
               | (uu____2018,ctx_uvar) ->
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
             (fun uu____2063  ->
                let uu____2064 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.print1 "Tac> __tc(%s)\n" uu____2064)
             (fun uu____2067  ->
                let e1 =
                  let uu___373_2069 = e  in
                  {
                    FStar_TypeChecker_Env.solver =
                      (uu___373_2069.FStar_TypeChecker_Env.solver);
                    FStar_TypeChecker_Env.range =
                      (uu___373_2069.FStar_TypeChecker_Env.range);
                    FStar_TypeChecker_Env.curmodule =
                      (uu___373_2069.FStar_TypeChecker_Env.curmodule);
                    FStar_TypeChecker_Env.gamma =
                      (uu___373_2069.FStar_TypeChecker_Env.gamma);
                    FStar_TypeChecker_Env.gamma_sig =
                      (uu___373_2069.FStar_TypeChecker_Env.gamma_sig);
                    FStar_TypeChecker_Env.gamma_cache =
                      (uu___373_2069.FStar_TypeChecker_Env.gamma_cache);
                    FStar_TypeChecker_Env.modules =
                      (uu___373_2069.FStar_TypeChecker_Env.modules);
                    FStar_TypeChecker_Env.expected_typ =
                      (uu___373_2069.FStar_TypeChecker_Env.expected_typ);
                    FStar_TypeChecker_Env.sigtab =
                      (uu___373_2069.FStar_TypeChecker_Env.sigtab);
                    FStar_TypeChecker_Env.attrtab =
                      (uu___373_2069.FStar_TypeChecker_Env.attrtab);
                    FStar_TypeChecker_Env.is_pattern =
                      (uu___373_2069.FStar_TypeChecker_Env.is_pattern);
                    FStar_TypeChecker_Env.instantiate_imp =
                      (uu___373_2069.FStar_TypeChecker_Env.instantiate_imp);
                    FStar_TypeChecker_Env.effects =
                      (uu___373_2069.FStar_TypeChecker_Env.effects);
                    FStar_TypeChecker_Env.generalize =
                      (uu___373_2069.FStar_TypeChecker_Env.generalize);
                    FStar_TypeChecker_Env.letrecs =
                      (uu___373_2069.FStar_TypeChecker_Env.letrecs);
                    FStar_TypeChecker_Env.top_level =
                      (uu___373_2069.FStar_TypeChecker_Env.top_level);
                    FStar_TypeChecker_Env.check_uvars =
                      (uu___373_2069.FStar_TypeChecker_Env.check_uvars);
                    FStar_TypeChecker_Env.use_eq =
                      (uu___373_2069.FStar_TypeChecker_Env.use_eq);
                    FStar_TypeChecker_Env.is_iface =
                      (uu___373_2069.FStar_TypeChecker_Env.is_iface);
                    FStar_TypeChecker_Env.admit =
                      (uu___373_2069.FStar_TypeChecker_Env.admit);
                    FStar_TypeChecker_Env.lax =
                      (uu___373_2069.FStar_TypeChecker_Env.lax);
                    FStar_TypeChecker_Env.lax_universes =
                      (uu___373_2069.FStar_TypeChecker_Env.lax_universes);
                    FStar_TypeChecker_Env.phase1 =
                      (uu___373_2069.FStar_TypeChecker_Env.phase1);
                    FStar_TypeChecker_Env.failhard =
                      (uu___373_2069.FStar_TypeChecker_Env.failhard);
                    FStar_TypeChecker_Env.nosynth =
                      (uu___373_2069.FStar_TypeChecker_Env.nosynth);
                    FStar_TypeChecker_Env.uvar_subtyping = false;
                    FStar_TypeChecker_Env.tc_term =
                      (uu___373_2069.FStar_TypeChecker_Env.tc_term);
                    FStar_TypeChecker_Env.type_of =
                      (uu___373_2069.FStar_TypeChecker_Env.type_of);
                    FStar_TypeChecker_Env.universe_of =
                      (uu___373_2069.FStar_TypeChecker_Env.universe_of);
                    FStar_TypeChecker_Env.check_type_of =
                      (uu___373_2069.FStar_TypeChecker_Env.check_type_of);
                    FStar_TypeChecker_Env.use_bv_sorts =
                      (uu___373_2069.FStar_TypeChecker_Env.use_bv_sorts);
                    FStar_TypeChecker_Env.qtbl_name_and_index =
                      (uu___373_2069.FStar_TypeChecker_Env.qtbl_name_and_index);
                    FStar_TypeChecker_Env.normalized_eff_names =
                      (uu___373_2069.FStar_TypeChecker_Env.normalized_eff_names);
                    FStar_TypeChecker_Env.proof_ns =
                      (uu___373_2069.FStar_TypeChecker_Env.proof_ns);
                    FStar_TypeChecker_Env.synth_hook =
                      (uu___373_2069.FStar_TypeChecker_Env.synth_hook);
                    FStar_TypeChecker_Env.splice =
                      (uu___373_2069.FStar_TypeChecker_Env.splice);
                    FStar_TypeChecker_Env.is_native_tactic =
                      (uu___373_2069.FStar_TypeChecker_Env.is_native_tactic);
                    FStar_TypeChecker_Env.identifier_info =
                      (uu___373_2069.FStar_TypeChecker_Env.identifier_info);
                    FStar_TypeChecker_Env.tc_hooks =
                      (uu___373_2069.FStar_TypeChecker_Env.tc_hooks);
                    FStar_TypeChecker_Env.dsenv =
                      (uu___373_2069.FStar_TypeChecker_Env.dsenv);
                    FStar_TypeChecker_Env.dep_graph =
                      (uu___373_2069.FStar_TypeChecker_Env.dep_graph);
                    FStar_TypeChecker_Env.nbe =
                      (uu___373_2069.FStar_TypeChecker_Env.nbe)
                  }  in
                try
                  (fun uu___375_2080  ->
                     match () with
                     | () ->
                         let uu____2089 =
                           (ps.FStar_Tactics_Types.main_context).FStar_TypeChecker_Env.type_of
                             e1 t
                            in
                         ret uu____2089) ()
                with
                | FStar_Errors.Err (uu____2116,msg) ->
                    let uu____2118 = tts e1 t  in
                    let uu____2119 =
                      let uu____2120 = FStar_TypeChecker_Env.all_binders e1
                         in
                      FStar_All.pipe_right uu____2120
                        (FStar_Syntax_Print.binders_to_string ", ")
                       in
                    fail3 "Cannot type %s in context (%s). Error = (%s)"
                      uu____2118 uu____2119 msg
                | FStar_Errors.Error (uu____2127,msg,uu____2129) ->
                    let uu____2130 = tts e1 t  in
                    let uu____2131 =
                      let uu____2132 = FStar_TypeChecker_Env.all_binders e1
                         in
                      FStar_All.pipe_right uu____2132
                        (FStar_Syntax_Print.binders_to_string ", ")
                       in
                    fail3 "Cannot type %s in context (%s). Error = (%s)"
                      uu____2130 uu____2131 msg))
  
let (istrivial : env -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun e  ->
    fun t  ->
      let steps =
        [FStar_TypeChecker_Env.Reify;
        FStar_TypeChecker_Env.UnfoldUntil FStar_Syntax_Syntax.delta_constant;
        FStar_TypeChecker_Env.Primops;
        FStar_TypeChecker_Env.Simplify;
        FStar_TypeChecker_Env.UnfoldTac;
        FStar_TypeChecker_Env.Unmeta]  in
      let t1 = normalize steps e t  in is_true t1
  
let (get_guard_policy : unit -> FStar_Tactics_Types.guard_policy tac) =
  fun uu____2159  ->
    bind get (fun ps  -> ret ps.FStar_Tactics_Types.guard_policy)
  
let (set_guard_policy : FStar_Tactics_Types.guard_policy -> unit tac) =
  fun pol  ->
    bind get
      (fun ps  ->
         set
           (let uu___376_2177 = ps  in
            {
              FStar_Tactics_Types.main_context =
                (uu___376_2177.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___376_2177.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___376_2177.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___376_2177.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (uu___376_2177.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___376_2177.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___376_2177.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___376_2177.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___376_2177.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy = pol;
              FStar_Tactics_Types.freshness =
                (uu___376_2177.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___376_2177.FStar_Tactics_Types.tac_verb_dbg);
              FStar_Tactics_Types.local_state =
                (uu___376_2177.FStar_Tactics_Types.local_state)
            }))
  
let with_policy : 'a . FStar_Tactics_Types.guard_policy -> 'a tac -> 'a tac =
  fun pol  ->
    fun t  ->
      let uu____2201 = get_guard_policy ()  in
      bind uu____2201
        (fun old_pol  ->
           let uu____2207 = set_guard_policy pol  in
           bind uu____2207
             (fun uu____2211  ->
                bind t
                  (fun r  ->
                     let uu____2215 = set_guard_policy old_pol  in
                     bind uu____2215 (fun uu____2219  -> ret r))))
  
let (getopts : FStar_Options.optionstate tac) =
  let uu____2222 = let uu____2227 = cur_goal ()  in trytac uu____2227  in
  bind uu____2222
    (fun uu___346_2234  ->
       match uu___346_2234 with
       | FStar_Pervasives_Native.Some g -> ret g.FStar_Tactics_Types.opts
       | FStar_Pervasives_Native.None  ->
           let uu____2240 = FStar_Options.peek ()  in ret uu____2240)
  
let (proc_guard :
  Prims.string -> env -> FStar_TypeChecker_Env.guard_t -> unit tac) =
  fun reason  ->
    fun e  ->
      fun g  ->
        mlog
          (fun uu____2262  ->
             let uu____2263 = FStar_TypeChecker_Rel.guard_to_string e g  in
             FStar_Util.print2 "Processing guard (%s:%s)\n" reason uu____2263)
          (fun uu____2266  ->
             let uu____2267 = add_implicits g.FStar_TypeChecker_Env.implicits
                in
             bind uu____2267
               (fun uu____2271  ->
                  bind getopts
                    (fun opts  ->
                       let uu____2275 =
                         let uu____2276 =
                           FStar_TypeChecker_Rel.simplify_guard e g  in
                         uu____2276.FStar_TypeChecker_Env.guard_f  in
                       match uu____2275 with
                       | FStar_TypeChecker_Common.Trivial  -> ret ()
                       | FStar_TypeChecker_Common.NonTrivial f ->
                           let uu____2280 = istrivial e f  in
                           if uu____2280
                           then ret ()
                           else
                             bind get
                               (fun ps  ->
                                  match ps.FStar_Tactics_Types.guard_policy
                                  with
                                  | FStar_Tactics_Types.Drop  ->
                                      ((let uu____2290 =
                                          let uu____2295 =
                                            let uu____2296 =
                                              FStar_TypeChecker_Rel.guard_to_string
                                                e g
                                               in
                                            FStar_Util.format1
                                              "Tactics admitted guard <%s>\n\n"
                                              uu____2296
                                             in
                                          (FStar_Errors.Warning_TacAdmit,
                                            uu____2295)
                                           in
                                        FStar_Errors.log_issue
                                          e.FStar_TypeChecker_Env.range
                                          uu____2290);
                                       ret ())
                                  | FStar_Tactics_Types.Goal  ->
                                      mlog
                                        (fun uu____2299  ->
                                           let uu____2300 =
                                             FStar_TypeChecker_Rel.guard_to_string
                                               e g
                                              in
                                           FStar_Util.print2
                                             "Making guard (%s:%s) into a goal\n"
                                             reason uu____2300)
                                        (fun uu____2303  ->
                                           let uu____2304 =
                                             mk_irrelevant_goal reason e f
                                               opts
                                              in
                                           bind uu____2304
                                             (fun goal  ->
                                                let goal1 =
                                                  let uu___377_2311 = goal
                                                     in
                                                  {
                                                    FStar_Tactics_Types.goal_main_env
                                                      =
                                                      (uu___377_2311.FStar_Tactics_Types.goal_main_env);
                                                    FStar_Tactics_Types.goal_ctx_uvar
                                                      =
                                                      (uu___377_2311.FStar_Tactics_Types.goal_ctx_uvar);
                                                    FStar_Tactics_Types.opts
                                                      =
                                                      (uu___377_2311.FStar_Tactics_Types.opts);
                                                    FStar_Tactics_Types.is_guard
                                                      = true
                                                  }  in
                                                push_goals [goal1]))
                                  | FStar_Tactics_Types.SMT  ->
                                      mlog
                                        (fun uu____2314  ->
                                           let uu____2315 =
                                             FStar_TypeChecker_Rel.guard_to_string
                                               e g
                                              in
                                           FStar_Util.print2
                                             "Sending guard (%s:%s) to SMT goal\n"
                                             reason uu____2315)
                                        (fun uu____2318  ->
                                           let uu____2319 =
                                             mk_irrelevant_goal reason e f
                                               opts
                                              in
                                           bind uu____2319
                                             (fun goal  ->
                                                let goal1 =
                                                  let uu___378_2326 = goal
                                                     in
                                                  {
                                                    FStar_Tactics_Types.goal_main_env
                                                      =
                                                      (uu___378_2326.FStar_Tactics_Types.goal_main_env);
                                                    FStar_Tactics_Types.goal_ctx_uvar
                                                      =
                                                      (uu___378_2326.FStar_Tactics_Types.goal_ctx_uvar);
                                                    FStar_Tactics_Types.opts
                                                      =
                                                      (uu___378_2326.FStar_Tactics_Types.opts);
                                                    FStar_Tactics_Types.is_guard
                                                      = true
                                                  }  in
                                                push_smt_goals [goal1]))
                                  | FStar_Tactics_Types.Force  ->
                                      mlog
                                        (fun uu____2329  ->
                                           let uu____2330 =
                                             FStar_TypeChecker_Rel.guard_to_string
                                               e g
                                              in
                                           FStar_Util.print2
                                             "Forcing guard (%s:%s)\n" reason
                                             uu____2330)
                                        (fun uu____2332  ->
                                           try
                                             (fun uu___380_2337  ->
                                                match () with
                                                | () ->
                                                    let uu____2340 =
                                                      let uu____2341 =
                                                        let uu____2342 =
                                                          FStar_TypeChecker_Rel.discharge_guard_no_smt
                                                            e g
                                                           in
                                                        FStar_All.pipe_left
                                                          FStar_TypeChecker_Env.is_trivial
                                                          uu____2342
                                                         in
                                                      Prims.op_Negation
                                                        uu____2341
                                                       in
                                                    if uu____2340
                                                    then
                                                      mlog
                                                        (fun uu____2347  ->
                                                           let uu____2348 =
                                                             FStar_TypeChecker_Rel.guard_to_string
                                                               e g
                                                              in
                                                           FStar_Util.print1
                                                             "guard = %s\n"
                                                             uu____2348)
                                                        (fun uu____2350  ->
                                                           fail1
                                                             "Forcing the guard failed (%s)"
                                                             reason)
                                                    else ret ()) ()
                                           with
                                           | uu___379_2353 ->
                                               mlog
                                                 (fun uu____2358  ->
                                                    let uu____2359 =
                                                      FStar_TypeChecker_Rel.guard_to_string
                                                        e g
                                                       in
                                                    FStar_Util.print1
                                                      "guard = %s\n"
                                                      uu____2359)
                                                 (fun uu____2361  ->
                                                    fail1
                                                      "Forcing the guard failed (%s)"
                                                      reason))))))
  
let (tc : FStar_Syntax_Syntax.term -> FStar_Reflection_Data.typ tac) =
  fun t  ->
    let uu____2371 =
      let uu____2374 = cur_goal ()  in
      bind uu____2374
        (fun goal  ->
           let uu____2380 =
             let uu____2389 = FStar_Tactics_Types.goal_env goal  in
             __tc uu____2389 t  in
           bind uu____2380
             (fun uu____2400  ->
                match uu____2400 with
                | (uu____2409,typ,uu____2411) -> ret typ))
       in
    FStar_All.pipe_left (wrap_err "tc") uu____2371
  
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
                           (let uu___381_2524 = goal  in
                            {
                              FStar_Tactics_Types.goal_main_env =
                                (uu___381_2524.FStar_Tactics_Types.goal_main_env);
                              FStar_Tactics_Types.goal_ctx_uvar =
                                (uu___381_2524.FStar_Tactics_Types.goal_ctx_uvar);
                              FStar_Tactics_Types.opts =
                                (uu___381_2524.FStar_Tactics_Types.opts);
                              FStar_Tactics_Types.is_guard = true
                            }))))
  
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
             let uu____2573 =
               try
                 (fun uu___386_2596  ->
                    match () with
                    | () ->
                        let uu____2607 =
                          let uu____2616 = FStar_BigInt.to_int_fs n1  in
                          FStar_List.splitAt uu____2616
                            p.FStar_Tactics_Types.goals
                           in
                        ret uu____2607) ()
               with | uu___385_2626 -> fail "divide: not enough goals"  in
             bind uu____2573
               (fun uu____2662  ->
                  match uu____2662 with
                  | (lgs,rgs) ->
                      let lp =
                        let uu___382_2688 = p  in
                        {
                          FStar_Tactics_Types.main_context =
                            (uu___382_2688.FStar_Tactics_Types.main_context);
                          FStar_Tactics_Types.main_goal =
                            (uu___382_2688.FStar_Tactics_Types.main_goal);
                          FStar_Tactics_Types.all_implicits =
                            (uu___382_2688.FStar_Tactics_Types.all_implicits);
                          FStar_Tactics_Types.goals = lgs;
                          FStar_Tactics_Types.smt_goals = [];
                          FStar_Tactics_Types.depth =
                            (uu___382_2688.FStar_Tactics_Types.depth);
                          FStar_Tactics_Types.__dump =
                            (uu___382_2688.FStar_Tactics_Types.__dump);
                          FStar_Tactics_Types.psc =
                            (uu___382_2688.FStar_Tactics_Types.psc);
                          FStar_Tactics_Types.entry_range =
                            (uu___382_2688.FStar_Tactics_Types.entry_range);
                          FStar_Tactics_Types.guard_policy =
                            (uu___382_2688.FStar_Tactics_Types.guard_policy);
                          FStar_Tactics_Types.freshness =
                            (uu___382_2688.FStar_Tactics_Types.freshness);
                          FStar_Tactics_Types.tac_verb_dbg =
                            (uu___382_2688.FStar_Tactics_Types.tac_verb_dbg);
                          FStar_Tactics_Types.local_state =
                            (uu___382_2688.FStar_Tactics_Types.local_state)
                        }  in
                      let uu____2689 = set lp  in
                      bind uu____2689
                        (fun uu____2697  ->
                           bind l
                             (fun a  ->
                                bind get
                                  (fun lp'  ->
                                     let rp =
                                       let uu___383_2713 = lp'  in
                                       {
                                         FStar_Tactics_Types.main_context =
                                           (uu___383_2713.FStar_Tactics_Types.main_context);
                                         FStar_Tactics_Types.main_goal =
                                           (uu___383_2713.FStar_Tactics_Types.main_goal);
                                         FStar_Tactics_Types.all_implicits =
                                           (uu___383_2713.FStar_Tactics_Types.all_implicits);
                                         FStar_Tactics_Types.goals = rgs;
                                         FStar_Tactics_Types.smt_goals = [];
                                         FStar_Tactics_Types.depth =
                                           (uu___383_2713.FStar_Tactics_Types.depth);
                                         FStar_Tactics_Types.__dump =
                                           (uu___383_2713.FStar_Tactics_Types.__dump);
                                         FStar_Tactics_Types.psc =
                                           (uu___383_2713.FStar_Tactics_Types.psc);
                                         FStar_Tactics_Types.entry_range =
                                           (uu___383_2713.FStar_Tactics_Types.entry_range);
                                         FStar_Tactics_Types.guard_policy =
                                           (uu___383_2713.FStar_Tactics_Types.guard_policy);
                                         FStar_Tactics_Types.freshness =
                                           (uu___383_2713.FStar_Tactics_Types.freshness);
                                         FStar_Tactics_Types.tac_verb_dbg =
                                           (uu___383_2713.FStar_Tactics_Types.tac_verb_dbg);
                                         FStar_Tactics_Types.local_state =
                                           (uu___383_2713.FStar_Tactics_Types.local_state)
                                       }  in
                                     let uu____2714 = set rp  in
                                     bind uu____2714
                                       (fun uu____2722  ->
                                          bind r
                                            (fun b  ->
                                               bind get
                                                 (fun rp'  ->
                                                    let p' =
                                                      let uu___384_2738 = rp'
                                                         in
                                                      {
                                                        FStar_Tactics_Types.main_context
                                                          =
                                                          (uu___384_2738.FStar_Tactics_Types.main_context);
                                                        FStar_Tactics_Types.main_goal
                                                          =
                                                          (uu___384_2738.FStar_Tactics_Types.main_goal);
                                                        FStar_Tactics_Types.all_implicits
                                                          =
                                                          (uu___384_2738.FStar_Tactics_Types.all_implicits);
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
                                                          (uu___384_2738.FStar_Tactics_Types.depth);
                                                        FStar_Tactics_Types.__dump
                                                          =
                                                          (uu___384_2738.FStar_Tactics_Types.__dump);
                                                        FStar_Tactics_Types.psc
                                                          =
                                                          (uu___384_2738.FStar_Tactics_Types.psc);
                                                        FStar_Tactics_Types.entry_range
                                                          =
                                                          (uu___384_2738.FStar_Tactics_Types.entry_range);
                                                        FStar_Tactics_Types.guard_policy
                                                          =
                                                          (uu___384_2738.FStar_Tactics_Types.guard_policy);
                                                        FStar_Tactics_Types.freshness
                                                          =
                                                          (uu___384_2738.FStar_Tactics_Types.freshness);
                                                        FStar_Tactics_Types.tac_verb_dbg
                                                          =
                                                          (uu___384_2738.FStar_Tactics_Types.tac_verb_dbg);
                                                        FStar_Tactics_Types.local_state
                                                          =
                                                          (uu___384_2738.FStar_Tactics_Types.local_state)
                                                      }  in
                                                    let uu____2739 = set p'
                                                       in
                                                    bind uu____2739
                                                      (fun uu____2747  ->
                                                         bind
                                                           remove_solved_goals
                                                           (fun uu____2753 
                                                              -> ret (a, b)))))))))))
  
let focus : 'a . 'a tac -> 'a tac =
  fun f  ->
    let uu____2774 = divide FStar_BigInt.one f idtac  in
    bind uu____2774
      (fun uu____2787  -> match uu____2787 with | (a,()) -> ret a)
  
let rec map : 'a . 'a tac -> 'a Prims.list tac =
  fun tau  ->
    bind get
      (fun p  ->
         match p.FStar_Tactics_Types.goals with
         | [] -> ret []
         | uu____2824::uu____2825 ->
             let uu____2828 =
               let uu____2837 = map tau  in
               divide FStar_BigInt.one tau uu____2837  in
             bind uu____2828
               (fun uu____2855  ->
                  match uu____2855 with | (h,t) -> ret (h :: t)))
  
let (seq : unit tac -> unit tac -> unit tac) =
  fun t1  ->
    fun t2  ->
      let uu____2896 =
        bind t1
          (fun uu____2901  ->
             let uu____2902 = map t2  in
             bind uu____2902 (fun uu____2910  -> ret ()))
         in
      focus uu____2896
  
let (intro : unit -> FStar_Syntax_Syntax.binder tac) =
  fun uu____2919  ->
    let uu____2922 =
      let uu____2925 = cur_goal ()  in
      bind uu____2925
        (fun goal  ->
           let uu____2934 =
             let uu____2941 = FStar_Tactics_Types.goal_type goal  in
             FStar_Syntax_Util.arrow_one uu____2941  in
           match uu____2934 with
           | FStar_Pervasives_Native.Some (b,c) ->
               let uu____2950 =
                 let uu____2951 = FStar_Syntax_Util.is_total_comp c  in
                 Prims.op_Negation uu____2951  in
               if uu____2950
               then fail "Codomain is effectful"
               else
                 (let env' =
                    let uu____2956 = FStar_Tactics_Types.goal_env goal  in
                    FStar_TypeChecker_Env.push_binders uu____2956 [b]  in
                  let typ' = comp_to_typ c  in
                  let uu____2970 = new_uvar "intro" env' typ'  in
                  bind uu____2970
                    (fun uu____2986  ->
                       match uu____2986 with
                       | (body,ctx_uvar) ->
                           let sol =
                             FStar_Syntax_Util.abs [b] body
                               (FStar_Pervasives_Native.Some
                                  (FStar_Syntax_Util.residual_comp_of_comp c))
                              in
                           let uu____3010 = set_solution goal sol  in
                           bind uu____3010
                             (fun uu____3016  ->
                                let g =
                                  FStar_Tactics_Types.mk_goal env' ctx_uvar
                                    goal.FStar_Tactics_Types.opts
                                    goal.FStar_Tactics_Types.is_guard
                                   in
                                let uu____3018 =
                                  let uu____3021 = bnorm_goal g  in
                                  replace_cur uu____3021  in
                                bind uu____3018 (fun uu____3023  -> ret b))))
           | FStar_Pervasives_Native.None  ->
               let uu____3028 =
                 let uu____3029 = FStar_Tactics_Types.goal_env goal  in
                 let uu____3030 = FStar_Tactics_Types.goal_type goal  in
                 tts uu____3029 uu____3030  in
               fail1 "goal is not an arrow (%s)" uu____3028)
       in
    FStar_All.pipe_left (wrap_err "intro") uu____2922
  
let (intro_rec :
  unit ->
    (FStar_Syntax_Syntax.binder,FStar_Syntax_Syntax.binder)
      FStar_Pervasives_Native.tuple2 tac)
  =
  fun uu____3045  ->
    let uu____3052 = cur_goal ()  in
    bind uu____3052
      (fun goal  ->
         FStar_Util.print_string
           "WARNING (intro_rec): calling this is known to cause normalizer loops\n";
         FStar_Util.print_string
           "WARNING (intro_rec): proceed at your own risk...\n";
         (let uu____3069 =
            let uu____3076 = FStar_Tactics_Types.goal_type goal  in
            FStar_Syntax_Util.arrow_one uu____3076  in
          match uu____3069 with
          | FStar_Pervasives_Native.Some (b,c) ->
              let uu____3089 =
                let uu____3090 = FStar_Syntax_Util.is_total_comp c  in
                Prims.op_Negation uu____3090  in
              if uu____3089
              then fail "Codomain is effectful"
              else
                (let bv =
                   let uu____3103 = FStar_Tactics_Types.goal_type goal  in
                   FStar_Syntax_Syntax.gen_bv "__recf"
                     FStar_Pervasives_Native.None uu____3103
                    in
                 let bs =
                   let uu____3113 = FStar_Syntax_Syntax.mk_binder bv  in
                   [uu____3113; b]  in
                 let env' =
                   let uu____3139 = FStar_Tactics_Types.goal_env goal  in
                   FStar_TypeChecker_Env.push_binders uu____3139 bs  in
                 let uu____3140 =
                   let uu____3147 = comp_to_typ c  in
                   new_uvar "intro_rec" env' uu____3147  in
                 bind uu____3140
                   (fun uu____3166  ->
                      match uu____3166 with
                      | (u,ctx_uvar_u) ->
                          let lb =
                            let uu____3180 =
                              FStar_Tactics_Types.goal_type goal  in
                            let uu____3183 =
                              FStar_Syntax_Util.abs [b] u
                                FStar_Pervasives_Native.None
                               in
                            FStar_Syntax_Util.mk_letbinding
                              (FStar_Util.Inl bv) [] uu____3180
                              FStar_Parser_Const.effect_Tot_lid uu____3183 []
                              FStar_Range.dummyRange
                             in
                          let body = FStar_Syntax_Syntax.bv_to_name bv  in
                          let uu____3201 =
                            FStar_Syntax_Subst.close_let_rec [lb] body  in
                          (match uu____3201 with
                           | (lbs,body1) ->
                               let tm =
                                 let uu____3223 =
                                   let uu____3224 =
                                     FStar_Tactics_Types.goal_witness goal
                                      in
                                   uu____3224.FStar_Syntax_Syntax.pos  in
                                 FStar_Syntax_Syntax.mk
                                   (FStar_Syntax_Syntax.Tm_let
                                      ((true, lbs), body1))
                                   FStar_Pervasives_Native.None uu____3223
                                  in
                               let uu____3237 = set_solution goal tm  in
                               bind uu____3237
                                 (fun uu____3246  ->
                                    let uu____3247 =
                                      let uu____3250 =
                                        bnorm_goal
                                          (let uu___387_3253 = goal  in
                                           {
                                             FStar_Tactics_Types.goal_main_env
                                               =
                                               (uu___387_3253.FStar_Tactics_Types.goal_main_env);
                                             FStar_Tactics_Types.goal_ctx_uvar
                                               = ctx_uvar_u;
                                             FStar_Tactics_Types.opts =
                                               (uu___387_3253.FStar_Tactics_Types.opts);
                                             FStar_Tactics_Types.is_guard =
                                               (uu___387_3253.FStar_Tactics_Types.is_guard)
                                           })
                                         in
                                      replace_cur uu____3250  in
                                    bind uu____3247
                                      (fun uu____3260  ->
                                         let uu____3261 =
                                           let uu____3266 =
                                             FStar_Syntax_Syntax.mk_binder bv
                                              in
                                           (uu____3266, b)  in
                                         ret uu____3261)))))
          | FStar_Pervasives_Native.None  ->
              let uu____3275 =
                let uu____3276 = FStar_Tactics_Types.goal_env goal  in
                let uu____3277 = FStar_Tactics_Types.goal_type goal  in
                tts uu____3276 uu____3277  in
              fail1 "intro_rec: goal is not an arrow (%s)" uu____3275))
  
let (norm : FStar_Syntax_Embeddings.norm_step Prims.list -> unit tac) =
  fun s  ->
    let uu____3295 = cur_goal ()  in
    bind uu____3295
      (fun goal  ->
         mlog
           (fun uu____3302  ->
              let uu____3303 =
                let uu____3304 = FStar_Tactics_Types.goal_witness goal  in
                FStar_Syntax_Print.term_to_string uu____3304  in
              FStar_Util.print1 "norm: witness = %s\n" uu____3303)
           (fun uu____3309  ->
              let steps =
                let uu____3313 = FStar_TypeChecker_Normalize.tr_norm_steps s
                   in
                FStar_List.append
                  [FStar_TypeChecker_Env.Reify;
                  FStar_TypeChecker_Env.UnfoldTac] uu____3313
                 in
              let t =
                let uu____3317 = FStar_Tactics_Types.goal_env goal  in
                let uu____3318 = FStar_Tactics_Types.goal_type goal  in
                normalize steps uu____3317 uu____3318  in
              let uu____3319 = FStar_Tactics_Types.goal_with_type goal t  in
              replace_cur uu____3319))
  
let (norm_term_env :
  env ->
    FStar_Syntax_Embeddings.norm_step Prims.list ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term tac)
  =
  fun e  ->
    fun s  ->
      fun t  ->
        let uu____3343 =
          mlog
            (fun uu____3348  ->
               let uu____3349 = FStar_Syntax_Print.term_to_string t  in
               FStar_Util.print1 "norm_term: tm = %s\n" uu____3349)
            (fun uu____3351  ->
               bind get
                 (fun ps  ->
                    let opts =
                      match ps.FStar_Tactics_Types.goals with
                      | g::uu____3357 -> g.FStar_Tactics_Types.opts
                      | uu____3360 -> FStar_Options.peek ()  in
                    mlog
                      (fun uu____3365  ->
                         let uu____3366 = FStar_Syntax_Print.term_to_string t
                            in
                         FStar_Util.print1 "norm_term_env: t = %s\n"
                           uu____3366)
                      (fun uu____3369  ->
                         let uu____3370 = __tc e t  in
                         bind uu____3370
                           (fun uu____3391  ->
                              match uu____3391 with
                              | (t1,uu____3401,uu____3402) ->
                                  let steps =
                                    let uu____3406 =
                                      FStar_TypeChecker_Normalize.tr_norm_steps
                                        s
                                       in
                                    FStar_List.append
                                      [FStar_TypeChecker_Env.Reify;
                                      FStar_TypeChecker_Env.UnfoldTac]
                                      uu____3406
                                     in
                                  let t2 =
                                    normalize steps
                                      ps.FStar_Tactics_Types.main_context t1
                                     in
                                  ret t2))))
           in
        FStar_All.pipe_left (wrap_err "norm_term") uu____3343
  
let (refine_intro : unit -> unit tac) =
  fun uu____3420  ->
    let uu____3423 =
      let uu____3426 = cur_goal ()  in
      bind uu____3426
        (fun g  ->
           let uu____3433 =
             let uu____3444 = FStar_Tactics_Types.goal_env g  in
             let uu____3445 = FStar_Tactics_Types.goal_type g  in
             FStar_TypeChecker_Rel.base_and_refinement uu____3444 uu____3445
              in
           match uu____3433 with
           | (uu____3448,FStar_Pervasives_Native.None ) ->
               fail "not a refinement"
           | (t,FStar_Pervasives_Native.Some (bv,phi)) ->
               let g1 = FStar_Tactics_Types.goal_with_type g t  in
               let uu____3473 =
                 let uu____3478 =
                   let uu____3483 =
                     let uu____3484 = FStar_Syntax_Syntax.mk_binder bv  in
                     [uu____3484]  in
                   FStar_Syntax_Subst.open_term uu____3483 phi  in
                 match uu____3478 with
                 | (bvs,phi1) ->
                     let uu____3509 =
                       let uu____3510 = FStar_List.hd bvs  in
                       FStar_Pervasives_Native.fst uu____3510  in
                     (uu____3509, phi1)
                  in
               (match uu____3473 with
                | (bv1,phi1) ->
                    let uu____3529 =
                      let uu____3532 = FStar_Tactics_Types.goal_env g  in
                      let uu____3533 =
                        let uu____3534 =
                          let uu____3537 =
                            let uu____3538 =
                              let uu____3545 =
                                FStar_Tactics_Types.goal_witness g  in
                              (bv1, uu____3545)  in
                            FStar_Syntax_Syntax.NT uu____3538  in
                          [uu____3537]  in
                        FStar_Syntax_Subst.subst uu____3534 phi1  in
                      mk_irrelevant_goal "refine_intro refinement" uu____3532
                        uu____3533 g.FStar_Tactics_Types.opts
                       in
                    bind uu____3529
                      (fun g2  ->
                         bind __dismiss
                           (fun uu____3553  -> add_goals [g1; g2]))))
       in
    FStar_All.pipe_left (wrap_err "refine_intro") uu____3423
  
let (__exact_now : Prims.bool -> FStar_Syntax_Syntax.term -> unit tac) =
  fun set_expected_typ1  ->
    fun t  ->
      let uu____3572 = cur_goal ()  in
      bind uu____3572
        (fun goal  ->
           let env =
             if set_expected_typ1
             then
               let uu____3580 = FStar_Tactics_Types.goal_env goal  in
               let uu____3581 = FStar_Tactics_Types.goal_type goal  in
               FStar_TypeChecker_Env.set_expected_typ uu____3580 uu____3581
             else FStar_Tactics_Types.goal_env goal  in
           let uu____3583 = __tc env t  in
           bind uu____3583
             (fun uu____3602  ->
                match uu____3602 with
                | (t1,typ,guard) ->
                    mlog
                      (fun uu____3617  ->
                         let uu____3618 =
                           FStar_Syntax_Print.term_to_string typ  in
                         let uu____3619 =
                           let uu____3620 = FStar_Tactics_Types.goal_env goal
                              in
                           FStar_TypeChecker_Rel.guard_to_string uu____3620
                             guard
                            in
                         FStar_Util.print2
                           "__exact_now: got type %s\n__exact_now: and guard %s\n"
                           uu____3618 uu____3619)
                      (fun uu____3623  ->
                         let uu____3624 =
                           let uu____3627 = FStar_Tactics_Types.goal_env goal
                              in
                           proc_guard "__exact typing" uu____3627 guard  in
                         bind uu____3624
                           (fun uu____3629  ->
                              mlog
                                (fun uu____3633  ->
                                   let uu____3634 =
                                     FStar_Syntax_Print.term_to_string typ
                                      in
                                   let uu____3635 =
                                     let uu____3636 =
                                       FStar_Tactics_Types.goal_type goal  in
                                     FStar_Syntax_Print.term_to_string
                                       uu____3636
                                      in
                                   FStar_Util.print2
                                     "__exact_now: unifying %s and %s\n"
                                     uu____3634 uu____3635)
                                (fun uu____3639  ->
                                   let uu____3640 =
                                     let uu____3643 =
                                       FStar_Tactics_Types.goal_env goal  in
                                     let uu____3644 =
                                       FStar_Tactics_Types.goal_type goal  in
                                     do_unify uu____3643 typ uu____3644  in
                                   bind uu____3640
                                     (fun b  ->
                                        if b
                                        then solve goal t1
                                        else
                                          (let uu____3650 =
                                             let uu____3651 =
                                               FStar_Tactics_Types.goal_env
                                                 goal
                                                in
                                             tts uu____3651 t1  in
                                           let uu____3652 =
                                             let uu____3653 =
                                               FStar_Tactics_Types.goal_env
                                                 goal
                                                in
                                             tts uu____3653 typ  in
                                           let uu____3654 =
                                             let uu____3655 =
                                               FStar_Tactics_Types.goal_env
                                                 goal
                                                in
                                             let uu____3656 =
                                               FStar_Tactics_Types.goal_type
                                                 goal
                                                in
                                             tts uu____3655 uu____3656  in
                                           let uu____3657 =
                                             let uu____3658 =
                                               FStar_Tactics_Types.goal_env
                                                 goal
                                                in
                                             let uu____3659 =
                                               FStar_Tactics_Types.goal_witness
                                                 goal
                                                in
                                             tts uu____3658 uu____3659  in
                                           fail4
                                             "%s : %s does not exactly solve the goal %s (witness = %s)"
                                             uu____3650 uu____3652 uu____3654
                                             uu____3657)))))))
  
let (t_exact :
  Prims.bool -> Prims.bool -> FStar_Syntax_Syntax.term -> unit tac) =
  fun try_refine  ->
    fun set_expected_typ1  ->
      fun tm  ->
        let uu____3679 =
          mlog
            (fun uu____3684  ->
               let uu____3685 = FStar_Syntax_Print.term_to_string tm  in
               FStar_Util.print1 "t_exact: tm = %s\n" uu____3685)
            (fun uu____3688  ->
               let uu____3689 =
                 let uu____3696 = __exact_now set_expected_typ1 tm  in
                 catch uu____3696  in
               bind uu____3689
                 (fun uu___348_3705  ->
                    match uu___348_3705 with
                    | FStar_Util.Inr r -> ret ()
                    | FStar_Util.Inl e when Prims.op_Negation try_refine ->
                        fail e
                    | FStar_Util.Inl e ->
                        mlog
                          (fun uu____3716  ->
                             FStar_Util.print_string
                               "__exact_now failed, trying refine...\n")
                          (fun uu____3719  ->
                             let uu____3720 =
                               let uu____3727 =
                                 let uu____3730 =
                                   norm [FStar_Syntax_Embeddings.Delta]  in
                                 bind uu____3730
                                   (fun uu____3735  ->
                                      let uu____3736 = refine_intro ()  in
                                      bind uu____3736
                                        (fun uu____3740  ->
                                           __exact_now set_expected_typ1 tm))
                                  in
                               catch uu____3727  in
                             bind uu____3720
                               (fun uu___347_3747  ->
                                  match uu___347_3747 with
                                  | FStar_Util.Inr r -> ret ()
                                  | FStar_Util.Inl uu____3755 -> fail e))))
           in
        FStar_All.pipe_left (wrap_err "exact") uu____3679
  
let rec mapM : 'a 'b . ('a -> 'b tac) -> 'a Prims.list -> 'b Prims.list tac =
  fun f  ->
    fun l  ->
      match l with
      | [] -> ret []
      | x::xs ->
          let uu____3805 = f x  in
          bind uu____3805
            (fun y  ->
               let uu____3813 = mapM f xs  in
               bind uu____3813 (fun ys  -> ret (y :: ys)))
  
let rec (__try_match_by_application :
  (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.aqual,FStar_Syntax_Syntax.ctx_uvar)
    FStar_Pervasives_Native.tuple3 Prims.list ->
    env ->
      FStar_Syntax_Syntax.term ->
        FStar_Syntax_Syntax.term ->
          (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.aqual,FStar_Syntax_Syntax.ctx_uvar)
            FStar_Pervasives_Native.tuple3 Prims.list tac)
  =
  fun acc  ->
    fun e  ->
      fun ty1  ->
        fun ty2  ->
          let uu____3884 = do_unify e ty1 ty2  in
          bind uu____3884
            (fun uu___349_3896  ->
               if uu___349_3896
               then ret acc
               else
                 (let uu____3915 = FStar_Syntax_Util.arrow_one ty1  in
                  match uu____3915 with
                  | FStar_Pervasives_Native.None  ->
                      let uu____3936 = FStar_Syntax_Print.term_to_string ty1
                         in
                      let uu____3937 = FStar_Syntax_Print.term_to_string ty2
                         in
                      fail2 "Could not instantiate, %s to %s" uu____3936
                        uu____3937
                  | FStar_Pervasives_Native.Some (b,c) ->
                      let uu____3952 =
                        let uu____3953 = FStar_Syntax_Util.is_total_comp c
                           in
                        Prims.op_Negation uu____3953  in
                      if uu____3952
                      then fail "Codomain is effectful"
                      else
                        (let uu____3973 =
                           new_uvar "apply arg" e
                             (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                            in
                         bind uu____3973
                           (fun uu____3999  ->
                              match uu____3999 with
                              | (uvt,uv) ->
                                  let typ = comp_to_typ c  in
                                  let typ' =
                                    FStar_Syntax_Subst.subst
                                      [FStar_Syntax_Syntax.NT
                                         ((FStar_Pervasives_Native.fst b),
                                           uvt)] typ
                                     in
                                  __try_match_by_application
                                    ((uvt, (FStar_Pervasives_Native.snd b),
                                       uv) :: acc) e typ' ty2))))
  
let (try_match_by_application :
  env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term ->
        (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.aqual,FStar_Syntax_Syntax.ctx_uvar)
          FStar_Pervasives_Native.tuple3 Prims.list tac)
  = fun e  -> fun ty1  -> fun ty2  -> __try_match_by_application [] e ty1 ty2 
let (t_apply : Prims.bool -> FStar_Syntax_Syntax.term -> unit tac) =
  fun uopt  ->
    fun tm  ->
      let uu____4085 =
        mlog
          (fun uu____4090  ->
             let uu____4091 = FStar_Syntax_Print.term_to_string tm  in
             FStar_Util.print1 "t_apply: tm = %s\n" uu____4091)
          (fun uu____4094  ->
             let uu____4095 = cur_goal ()  in
             bind uu____4095
               (fun goal  ->
                  let e = FStar_Tactics_Types.goal_env goal  in
                  let uu____4103 = __tc e tm  in
                  bind uu____4103
                    (fun uu____4124  ->
                       match uu____4124 with
                       | (tm1,typ,guard) ->
                           let typ1 = bnorm e typ  in
                           let uu____4137 =
                             let uu____4148 =
                               FStar_Tactics_Types.goal_type goal  in
                             try_match_by_application e typ1 uu____4148  in
                           bind uu____4137
                             (fun uvs  ->
                                let w =
                                  FStar_List.fold_right
                                    (fun uu____4191  ->
                                       fun w  ->
                                         match uu____4191 with
                                         | (uvt,q,uu____4209) ->
                                             FStar_Syntax_Util.mk_app w
                                               [(uvt, q)]) uvs tm1
                                   in
                                let uvset =
                                  let uu____4241 =
                                    FStar_Syntax_Free.new_uv_set ()  in
                                  FStar_List.fold_right
                                    (fun uu____4258  ->
                                       fun s  ->
                                         match uu____4258 with
                                         | (uu____4270,uu____4271,uv) ->
                                             let uu____4273 =
                                               FStar_Syntax_Free.uvars
                                                 uv.FStar_Syntax_Syntax.ctx_uvar_typ
                                                in
                                             FStar_Util.set_union s
                                               uu____4273) uvs uu____4241
                                   in
                                let free_in_some_goal uv =
                                  FStar_Util.set_mem uv uvset  in
                                let uu____4282 = solve' goal w  in
                                bind uu____4282
                                  (fun uu____4287  ->
                                     let uu____4288 =
                                       mapM
                                         (fun uu____4305  ->
                                            match uu____4305 with
                                            | (uvt,q,uv) ->
                                                let uu____4317 =
                                                  FStar_Syntax_Unionfind.find
                                                    uv.FStar_Syntax_Syntax.ctx_uvar_head
                                                   in
                                                (match uu____4317 with
                                                 | FStar_Pervasives_Native.Some
                                                     uu____4322 -> ret ()
                                                 | FStar_Pervasives_Native.None
                                                      ->
                                                     let uu____4323 =
                                                       uopt &&
                                                         (free_in_some_goal
                                                            uv)
                                                        in
                                                     if uu____4323
                                                     then ret ()
                                                     else
                                                       (let uu____4327 =
                                                          let uu____4330 =
                                                            bnorm_goal
                                                              (let uu___388_4333
                                                                 = goal  in
                                                               {
                                                                 FStar_Tactics_Types.goal_main_env
                                                                   =
                                                                   (uu___388_4333.FStar_Tactics_Types.goal_main_env);
                                                                 FStar_Tactics_Types.goal_ctx_uvar
                                                                   = uv;
                                                                 FStar_Tactics_Types.opts
                                                                   =
                                                                   (uu___388_4333.FStar_Tactics_Types.opts);
                                                                 FStar_Tactics_Types.is_guard
                                                                   = false
                                                               })
                                                             in
                                                          [uu____4330]  in
                                                        add_goals uu____4327)))
                                         uvs
                                        in
                                     bind uu____4288
                                       (fun uu____4337  ->
                                          proc_guard "apply guard" e guard))))))
         in
      FStar_All.pipe_left (wrap_err "apply") uu____4085
  
let (lemma_or_sq :
  FStar_Syntax_Syntax.comp ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun c  ->
    let ct = FStar_Syntax_Util.comp_to_comp_typ_nouniv c  in
    let uu____4362 =
      FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
        FStar_Parser_Const.effect_Lemma_lid
       in
    if uu____4362
    then
      let uu____4369 =
        match ct.FStar_Syntax_Syntax.effect_args with
        | pre::post::uu____4384 ->
            ((FStar_Pervasives_Native.fst pre),
              (FStar_Pervasives_Native.fst post))
        | uu____4437 -> failwith "apply_lemma: impossible: not a lemma"  in
      match uu____4369 with
      | (pre,post) ->
          let post1 =
            let uu____4469 =
              let uu____4480 =
                FStar_Syntax_Syntax.as_arg FStar_Syntax_Util.exp_unit  in
              [uu____4480]  in
            FStar_Syntax_Util.mk_app post uu____4469  in
          FStar_Pervasives_Native.Some (pre, post1)
    else
      (let uu____4510 =
         FStar_Syntax_Util.is_pure_effect ct.FStar_Syntax_Syntax.effect_name
          in
       if uu____4510
       then
         let uu____4517 =
           FStar_Syntax_Util.un_squash ct.FStar_Syntax_Syntax.result_typ  in
         FStar_Util.map_opt uu____4517
           (fun post  -> (FStar_Syntax_Util.t_true, post))
       else FStar_Pervasives_Native.None)
  
let (apply_lemma : FStar_Syntax_Syntax.term -> unit tac) =
  fun tm  ->
    let uu____4550 =
      let uu____4553 =
        bind get
          (fun ps  ->
             mlog
               (fun uu____4560  ->
                  let uu____4561 = FStar_Syntax_Print.term_to_string tm  in
                  FStar_Util.print1 "apply_lemma: tm = %s\n" uu____4561)
               (fun uu____4565  ->
                  let is_unit_t t =
                    let uu____4572 =
                      let uu____4573 = FStar_Syntax_Subst.compress t  in
                      uu____4573.FStar_Syntax_Syntax.n  in
                    match uu____4572 with
                    | FStar_Syntax_Syntax.Tm_fvar fv when
                        FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.unit_lid
                        -> true
                    | uu____4577 -> false  in
                  let uu____4578 = cur_goal ()  in
                  bind uu____4578
                    (fun goal  ->
                       let uu____4584 =
                         let uu____4593 = FStar_Tactics_Types.goal_env goal
                            in
                         __tc uu____4593 tm  in
                       bind uu____4584
                         (fun uu____4608  ->
                            match uu____4608 with
                            | (tm1,t,guard) ->
                                let uu____4620 =
                                  FStar_Syntax_Util.arrow_formals_comp t  in
                                (match uu____4620 with
                                 | (bs,comp) ->
                                     let uu____4653 = lemma_or_sq comp  in
                                     (match uu____4653 with
                                      | FStar_Pervasives_Native.None  ->
                                          fail
                                            "not a lemma or squashed function"
                                      | FStar_Pervasives_Native.Some
                                          (pre,post) ->
                                          let uu____4672 =
                                            FStar_List.fold_left
                                              (fun uu____4720  ->
                                                 fun uu____4721  ->
                                                   match (uu____4720,
                                                           uu____4721)
                                                   with
                                                   | ((uvs,guard1,subst1),
                                                      (b,aq)) ->
                                                       let b_t =
                                                         FStar_Syntax_Subst.subst
                                                           subst1
                                                           b.FStar_Syntax_Syntax.sort
                                                          in
                                                       let uu____4834 =
                                                         is_unit_t b_t  in
                                                       if uu____4834
                                                       then
                                                         (((FStar_Syntax_Util.exp_unit,
                                                             aq) :: uvs),
                                                           guard1,
                                                           ((FStar_Syntax_Syntax.NT
                                                               (b,
                                                                 FStar_Syntax_Util.exp_unit))
                                                           :: subst1))
                                                       else
                                                         (let uu____4872 =
                                                            let uu____4885 =
                                                              let uu____4886
                                                                =
                                                                FStar_Tactics_Types.goal_type
                                                                  goal
                                                                 in
                                                              uu____4886.FStar_Syntax_Syntax.pos
                                                               in
                                                            let uu____4889 =
                                                              FStar_Tactics_Types.goal_env
                                                                goal
                                                               in
                                                            FStar_TypeChecker_Util.new_implicit_var
                                                              "apply_lemma"
                                                              uu____4885
                                                              uu____4889 b_t
                                                             in
                                                          match uu____4872
                                                          with
                                                          | (u,uu____4907,g_u)
                                                              ->
                                                              let uu____4921
                                                                =
                                                                FStar_TypeChecker_Env.conj_guard
                                                                  guard1 g_u
                                                                 in
                                                              (((u, aq) ::
                                                                uvs),
                                                                uu____4921,
                                                                ((FStar_Syntax_Syntax.NT
                                                                    (b, u))
                                                                :: subst1))))
                                              ([], guard, []) bs
                                             in
                                          (match uu____4672 with
                                           | (uvs,implicits,subst1) ->
                                               let uvs1 = FStar_List.rev uvs
                                                  in
                                               let pre1 =
                                                 FStar_Syntax_Subst.subst
                                                   subst1 pre
                                                  in
                                               let post1 =
                                                 FStar_Syntax_Subst.subst
                                                   subst1 post
                                                  in
                                               let uu____5000 =
                                                 let uu____5003 =
                                                   FStar_Tactics_Types.goal_env
                                                     goal
                                                    in
                                                 let uu____5004 =
                                                   FStar_Syntax_Util.mk_squash
                                                     FStar_Syntax_Syntax.U_zero
                                                     post1
                                                    in
                                                 let uu____5005 =
                                                   FStar_Tactics_Types.goal_type
                                                     goal
                                                    in
                                                 do_unify uu____5003
                                                   uu____5004 uu____5005
                                                  in
                                               bind uu____5000
                                                 (fun b  ->
                                                    if Prims.op_Negation b
                                                    then
                                                      let uu____5013 =
                                                        let uu____5014 =
                                                          FStar_Tactics_Types.goal_env
                                                            goal
                                                           in
                                                        tts uu____5014 tm1
                                                         in
                                                      let uu____5015 =
                                                        let uu____5016 =
                                                          FStar_Tactics_Types.goal_env
                                                            goal
                                                           in
                                                        let uu____5017 =
                                                          FStar_Syntax_Util.mk_squash
                                                            FStar_Syntax_Syntax.U_zero
                                                            post1
                                                           in
                                                        tts uu____5016
                                                          uu____5017
                                                         in
                                                      let uu____5018 =
                                                        let uu____5019 =
                                                          FStar_Tactics_Types.goal_env
                                                            goal
                                                           in
                                                        let uu____5020 =
                                                          FStar_Tactics_Types.goal_type
                                                            goal
                                                           in
                                                        tts uu____5019
                                                          uu____5020
                                                         in
                                                      fail3
                                                        "Cannot instantiate lemma %s (with postcondition: %s) to match goal (%s)"
                                                        uu____5013 uu____5015
                                                        uu____5018
                                                    else
                                                      (let uu____5022 =
                                                         add_implicits
                                                           implicits.FStar_TypeChecker_Env.implicits
                                                          in
                                                       bind uu____5022
                                                         (fun uu____5027  ->
                                                            let uu____5028 =
                                                              solve' goal
                                                                FStar_Syntax_Util.exp_unit
                                                               in
                                                            bind uu____5028
                                                              (fun uu____5036
                                                                  ->
                                                                 let is_free_uvar
                                                                   uv t1 =
                                                                   let free_uvars
                                                                    =
                                                                    let uu____5061
                                                                    =
                                                                    let uu____5064
                                                                    =
                                                                    FStar_Syntax_Free.uvars
                                                                    t1  in
                                                                    FStar_Util.set_elements
                                                                    uu____5064
                                                                     in
                                                                    FStar_List.map
                                                                    (fun x 
                                                                    ->
                                                                    x.FStar_Syntax_Syntax.ctx_uvar_head)
                                                                    uu____5061
                                                                     in
                                                                   FStar_List.existsML
                                                                    (fun u 
                                                                    ->
                                                                    FStar_Syntax_Unionfind.equiv
                                                                    u uv)
                                                                    free_uvars
                                                                    in
                                                                 let appears
                                                                   uv goals =
                                                                   FStar_List.existsML
                                                                    (fun g' 
                                                                    ->
                                                                    let uu____5099
                                                                    =
                                                                    FStar_Tactics_Types.goal_type
                                                                    g'  in
                                                                    is_free_uvar
                                                                    uv
                                                                    uu____5099)
                                                                    goals
                                                                    in
                                                                 let checkone
                                                                   t1 goals =
                                                                   let uu____5115
                                                                    =
                                                                    FStar_Syntax_Util.head_and_args
                                                                    t1  in
                                                                   match uu____5115
                                                                   with
                                                                   | 
                                                                   (hd1,uu____5133)
                                                                    ->
                                                                    (match 
                                                                    hd1.FStar_Syntax_Syntax.n
                                                                    with
                                                                    | 
                                                                    FStar_Syntax_Syntax.Tm_uvar
                                                                    (uv,uu____5159)
                                                                    ->
                                                                    appears
                                                                    uv.FStar_Syntax_Syntax.ctx_uvar_head
                                                                    goals
                                                                    | 
                                                                    uu____5176
                                                                    -> false)
                                                                    in
                                                                 let uu____5177
                                                                   =
                                                                   FStar_All.pipe_right
                                                                    implicits.FStar_TypeChecker_Env.implicits
                                                                    (mapM
                                                                    (fun imp 
                                                                    ->
                                                                    let term
                                                                    =
                                                                    imp.FStar_TypeChecker_Env.imp_tm
                                                                     in
                                                                    let ctx_uvar
                                                                    =
                                                                    imp.FStar_TypeChecker_Env.imp_uvar
                                                                     in
                                                                    let uu____5207
                                                                    =
                                                                    FStar_Syntax_Util.head_and_args
                                                                    term  in
                                                                    match uu____5207
                                                                    with
                                                                    | 
                                                                    (hd1,uu____5229)
                                                                    ->
                                                                    let uu____5254
                                                                    =
                                                                    let uu____5255
                                                                    =
                                                                    FStar_Syntax_Subst.compress
                                                                    hd1  in
                                                                    uu____5255.FStar_Syntax_Syntax.n
                                                                     in
                                                                    (match uu____5254
                                                                    with
                                                                    | 
                                                                    FStar_Syntax_Syntax.Tm_uvar
                                                                    (ctx_uvar1,uu____5263)
                                                                    ->
                                                                    let goal1
                                                                    =
                                                                    bnorm_goal
                                                                    (let uu___389_5283
                                                                    = goal
                                                                     in
                                                                    {
                                                                    FStar_Tactics_Types.goal_main_env
                                                                    =
                                                                    (uu___389_5283.FStar_Tactics_Types.goal_main_env);
                                                                    FStar_Tactics_Types.goal_ctx_uvar
                                                                    =
                                                                    ctx_uvar1;
                                                                    FStar_Tactics_Types.opts
                                                                    =
                                                                    (uu___389_5283.FStar_Tactics_Types.opts);
                                                                    FStar_Tactics_Types.is_guard
                                                                    =
                                                                    (uu___389_5283.FStar_Tactics_Types.is_guard)
                                                                    })  in
                                                                    ret
                                                                    [goal1]
                                                                    | 
                                                                    uu____5286
                                                                    ->
                                                                    mlog
                                                                    (fun
                                                                    uu____5292
                                                                     ->
                                                                    let uu____5293
                                                                    =
                                                                    FStar_Syntax_Print.uvar_to_string
                                                                    ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_head
                                                                     in
                                                                    let uu____5294
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    term  in
                                                                    FStar_Util.print2
                                                                    "apply_lemma: arg %s unified to (%s)\n"
                                                                    uu____5293
                                                                    uu____5294)
                                                                    (fun
                                                                    uu____5299
                                                                     ->
                                                                    let env =
                                                                    let uu___390_5301
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    goal  in
                                                                    {
                                                                    FStar_TypeChecker_Env.solver
                                                                    =
                                                                    (uu___390_5301.FStar_TypeChecker_Env.solver);
                                                                    FStar_TypeChecker_Env.range
                                                                    =
                                                                    (uu___390_5301.FStar_TypeChecker_Env.range);
                                                                    FStar_TypeChecker_Env.curmodule
                                                                    =
                                                                    (uu___390_5301.FStar_TypeChecker_Env.curmodule);
                                                                    FStar_TypeChecker_Env.gamma
                                                                    =
                                                                    (ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_gamma);
                                                                    FStar_TypeChecker_Env.gamma_sig
                                                                    =
                                                                    (uu___390_5301.FStar_TypeChecker_Env.gamma_sig);
                                                                    FStar_TypeChecker_Env.gamma_cache
                                                                    =
                                                                    (uu___390_5301.FStar_TypeChecker_Env.gamma_cache);
                                                                    FStar_TypeChecker_Env.modules
                                                                    =
                                                                    (uu___390_5301.FStar_TypeChecker_Env.modules);
                                                                    FStar_TypeChecker_Env.expected_typ
                                                                    =
                                                                    (uu___390_5301.FStar_TypeChecker_Env.expected_typ);
                                                                    FStar_TypeChecker_Env.sigtab
                                                                    =
                                                                    (uu___390_5301.FStar_TypeChecker_Env.sigtab);
                                                                    FStar_TypeChecker_Env.attrtab
                                                                    =
                                                                    (uu___390_5301.FStar_TypeChecker_Env.attrtab);
                                                                    FStar_TypeChecker_Env.is_pattern
                                                                    =
                                                                    (uu___390_5301.FStar_TypeChecker_Env.is_pattern);
                                                                    FStar_TypeChecker_Env.instantiate_imp
                                                                    =
                                                                    (uu___390_5301.FStar_TypeChecker_Env.instantiate_imp);
                                                                    FStar_TypeChecker_Env.effects
                                                                    =
                                                                    (uu___390_5301.FStar_TypeChecker_Env.effects);
                                                                    FStar_TypeChecker_Env.generalize
                                                                    =
                                                                    (uu___390_5301.FStar_TypeChecker_Env.generalize);
                                                                    FStar_TypeChecker_Env.letrecs
                                                                    =
                                                                    (uu___390_5301.FStar_TypeChecker_Env.letrecs);
                                                                    FStar_TypeChecker_Env.top_level
                                                                    =
                                                                    (uu___390_5301.FStar_TypeChecker_Env.top_level);
                                                                    FStar_TypeChecker_Env.check_uvars
                                                                    =
                                                                    (uu___390_5301.FStar_TypeChecker_Env.check_uvars);
                                                                    FStar_TypeChecker_Env.use_eq
                                                                    =
                                                                    (uu___390_5301.FStar_TypeChecker_Env.use_eq);
                                                                    FStar_TypeChecker_Env.is_iface
                                                                    =
                                                                    (uu___390_5301.FStar_TypeChecker_Env.is_iface);
                                                                    FStar_TypeChecker_Env.admit
                                                                    =
                                                                    (uu___390_5301.FStar_TypeChecker_Env.admit);
                                                                    FStar_TypeChecker_Env.lax
                                                                    =
                                                                    (uu___390_5301.FStar_TypeChecker_Env.lax);
                                                                    FStar_TypeChecker_Env.lax_universes
                                                                    =
                                                                    (uu___390_5301.FStar_TypeChecker_Env.lax_universes);
                                                                    FStar_TypeChecker_Env.phase1
                                                                    =
                                                                    (uu___390_5301.FStar_TypeChecker_Env.phase1);
                                                                    FStar_TypeChecker_Env.failhard
                                                                    =
                                                                    (uu___390_5301.FStar_TypeChecker_Env.failhard);
                                                                    FStar_TypeChecker_Env.nosynth
                                                                    =
                                                                    (uu___390_5301.FStar_TypeChecker_Env.nosynth);
                                                                    FStar_TypeChecker_Env.uvar_subtyping
                                                                    =
                                                                    (uu___390_5301.FStar_TypeChecker_Env.uvar_subtyping);
                                                                    FStar_TypeChecker_Env.tc_term
                                                                    =
                                                                    (uu___390_5301.FStar_TypeChecker_Env.tc_term);
                                                                    FStar_TypeChecker_Env.type_of
                                                                    =
                                                                    (uu___390_5301.FStar_TypeChecker_Env.type_of);
                                                                    FStar_TypeChecker_Env.universe_of
                                                                    =
                                                                    (uu___390_5301.FStar_TypeChecker_Env.universe_of);
                                                                    FStar_TypeChecker_Env.check_type_of
                                                                    =
                                                                    (uu___390_5301.FStar_TypeChecker_Env.check_type_of);
                                                                    FStar_TypeChecker_Env.use_bv_sorts
                                                                    =
                                                                    (uu___390_5301.FStar_TypeChecker_Env.use_bv_sorts);
                                                                    FStar_TypeChecker_Env.qtbl_name_and_index
                                                                    =
                                                                    (uu___390_5301.FStar_TypeChecker_Env.qtbl_name_and_index);
                                                                    FStar_TypeChecker_Env.normalized_eff_names
                                                                    =
                                                                    (uu___390_5301.FStar_TypeChecker_Env.normalized_eff_names);
                                                                    FStar_TypeChecker_Env.proof_ns
                                                                    =
                                                                    (uu___390_5301.FStar_TypeChecker_Env.proof_ns);
                                                                    FStar_TypeChecker_Env.synth_hook
                                                                    =
                                                                    (uu___390_5301.FStar_TypeChecker_Env.synth_hook);
                                                                    FStar_TypeChecker_Env.splice
                                                                    =
                                                                    (uu___390_5301.FStar_TypeChecker_Env.splice);
                                                                    FStar_TypeChecker_Env.is_native_tactic
                                                                    =
                                                                    (uu___390_5301.FStar_TypeChecker_Env.is_native_tactic);
                                                                    FStar_TypeChecker_Env.identifier_info
                                                                    =
                                                                    (uu___390_5301.FStar_TypeChecker_Env.identifier_info);
                                                                    FStar_TypeChecker_Env.tc_hooks
                                                                    =
                                                                    (uu___390_5301.FStar_TypeChecker_Env.tc_hooks);
                                                                    FStar_TypeChecker_Env.dsenv
                                                                    =
                                                                    (uu___390_5301.FStar_TypeChecker_Env.dsenv);
                                                                    FStar_TypeChecker_Env.dep_graph
                                                                    =
                                                                    (uu___390_5301.FStar_TypeChecker_Env.dep_graph);
                                                                    FStar_TypeChecker_Env.nbe
                                                                    =
                                                                    (uu___390_5301.FStar_TypeChecker_Env.nbe)
                                                                    }  in
                                                                    let g_typ
                                                                    =
                                                                    FStar_TypeChecker_TcTerm.check_type_of_well_typed_term'
                                                                    true env
                                                                    term
                                                                    ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_typ
                                                                     in
                                                                    let uu____5303
                                                                    =
                                                                    let uu____5306
                                                                    =
                                                                    if
                                                                    ps.FStar_Tactics_Types.tac_verb_dbg
                                                                    then
                                                                    let uu____5307
                                                                    =
                                                                    FStar_Syntax_Print.ctx_uvar_to_string
                                                                    ctx_uvar
                                                                     in
                                                                    let uu____5308
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    term  in
                                                                    FStar_Util.format2
                                                                    "apply_lemma solved arg %s to %s\n"
                                                                    uu____5307
                                                                    uu____5308
                                                                    else
                                                                    "apply_lemma solved arg"
                                                                     in
                                                                    let uu____5310
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    goal  in
                                                                    proc_guard
                                                                    uu____5306
                                                                    uu____5310
                                                                    g_typ  in
                                                                    bind
                                                                    uu____5303
                                                                    (fun
                                                                    uu____5314
                                                                     ->
                                                                    ret [])))))
                                                                    in
                                                                 bind
                                                                   uu____5177
                                                                   (fun
                                                                    sub_goals
                                                                     ->
                                                                    let sub_goals1
                                                                    =
                                                                    FStar_List.flatten
                                                                    sub_goals
                                                                     in
                                                                    let rec filter'
                                                                    f xs =
                                                                    match xs
                                                                    with
                                                                    | 
                                                                    [] -> []
                                                                    | 
                                                                    x::xs1 ->
                                                                    let uu____5376
                                                                    = f x xs1
                                                                     in
                                                                    if
                                                                    uu____5376
                                                                    then
                                                                    let uu____5379
                                                                    =
                                                                    filter' f
                                                                    xs1  in x
                                                                    ::
                                                                    uu____5379
                                                                    else
                                                                    filter' f
                                                                    xs1  in
                                                                    let sub_goals2
                                                                    =
                                                                    filter'
                                                                    (fun g 
                                                                    ->
                                                                    fun goals
                                                                     ->
                                                                    let uu____5393
                                                                    =
                                                                    let uu____5394
                                                                    =
                                                                    FStar_Tactics_Types.goal_witness
                                                                    g  in
                                                                    checkone
                                                                    uu____5394
                                                                    goals  in
                                                                    Prims.op_Negation
                                                                    uu____5393)
                                                                    sub_goals1
                                                                     in
                                                                    let uu____5395
                                                                    =
                                                                    let uu____5398
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    goal  in
                                                                    proc_guard
                                                                    "apply_lemma guard"
                                                                    uu____5398
                                                                    guard  in
                                                                    bind
                                                                    uu____5395
                                                                    (fun
                                                                    uu____5401
                                                                     ->
                                                                    let uu____5402
                                                                    =
                                                                    let uu____5405
                                                                    =
                                                                    let uu____5406
                                                                    =
                                                                    let uu____5407
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    goal  in
                                                                    let uu____5408
                                                                    =
                                                                    FStar_Syntax_Util.mk_squash
                                                                    FStar_Syntax_Syntax.U_zero
                                                                    pre1  in
                                                                    istrivial
                                                                    uu____5407
                                                                    uu____5408
                                                                     in
                                                                    Prims.op_Negation
                                                                    uu____5406
                                                                     in
                                                                    if
                                                                    uu____5405
                                                                    then
                                                                    let uu____5411
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    goal  in
                                                                    add_irrelevant_goal
                                                                    "apply_lemma precondition"
                                                                    uu____5411
                                                                    pre1
                                                                    goal.FStar_Tactics_Types.opts
                                                                    else
                                                                    ret ()
                                                                     in
                                                                    bind
                                                                    uu____5402
                                                                    (fun
                                                                    uu____5414
                                                                     ->
                                                                    add_goals
                                                                    sub_goals2))))))))))))))
         in
      focus uu____4553  in
    FStar_All.pipe_left (wrap_err "apply_lemma") uu____4550
  
let (destruct_eq' :
  FStar_Reflection_Data.typ ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun typ  ->
    let uu____5436 = FStar_Syntax_Util.destruct_typ_as_formula typ  in
    match uu____5436 with
    | FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn
        (l,uu____5446::(e1,uu____5448)::(e2,uu____5450)::[])) when
        FStar_Ident.lid_equals l FStar_Parser_Const.eq2_lid ->
        FStar_Pervasives_Native.Some (e1, e2)
    | uu____5511 -> FStar_Pervasives_Native.None
  
let (destruct_eq :
  FStar_Reflection_Data.typ ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun typ  ->
    let uu____5535 = destruct_eq' typ  in
    match uu____5535 with
    | FStar_Pervasives_Native.Some t -> FStar_Pervasives_Native.Some t
    | FStar_Pervasives_Native.None  ->
        let uu____5565 = FStar_Syntax_Util.un_squash typ  in
        (match uu____5565 with
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
        let uu____5627 = FStar_TypeChecker_Env.pop_bv e1  in
        match uu____5627 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (bv',e') ->
            if FStar_Syntax_Syntax.bv_eq bvar bv'
            then FStar_Pervasives_Native.Some (e', [])
            else
              (let uu____5675 = aux e'  in
               FStar_Util.map_opt uu____5675
                 (fun uu____5699  ->
                    match uu____5699 with | (e'',bvs) -> (e'', (bv' :: bvs))))
         in
      let uu____5720 = aux e  in
      FStar_Util.map_opt uu____5720
        (fun uu____5744  ->
           match uu____5744 with | (e',bvs) -> (e', (FStar_List.rev bvs)))
  
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
          let uu____5811 =
            let uu____5820 = FStar_Tactics_Types.goal_env g  in
            split_env b1 uu____5820  in
          FStar_Util.map_opt uu____5811
            (fun uu____5835  ->
               match uu____5835 with
               | (e0,bvs) ->
                   let s1 bv =
                     let uu___391_5854 = bv  in
                     let uu____5855 =
                       FStar_Syntax_Subst.subst s bv.FStar_Syntax_Syntax.sort
                        in
                     {
                       FStar_Syntax_Syntax.ppname =
                         (uu___391_5854.FStar_Syntax_Syntax.ppname);
                       FStar_Syntax_Syntax.index =
                         (uu___391_5854.FStar_Syntax_Syntax.index);
                       FStar_Syntax_Syntax.sort = uu____5855
                     }  in
                   let bvs1 = FStar_List.map s1 bvs  in
                   let new_env = push_bvs e0 (b2 :: bvs1)  in
                   let new_goal =
                     let uu___392_5863 = g.FStar_Tactics_Types.goal_ctx_uvar
                        in
                     let uu____5864 =
                       FStar_TypeChecker_Env.all_binders new_env  in
                     let uu____5873 =
                       let uu____5876 = FStar_Tactics_Types.goal_type g  in
                       FStar_Syntax_Subst.subst s uu____5876  in
                     {
                       FStar_Syntax_Syntax.ctx_uvar_head =
                         (uu___392_5863.FStar_Syntax_Syntax.ctx_uvar_head);
                       FStar_Syntax_Syntax.ctx_uvar_gamma =
                         (new_env.FStar_TypeChecker_Env.gamma);
                       FStar_Syntax_Syntax.ctx_uvar_binders = uu____5864;
                       FStar_Syntax_Syntax.ctx_uvar_typ = uu____5873;
                       FStar_Syntax_Syntax.ctx_uvar_reason =
                         (uu___392_5863.FStar_Syntax_Syntax.ctx_uvar_reason);
                       FStar_Syntax_Syntax.ctx_uvar_should_check =
                         (uu___392_5863.FStar_Syntax_Syntax.ctx_uvar_should_check);
                       FStar_Syntax_Syntax.ctx_uvar_range =
                         (uu___392_5863.FStar_Syntax_Syntax.ctx_uvar_range)
                     }  in
                   let uu___393_5877 = g  in
                   {
                     FStar_Tactics_Types.goal_main_env =
                       (uu___393_5877.FStar_Tactics_Types.goal_main_env);
                     FStar_Tactics_Types.goal_ctx_uvar = new_goal;
                     FStar_Tactics_Types.opts =
                       (uu___393_5877.FStar_Tactics_Types.opts);
                     FStar_Tactics_Types.is_guard =
                       (uu___393_5877.FStar_Tactics_Types.is_guard)
                   })
  
let (rewrite : FStar_Syntax_Syntax.binder -> unit tac) =
  fun h  ->
    let uu____5887 =
      let uu____5890 = cur_goal ()  in
      bind uu____5890
        (fun goal  ->
           let uu____5898 = h  in
           match uu____5898 with
           | (bv,uu____5902) ->
               mlog
                 (fun uu____5910  ->
                    let uu____5911 = FStar_Syntax_Print.bv_to_string bv  in
                    let uu____5912 =
                      FStar_Syntax_Print.term_to_string
                        bv.FStar_Syntax_Syntax.sort
                       in
                    FStar_Util.print2 "+++Rewrite %s : %s\n" uu____5911
                      uu____5912)
                 (fun uu____5915  ->
                    let uu____5916 =
                      let uu____5925 = FStar_Tactics_Types.goal_env goal  in
                      split_env bv uu____5925  in
                    match uu____5916 with
                    | FStar_Pervasives_Native.None  ->
                        fail "binder not found in environment"
                    | FStar_Pervasives_Native.Some (e0,bvs) ->
                        let uu____5946 =
                          destruct_eq bv.FStar_Syntax_Syntax.sort  in
                        (match uu____5946 with
                         | FStar_Pervasives_Native.Some (x,e) ->
                             let uu____5961 =
                               let uu____5962 = FStar_Syntax_Subst.compress x
                                  in
                               uu____5962.FStar_Syntax_Syntax.n  in
                             (match uu____5961 with
                              | FStar_Syntax_Syntax.Tm_name x1 ->
                                  let s = [FStar_Syntax_Syntax.NT (x1, e)]
                                     in
                                  let s1 bv1 =
                                    let uu___394_5979 = bv1  in
                                    let uu____5980 =
                                      FStar_Syntax_Subst.subst s
                                        bv1.FStar_Syntax_Syntax.sort
                                       in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___394_5979.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___394_5979.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = uu____5980
                                    }  in
                                  let bvs1 = FStar_List.map s1 bvs  in
                                  let new_env = push_bvs e0 (bv :: bvs1)  in
                                  let new_goal =
                                    let uu___395_5988 =
                                      goal.FStar_Tactics_Types.goal_ctx_uvar
                                       in
                                    let uu____5989 =
                                      FStar_TypeChecker_Env.all_binders
                                        new_env
                                       in
                                    let uu____5998 =
                                      let uu____6001 =
                                        FStar_Tactics_Types.goal_type goal
                                         in
                                      FStar_Syntax_Subst.subst s uu____6001
                                       in
                                    {
                                      FStar_Syntax_Syntax.ctx_uvar_head =
                                        (uu___395_5988.FStar_Syntax_Syntax.ctx_uvar_head);
                                      FStar_Syntax_Syntax.ctx_uvar_gamma =
                                        (new_env.FStar_TypeChecker_Env.gamma);
                                      FStar_Syntax_Syntax.ctx_uvar_binders =
                                        uu____5989;
                                      FStar_Syntax_Syntax.ctx_uvar_typ =
                                        uu____5998;
                                      FStar_Syntax_Syntax.ctx_uvar_reason =
                                        (uu___395_5988.FStar_Syntax_Syntax.ctx_uvar_reason);
                                      FStar_Syntax_Syntax.ctx_uvar_should_check
                                        =
                                        (uu___395_5988.FStar_Syntax_Syntax.ctx_uvar_should_check);
                                      FStar_Syntax_Syntax.ctx_uvar_range =
                                        (uu___395_5988.FStar_Syntax_Syntax.ctx_uvar_range)
                                    }  in
                                  replace_cur
                                    (let uu___396_6004 = goal  in
                                     {
                                       FStar_Tactics_Types.goal_main_env =
                                         (uu___396_6004.FStar_Tactics_Types.goal_main_env);
                                       FStar_Tactics_Types.goal_ctx_uvar =
                                         new_goal;
                                       FStar_Tactics_Types.opts =
                                         (uu___396_6004.FStar_Tactics_Types.opts);
                                       FStar_Tactics_Types.is_guard =
                                         (uu___396_6004.FStar_Tactics_Types.is_guard)
                                     })
                              | uu____6005 ->
                                  fail
                                    "Not an equality hypothesis with a variable on the LHS")
                         | uu____6006 -> fail "Not an equality hypothesis")))
       in
    FStar_All.pipe_left (wrap_err "rewrite") uu____5887
  
let (rename_to : FStar_Syntax_Syntax.binder -> Prims.string -> unit tac) =
  fun b  ->
    fun s  ->
      let uu____6031 =
        let uu____6034 = cur_goal ()  in
        bind uu____6034
          (fun goal  ->
             let uu____6045 = b  in
             match uu____6045 with
             | (bv,uu____6049) ->
                 let bv' =
                   let uu____6055 =
                     let uu___397_6056 = bv  in
                     let uu____6057 =
                       FStar_Ident.mk_ident
                         (s,
                           ((bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange))
                        in
                     {
                       FStar_Syntax_Syntax.ppname = uu____6057;
                       FStar_Syntax_Syntax.index =
                         (uu___397_6056.FStar_Syntax_Syntax.index);
                       FStar_Syntax_Syntax.sort =
                         (uu___397_6056.FStar_Syntax_Syntax.sort)
                     }  in
                   FStar_Syntax_Syntax.freshen_bv uu____6055  in
                 let s1 =
                   let uu____6061 =
                     let uu____6062 =
                       let uu____6069 = FStar_Syntax_Syntax.bv_to_name bv'
                          in
                       (bv, uu____6069)  in
                     FStar_Syntax_Syntax.NT uu____6062  in
                   [uu____6061]  in
                 let uu____6074 = subst_goal bv bv' s1 goal  in
                 (match uu____6074 with
                  | FStar_Pervasives_Native.None  ->
                      fail "binder not found in environment"
                  | FStar_Pervasives_Native.Some goal1 -> replace_cur goal1))
         in
      FStar_All.pipe_left (wrap_err "rename_to") uu____6031
  
let (binder_retype : FStar_Syntax_Syntax.binder -> unit tac) =
  fun b  ->
    let uu____6093 =
      let uu____6096 = cur_goal ()  in
      bind uu____6096
        (fun goal  ->
           let uu____6105 = b  in
           match uu____6105 with
           | (bv,uu____6109) ->
               let uu____6114 =
                 let uu____6123 = FStar_Tactics_Types.goal_env goal  in
                 split_env bv uu____6123  in
               (match uu____6114 with
                | FStar_Pervasives_Native.None  ->
                    fail "binder is not present in environment"
                | FStar_Pervasives_Native.Some (e0,bvs) ->
                    let uu____6144 = FStar_Syntax_Util.type_u ()  in
                    (match uu____6144 with
                     | (ty,u) ->
                         let uu____6153 = new_uvar "binder_retype" e0 ty  in
                         bind uu____6153
                           (fun uu____6171  ->
                              match uu____6171 with
                              | (t',u_t') ->
                                  let bv'' =
                                    let uu___398_6181 = bv  in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___398_6181.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___398_6181.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = t'
                                    }  in
                                  let s =
                                    let uu____6185 =
                                      let uu____6186 =
                                        let uu____6193 =
                                          FStar_Syntax_Syntax.bv_to_name bv''
                                           in
                                        (bv, uu____6193)  in
                                      FStar_Syntax_Syntax.NT uu____6186  in
                                    [uu____6185]  in
                                  let bvs1 =
                                    FStar_List.map
                                      (fun b1  ->
                                         let uu___399_6205 = b1  in
                                         let uu____6206 =
                                           FStar_Syntax_Subst.subst s
                                             b1.FStar_Syntax_Syntax.sort
                                            in
                                         {
                                           FStar_Syntax_Syntax.ppname =
                                             (uu___399_6205.FStar_Syntax_Syntax.ppname);
                                           FStar_Syntax_Syntax.index =
                                             (uu___399_6205.FStar_Syntax_Syntax.index);
                                           FStar_Syntax_Syntax.sort =
                                             uu____6206
                                         }) bvs
                                     in
                                  let env' = push_bvs e0 (bv'' :: bvs1)  in
                                  bind __dismiss
                                    (fun uu____6213  ->
                                       let new_goal =
                                         let uu____6215 =
                                           FStar_Tactics_Types.goal_with_env
                                             goal env'
                                            in
                                         let uu____6216 =
                                           let uu____6217 =
                                             FStar_Tactics_Types.goal_type
                                               goal
                                              in
                                           FStar_Syntax_Subst.subst s
                                             uu____6217
                                            in
                                         FStar_Tactics_Types.goal_with_type
                                           uu____6215 uu____6216
                                          in
                                       let uu____6218 = add_goals [new_goal]
                                          in
                                       bind uu____6218
                                         (fun uu____6223  ->
                                            let uu____6224 =
                                              FStar_Syntax_Util.mk_eq2
                                                (FStar_Syntax_Syntax.U_succ u)
                                                ty
                                                bv.FStar_Syntax_Syntax.sort
                                                t'
                                               in
                                            add_irrelevant_goal
                                              "binder_retype equation" e0
                                              uu____6224
                                              goal.FStar_Tactics_Types.opts))))))
       in
    FStar_All.pipe_left (wrap_err "binder_retype") uu____6093
  
let (norm_binder_type :
  FStar_Syntax_Embeddings.norm_step Prims.list ->
    FStar_Syntax_Syntax.binder -> unit tac)
  =
  fun s  ->
    fun b  ->
      let uu____6247 =
        let uu____6250 = cur_goal ()  in
        bind uu____6250
          (fun goal  ->
             let uu____6259 = b  in
             match uu____6259 with
             | (bv,uu____6263) ->
                 let uu____6268 =
                   let uu____6277 = FStar_Tactics_Types.goal_env goal  in
                   split_env bv uu____6277  in
                 (match uu____6268 with
                  | FStar_Pervasives_Native.None  ->
                      fail "binder is not present in environment"
                  | FStar_Pervasives_Native.Some (e0,bvs) ->
                      let steps =
                        let uu____6301 =
                          FStar_TypeChecker_Normalize.tr_norm_steps s  in
                        FStar_List.append
                          [FStar_TypeChecker_Env.Reify;
                          FStar_TypeChecker_Env.UnfoldTac] uu____6301
                         in
                      let sort' =
                        normalize steps e0 bv.FStar_Syntax_Syntax.sort  in
                      let bv' =
                        let uu___400_6306 = bv  in
                        {
                          FStar_Syntax_Syntax.ppname =
                            (uu___400_6306.FStar_Syntax_Syntax.ppname);
                          FStar_Syntax_Syntax.index =
                            (uu___400_6306.FStar_Syntax_Syntax.index);
                          FStar_Syntax_Syntax.sort = sort'
                        }  in
                      let env' = push_bvs e0 (bv' :: bvs)  in
                      let uu____6308 =
                        FStar_Tactics_Types.goal_with_env goal env'  in
                      replace_cur uu____6308))
         in
      FStar_All.pipe_left (wrap_err "norm_binder_type") uu____6247
  
let (revert : unit -> unit tac) =
  fun uu____6319  ->
    let uu____6322 = cur_goal ()  in
    bind uu____6322
      (fun goal  ->
         let uu____6328 =
           let uu____6335 = FStar_Tactics_Types.goal_env goal  in
           FStar_TypeChecker_Env.pop_bv uu____6335  in
         match uu____6328 with
         | FStar_Pervasives_Native.None  ->
             fail "Cannot revert; empty context"
         | FStar_Pervasives_Native.Some (x,env') ->
             let typ' =
               let uu____6351 =
                 let uu____6354 = FStar_Tactics_Types.goal_type goal  in
                 FStar_Syntax_Syntax.mk_Total uu____6354  in
               FStar_Syntax_Util.arrow [(x, FStar_Pervasives_Native.None)]
                 uu____6351
                in
             let uu____6369 = new_uvar "revert" env' typ'  in
             bind uu____6369
               (fun uu____6384  ->
                  match uu____6384 with
                  | (r,u_r) ->
                      let uu____6393 =
                        let uu____6396 =
                          let uu____6397 =
                            let uu____6398 =
                              FStar_Tactics_Types.goal_type goal  in
                            uu____6398.FStar_Syntax_Syntax.pos  in
                          let uu____6401 =
                            let uu____6406 =
                              let uu____6407 =
                                let uu____6416 =
                                  FStar_Syntax_Syntax.bv_to_name x  in
                                FStar_Syntax_Syntax.as_arg uu____6416  in
                              [uu____6407]  in
                            FStar_Syntax_Syntax.mk_Tm_app r uu____6406  in
                          uu____6401 FStar_Pervasives_Native.None uu____6397
                           in
                        set_solution goal uu____6396  in
                      bind uu____6393
                        (fun uu____6437  ->
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
      let uu____6449 = FStar_Syntax_Free.names t  in
      FStar_Util.set_mem bv uu____6449
  
let rec (clear : FStar_Syntax_Syntax.binder -> unit tac) =
  fun b  ->
    let bv = FStar_Pervasives_Native.fst b  in
    let uu____6464 = cur_goal ()  in
    bind uu____6464
      (fun goal  ->
         mlog
           (fun uu____6472  ->
              let uu____6473 = FStar_Syntax_Print.binder_to_string b  in
              let uu____6474 =
                let uu____6475 =
                  let uu____6476 =
                    let uu____6485 = FStar_Tactics_Types.goal_env goal  in
                    FStar_TypeChecker_Env.all_binders uu____6485  in
                  FStar_All.pipe_right uu____6476 FStar_List.length  in
                FStar_All.pipe_right uu____6475 FStar_Util.string_of_int  in
              FStar_Util.print2 "Clear of (%s), env has %s binders\n"
                uu____6473 uu____6474)
           (fun uu____6502  ->
              let uu____6503 =
                let uu____6512 = FStar_Tactics_Types.goal_env goal  in
                split_env bv uu____6512  in
              match uu____6503 with
              | FStar_Pervasives_Native.None  ->
                  fail "Cannot clear; binder not in environment"
              | FStar_Pervasives_Native.Some (e',bvs) ->
                  let rec check1 bvs1 =
                    match bvs1 with
                    | [] -> ret ()
                    | bv'::bvs2 ->
                        let uu____6551 =
                          free_in bv bv'.FStar_Syntax_Syntax.sort  in
                        if uu____6551
                        then
                          let uu____6554 =
                            let uu____6555 =
                              FStar_Syntax_Print.bv_to_string bv'  in
                            FStar_Util.format1
                              "Cannot clear; binder present in the type of %s"
                              uu____6555
                             in
                          fail uu____6554
                        else check1 bvs2
                     in
                  let uu____6557 =
                    let uu____6558 = FStar_Tactics_Types.goal_type goal  in
                    free_in bv uu____6558  in
                  if uu____6557
                  then fail "Cannot clear; binder present in goal"
                  else
                    (let uu____6562 = check1 bvs  in
                     bind uu____6562
                       (fun uu____6568  ->
                          let env' = push_bvs e' bvs  in
                          let uu____6570 =
                            let uu____6577 =
                              FStar_Tactics_Types.goal_type goal  in
                            new_uvar "clear.witness" env' uu____6577  in
                          bind uu____6570
                            (fun uu____6586  ->
                               match uu____6586 with
                               | (ut,uvar_ut) ->
                                   let uu____6595 = set_solution goal ut  in
                                   bind uu____6595
                                     (fun uu____6600  ->
                                        let uu____6601 =
                                          FStar_Tactics_Types.mk_goal env'
                                            uvar_ut
                                            goal.FStar_Tactics_Types.opts
                                            goal.FStar_Tactics_Types.is_guard
                                           in
                                        replace_cur uu____6601))))))
  
let (clear_top : unit -> unit tac) =
  fun uu____6608  ->
    let uu____6611 = cur_goal ()  in
    bind uu____6611
      (fun goal  ->
         let uu____6617 =
           let uu____6624 = FStar_Tactics_Types.goal_env goal  in
           FStar_TypeChecker_Env.pop_bv uu____6624  in
         match uu____6617 with
         | FStar_Pervasives_Native.None  ->
             fail "Cannot clear; empty context"
         | FStar_Pervasives_Native.Some (x,uu____6632) ->
             let uu____6637 = FStar_Syntax_Syntax.mk_binder x  in
             clear uu____6637)
  
let (prune : Prims.string -> unit tac) =
  fun s  ->
    let uu____6647 = cur_goal ()  in
    bind uu____6647
      (fun g  ->
         let ctx = FStar_Tactics_Types.goal_env g  in
         let ctx' =
           let uu____6657 = FStar_Ident.path_of_text s  in
           FStar_TypeChecker_Env.rem_proof_ns ctx uu____6657  in
         let g' = FStar_Tactics_Types.goal_with_env g ctx'  in
         bind __dismiss (fun uu____6660  -> add_goals [g']))
  
let (addns : Prims.string -> unit tac) =
  fun s  ->
    let uu____6670 = cur_goal ()  in
    bind uu____6670
      (fun g  ->
         let ctx = FStar_Tactics_Types.goal_env g  in
         let ctx' =
           let uu____6680 = FStar_Ident.path_of_text s  in
           FStar_TypeChecker_Env.add_proof_ns ctx uu____6680  in
         let g' = FStar_Tactics_Types.goal_with_env g ctx'  in
         bind __dismiss (fun uu____6683  -> add_goals [g']))
  
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
            let uu____6723 = FStar_Syntax_Subst.compress t  in
            uu____6723.FStar_Syntax_Syntax.n  in
          let uu____6726 =
            if d = FStar_Tactics_Types.TopDown
            then
              f env
                (let uu___404_6732 = t  in
                 {
                   FStar_Syntax_Syntax.n = tn;
                   FStar_Syntax_Syntax.pos =
                     (uu___404_6732.FStar_Syntax_Syntax.pos);
                   FStar_Syntax_Syntax.vars =
                     (uu___404_6732.FStar_Syntax_Syntax.vars)
                 })
            else ret t  in
          bind uu____6726
            (fun t1  ->
               let ff = tac_fold_env d f env  in
               let tn1 =
                 let uu____6748 =
                   let uu____6749 = FStar_Syntax_Subst.compress t1  in
                   uu____6749.FStar_Syntax_Syntax.n  in
                 match uu____6748 with
                 | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
                     let uu____6780 = ff hd1  in
                     bind uu____6780
                       (fun hd2  ->
                          let fa uu____6806 =
                            match uu____6806 with
                            | (a,q) ->
                                let uu____6827 = ff a  in
                                bind uu____6827 (fun a1  -> ret (a1, q))
                             in
                          let uu____6846 = mapM fa args  in
                          bind uu____6846
                            (fun args1  ->
                               ret (FStar_Syntax_Syntax.Tm_app (hd2, args1))))
                 | FStar_Syntax_Syntax.Tm_abs (bs,t2,k) ->
                     let uu____6928 = FStar_Syntax_Subst.open_term bs t2  in
                     (match uu____6928 with
                      | (bs1,t') ->
                          let uu____6937 =
                            let uu____6940 =
                              FStar_TypeChecker_Env.push_binders env bs1  in
                            tac_fold_env d f uu____6940 t'  in
                          bind uu____6937
                            (fun t''  ->
                               let uu____6944 =
                                 let uu____6945 =
                                   let uu____6964 =
                                     FStar_Syntax_Subst.close_binders bs1  in
                                   let uu____6973 =
                                     FStar_Syntax_Subst.close bs1 t''  in
                                   (uu____6964, uu____6973, k)  in
                                 FStar_Syntax_Syntax.Tm_abs uu____6945  in
                               ret uu____6944))
                 | FStar_Syntax_Syntax.Tm_arrow (bs,k) -> ret tn
                 | FStar_Syntax_Syntax.Tm_match (hd1,brs) ->
                     let uu____7048 = ff hd1  in
                     bind uu____7048
                       (fun hd2  ->
                          let ffb br =
                            let uu____7063 =
                              FStar_Syntax_Subst.open_branch br  in
                            match uu____7063 with
                            | (pat,w,e) ->
                                let bvs = FStar_Syntax_Syntax.pat_bvs pat  in
                                let ff1 =
                                  let uu____7095 =
                                    FStar_TypeChecker_Env.push_bvs env bvs
                                     in
                                  tac_fold_env d f uu____7095  in
                                let uu____7096 = ff1 e  in
                                bind uu____7096
                                  (fun e1  ->
                                     let br1 =
                                       FStar_Syntax_Subst.close_branch
                                         (pat, w, e1)
                                        in
                                     ret br1)
                             in
                          let uu____7111 = mapM ffb brs  in
                          bind uu____7111
                            (fun brs1  ->
                               ret (FStar_Syntax_Syntax.Tm_match (hd2, brs1))))
                 | FStar_Syntax_Syntax.Tm_let
                     ((false
                       ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inl bv;
                          FStar_Syntax_Syntax.lbunivs = uu____7155;
                          FStar_Syntax_Syntax.lbtyp = uu____7156;
                          FStar_Syntax_Syntax.lbeff = uu____7157;
                          FStar_Syntax_Syntax.lbdef = def;
                          FStar_Syntax_Syntax.lbattrs = uu____7159;
                          FStar_Syntax_Syntax.lbpos = uu____7160;_}::[]),e)
                     ->
                     let lb =
                       let uu____7185 =
                         let uu____7186 = FStar_Syntax_Subst.compress t1  in
                         uu____7186.FStar_Syntax_Syntax.n  in
                       match uu____7185 with
                       | FStar_Syntax_Syntax.Tm_let
                           ((false ,lb::[]),uu____7190) -> lb
                       | uu____7203 -> failwith "impossible"  in
                     let fflb lb1 =
                       let uu____7212 = ff lb1.FStar_Syntax_Syntax.lbdef  in
                       bind uu____7212
                         (fun def1  ->
                            ret
                              (let uu___401_7218 = lb1  in
                               {
                                 FStar_Syntax_Syntax.lbname =
                                   (uu___401_7218.FStar_Syntax_Syntax.lbname);
                                 FStar_Syntax_Syntax.lbunivs =
                                   (uu___401_7218.FStar_Syntax_Syntax.lbunivs);
                                 FStar_Syntax_Syntax.lbtyp =
                                   (uu___401_7218.FStar_Syntax_Syntax.lbtyp);
                                 FStar_Syntax_Syntax.lbeff =
                                   (uu___401_7218.FStar_Syntax_Syntax.lbeff);
                                 FStar_Syntax_Syntax.lbdef = def1;
                                 FStar_Syntax_Syntax.lbattrs =
                                   (uu___401_7218.FStar_Syntax_Syntax.lbattrs);
                                 FStar_Syntax_Syntax.lbpos =
                                   (uu___401_7218.FStar_Syntax_Syntax.lbpos)
                               }))
                        in
                     let uu____7219 = fflb lb  in
                     bind uu____7219
                       (fun lb1  ->
                          let uu____7229 =
                            let uu____7234 =
                              let uu____7235 =
                                FStar_Syntax_Syntax.mk_binder bv  in
                              [uu____7235]  in
                            FStar_Syntax_Subst.open_term uu____7234 e  in
                          match uu____7229 with
                          | (bs,e1) ->
                              let ff1 =
                                let uu____7265 =
                                  FStar_TypeChecker_Env.push_binders env bs
                                   in
                                tac_fold_env d f uu____7265  in
                              let uu____7266 = ff1 e1  in
                              bind uu____7266
                                (fun e2  ->
                                   let e3 = FStar_Syntax_Subst.close bs e2
                                      in
                                   ret
                                     (FStar_Syntax_Syntax.Tm_let
                                        ((false, [lb1]), e3))))
                 | FStar_Syntax_Syntax.Tm_let ((true ,lbs),e) ->
                     let fflb lb =
                       let uu____7307 = ff lb.FStar_Syntax_Syntax.lbdef  in
                       bind uu____7307
                         (fun def  ->
                            ret
                              (let uu___402_7313 = lb  in
                               {
                                 FStar_Syntax_Syntax.lbname =
                                   (uu___402_7313.FStar_Syntax_Syntax.lbname);
                                 FStar_Syntax_Syntax.lbunivs =
                                   (uu___402_7313.FStar_Syntax_Syntax.lbunivs);
                                 FStar_Syntax_Syntax.lbtyp =
                                   (uu___402_7313.FStar_Syntax_Syntax.lbtyp);
                                 FStar_Syntax_Syntax.lbeff =
                                   (uu___402_7313.FStar_Syntax_Syntax.lbeff);
                                 FStar_Syntax_Syntax.lbdef = def;
                                 FStar_Syntax_Syntax.lbattrs =
                                   (uu___402_7313.FStar_Syntax_Syntax.lbattrs);
                                 FStar_Syntax_Syntax.lbpos =
                                   (uu___402_7313.FStar_Syntax_Syntax.lbpos)
                               }))
                        in
                     let uu____7314 = FStar_Syntax_Subst.open_let_rec lbs e
                        in
                     (match uu____7314 with
                      | (lbs1,e1) ->
                          let uu____7329 = mapM fflb lbs1  in
                          bind uu____7329
                            (fun lbs2  ->
                               let uu____7341 = ff e1  in
                               bind uu____7341
                                 (fun e2  ->
                                    let uu____7349 =
                                      FStar_Syntax_Subst.close_let_rec lbs2
                                        e2
                                       in
                                    match uu____7349 with
                                    | (lbs3,e3) ->
                                        ret
                                          (FStar_Syntax_Syntax.Tm_let
                                             ((true, lbs3), e3)))))
                 | FStar_Syntax_Syntax.Tm_ascribed (t2,asc,eff) ->
                     let uu____7417 = ff t2  in
                     bind uu____7417
                       (fun t3  ->
                          ret
                            (FStar_Syntax_Syntax.Tm_ascribed (t3, asc, eff)))
                 | FStar_Syntax_Syntax.Tm_meta (t2,m) ->
                     let uu____7448 = ff t2  in
                     bind uu____7448
                       (fun t3  -> ret (FStar_Syntax_Syntax.Tm_meta (t3, m)))
                 | uu____7455 -> ret tn  in
               bind tn1
                 (fun tn2  ->
                    let t' =
                      let uu___403_7462 = t1  in
                      {
                        FStar_Syntax_Syntax.n = tn2;
                        FStar_Syntax_Syntax.pos =
                          (uu___403_7462.FStar_Syntax_Syntax.pos);
                        FStar_Syntax_Syntax.vars =
                          (uu___403_7462.FStar_Syntax_Syntax.vars)
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
            let uu____7499 =
              FStar_TypeChecker_TcTerm.tc_term
                (let uu___405_7508 = env  in
                 {
                   FStar_TypeChecker_Env.solver =
                     (uu___405_7508.FStar_TypeChecker_Env.solver);
                   FStar_TypeChecker_Env.range =
                     (uu___405_7508.FStar_TypeChecker_Env.range);
                   FStar_TypeChecker_Env.curmodule =
                     (uu___405_7508.FStar_TypeChecker_Env.curmodule);
                   FStar_TypeChecker_Env.gamma =
                     (uu___405_7508.FStar_TypeChecker_Env.gamma);
                   FStar_TypeChecker_Env.gamma_sig =
                     (uu___405_7508.FStar_TypeChecker_Env.gamma_sig);
                   FStar_TypeChecker_Env.gamma_cache =
                     (uu___405_7508.FStar_TypeChecker_Env.gamma_cache);
                   FStar_TypeChecker_Env.modules =
                     (uu___405_7508.FStar_TypeChecker_Env.modules);
                   FStar_TypeChecker_Env.expected_typ =
                     (uu___405_7508.FStar_TypeChecker_Env.expected_typ);
                   FStar_TypeChecker_Env.sigtab =
                     (uu___405_7508.FStar_TypeChecker_Env.sigtab);
                   FStar_TypeChecker_Env.attrtab =
                     (uu___405_7508.FStar_TypeChecker_Env.attrtab);
                   FStar_TypeChecker_Env.is_pattern =
                     (uu___405_7508.FStar_TypeChecker_Env.is_pattern);
                   FStar_TypeChecker_Env.instantiate_imp =
                     (uu___405_7508.FStar_TypeChecker_Env.instantiate_imp);
                   FStar_TypeChecker_Env.effects =
                     (uu___405_7508.FStar_TypeChecker_Env.effects);
                   FStar_TypeChecker_Env.generalize =
                     (uu___405_7508.FStar_TypeChecker_Env.generalize);
                   FStar_TypeChecker_Env.letrecs =
                     (uu___405_7508.FStar_TypeChecker_Env.letrecs);
                   FStar_TypeChecker_Env.top_level =
                     (uu___405_7508.FStar_TypeChecker_Env.top_level);
                   FStar_TypeChecker_Env.check_uvars =
                     (uu___405_7508.FStar_TypeChecker_Env.check_uvars);
                   FStar_TypeChecker_Env.use_eq =
                     (uu___405_7508.FStar_TypeChecker_Env.use_eq);
                   FStar_TypeChecker_Env.is_iface =
                     (uu___405_7508.FStar_TypeChecker_Env.is_iface);
                   FStar_TypeChecker_Env.admit =
                     (uu___405_7508.FStar_TypeChecker_Env.admit);
                   FStar_TypeChecker_Env.lax = true;
                   FStar_TypeChecker_Env.lax_universes =
                     (uu___405_7508.FStar_TypeChecker_Env.lax_universes);
                   FStar_TypeChecker_Env.phase1 =
                     (uu___405_7508.FStar_TypeChecker_Env.phase1);
                   FStar_TypeChecker_Env.failhard =
                     (uu___405_7508.FStar_TypeChecker_Env.failhard);
                   FStar_TypeChecker_Env.nosynth =
                     (uu___405_7508.FStar_TypeChecker_Env.nosynth);
                   FStar_TypeChecker_Env.uvar_subtyping =
                     (uu___405_7508.FStar_TypeChecker_Env.uvar_subtyping);
                   FStar_TypeChecker_Env.tc_term =
                     (uu___405_7508.FStar_TypeChecker_Env.tc_term);
                   FStar_TypeChecker_Env.type_of =
                     (uu___405_7508.FStar_TypeChecker_Env.type_of);
                   FStar_TypeChecker_Env.universe_of =
                     (uu___405_7508.FStar_TypeChecker_Env.universe_of);
                   FStar_TypeChecker_Env.check_type_of =
                     (uu___405_7508.FStar_TypeChecker_Env.check_type_of);
                   FStar_TypeChecker_Env.use_bv_sorts =
                     (uu___405_7508.FStar_TypeChecker_Env.use_bv_sorts);
                   FStar_TypeChecker_Env.qtbl_name_and_index =
                     (uu___405_7508.FStar_TypeChecker_Env.qtbl_name_and_index);
                   FStar_TypeChecker_Env.normalized_eff_names =
                     (uu___405_7508.FStar_TypeChecker_Env.normalized_eff_names);
                   FStar_TypeChecker_Env.proof_ns =
                     (uu___405_7508.FStar_TypeChecker_Env.proof_ns);
                   FStar_TypeChecker_Env.synth_hook =
                     (uu___405_7508.FStar_TypeChecker_Env.synth_hook);
                   FStar_TypeChecker_Env.splice =
                     (uu___405_7508.FStar_TypeChecker_Env.splice);
                   FStar_TypeChecker_Env.is_native_tactic =
                     (uu___405_7508.FStar_TypeChecker_Env.is_native_tactic);
                   FStar_TypeChecker_Env.identifier_info =
                     (uu___405_7508.FStar_TypeChecker_Env.identifier_info);
                   FStar_TypeChecker_Env.tc_hooks =
                     (uu___405_7508.FStar_TypeChecker_Env.tc_hooks);
                   FStar_TypeChecker_Env.dsenv =
                     (uu___405_7508.FStar_TypeChecker_Env.dsenv);
                   FStar_TypeChecker_Env.dep_graph =
                     (uu___405_7508.FStar_TypeChecker_Env.dep_graph);
                   FStar_TypeChecker_Env.nbe =
                     (uu___405_7508.FStar_TypeChecker_Env.nbe)
                 }) t
               in
            match uu____7499 with
            | (t1,lcomp,g) ->
                let uu____7514 =
                  (let uu____7517 =
                     FStar_Syntax_Util.is_pure_or_ghost_lcomp lcomp  in
                   Prims.op_Negation uu____7517) ||
                    (let uu____7519 = FStar_TypeChecker_Env.is_trivial g  in
                     Prims.op_Negation uu____7519)
                   in
                if uu____7514
                then ret t1
                else
                  (let rewrite_eq =
                     let typ = lcomp.FStar_Syntax_Syntax.res_typ  in
                     let uu____7527 = new_uvar "pointwise_rec" env typ  in
                     bind uu____7527
                       (fun uu____7543  ->
                          match uu____7543 with
                          | (ut,uvar_ut) ->
                              (log ps
                                 (fun uu____7556  ->
                                    let uu____7557 =
                                      FStar_Syntax_Print.term_to_string t1
                                       in
                                    let uu____7558 =
                                      FStar_Syntax_Print.term_to_string ut
                                       in
                                    FStar_Util.print2
                                      "Pointwise_rec: making equality\n\t%s ==\n\t%s\n"
                                      uu____7557 uu____7558);
                               (let uu____7559 =
                                  let uu____7562 =
                                    let uu____7563 =
                                      FStar_TypeChecker_TcTerm.universe_of
                                        env typ
                                       in
                                    FStar_Syntax_Util.mk_eq2 uu____7563 typ
                                      t1 ut
                                     in
                                  add_irrelevant_goal
                                    "pointwise_rec equation" env uu____7562
                                    opts
                                   in
                                bind uu____7559
                                  (fun uu____7566  ->
                                     let uu____7567 =
                                       bind tau
                                         (fun uu____7573  ->
                                            let ut1 =
                                              FStar_TypeChecker_Normalize.reduce_uvar_solutions
                                                env ut
                                               in
                                            log ps
                                              (fun uu____7579  ->
                                                 let uu____7580 =
                                                   FStar_Syntax_Print.term_to_string
                                                     t1
                                                    in
                                                 let uu____7581 =
                                                   FStar_Syntax_Print.term_to_string
                                                     ut1
                                                    in
                                                 FStar_Util.print2
                                                   "Pointwise_rec: succeeded rewriting\n\t%s to\n\t%s\n"
                                                   uu____7580 uu____7581);
                                            ret ut1)
                                        in
                                     focus uu____7567))))
                      in
                   let uu____7582 = catch rewrite_eq  in
                   bind uu____7582
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
          let uu____7780 = FStar_Syntax_Subst.compress t  in
          maybe_continue ctrl uu____7780
            (fun t1  ->
               let uu____7788 =
                 f env
                   (let uu___408_7797 = t1  in
                    {
                      FStar_Syntax_Syntax.n = (t1.FStar_Syntax_Syntax.n);
                      FStar_Syntax_Syntax.pos =
                        (uu___408_7797.FStar_Syntax_Syntax.pos);
                      FStar_Syntax_Syntax.vars =
                        (uu___408_7797.FStar_Syntax_Syntax.vars)
                    })
                  in
               bind uu____7788
                 (fun uu____7813  ->
                    match uu____7813 with
                    | (t2,ctrl1) ->
                        maybe_continue ctrl1 t2
                          (fun t3  ->
                             let uu____7836 =
                               let uu____7837 =
                                 FStar_Syntax_Subst.compress t3  in
                               uu____7837.FStar_Syntax_Syntax.n  in
                             match uu____7836 with
                             | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
                                 let uu____7874 =
                                   ctrl_tac_fold f env ctrl1 hd1  in
                                 bind uu____7874
                                   (fun uu____7899  ->
                                      match uu____7899 with
                                      | (hd2,ctrl2) ->
                                          let ctrl3 = keep_going ctrl2  in
                                          let uu____7915 =
                                            ctrl_tac_fold_args f env ctrl3
                                              args
                                             in
                                          bind uu____7915
                                            (fun uu____7942  ->
                                               match uu____7942 with
                                               | (args1,ctrl4) ->
                                                   ret
                                                     ((let uu___406_7972 = t3
                                                          in
                                                       {
                                                         FStar_Syntax_Syntax.n
                                                           =
                                                           (FStar_Syntax_Syntax.Tm_app
                                                              (hd2, args1));
                                                         FStar_Syntax_Syntax.pos
                                                           =
                                                           (uu___406_7972.FStar_Syntax_Syntax.pos);
                                                         FStar_Syntax_Syntax.vars
                                                           =
                                                           (uu___406_7972.FStar_Syntax_Syntax.vars)
                                                       }), ctrl4)))
                             | FStar_Syntax_Syntax.Tm_abs (bs,t4,k) ->
                                 let uu____8014 =
                                   FStar_Syntax_Subst.open_term bs t4  in
                                 (match uu____8014 with
                                  | (bs1,t') ->
                                      let uu____8029 =
                                        let uu____8036 =
                                          FStar_TypeChecker_Env.push_binders
                                            env bs1
                                           in
                                        ctrl_tac_fold f uu____8036 ctrl1 t'
                                         in
                                      bind uu____8029
                                        (fun uu____8054  ->
                                           match uu____8054 with
                                           | (t'',ctrl2) ->
                                               let uu____8069 =
                                                 let uu____8076 =
                                                   let uu___407_8079 = t4  in
                                                   let uu____8082 =
                                                     let uu____8083 =
                                                       let uu____8102 =
                                                         FStar_Syntax_Subst.close_binders
                                                           bs1
                                                          in
                                                       let uu____8111 =
                                                         FStar_Syntax_Subst.close
                                                           bs1 t''
                                                          in
                                                       (uu____8102,
                                                         uu____8111, k)
                                                        in
                                                     FStar_Syntax_Syntax.Tm_abs
                                                       uu____8083
                                                      in
                                                   {
                                                     FStar_Syntax_Syntax.n =
                                                       uu____8082;
                                                     FStar_Syntax_Syntax.pos
                                                       =
                                                       (uu___407_8079.FStar_Syntax_Syntax.pos);
                                                     FStar_Syntax_Syntax.vars
                                                       =
                                                       (uu___407_8079.FStar_Syntax_Syntax.vars)
                                                   }  in
                                                 (uu____8076, ctrl2)  in
                                               ret uu____8069))
                             | FStar_Syntax_Syntax.Tm_arrow (bs,k) ->
                                 ret (t3, ctrl1)
                             | uu____8164 -> ret (t3, ctrl1))))

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
              let uu____8211 = ctrl_tac_fold f env ctrl t  in
              bind uu____8211
                (fun uu____8235  ->
                   match uu____8235 with
                   | (t1,ctrl1) ->
                       let uu____8250 = ctrl_tac_fold_args f env ctrl1 ts1
                          in
                       bind uu____8250
                         (fun uu____8277  ->
                            match uu____8277 with
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
              let uu____8361 =
                let uu____8368 =
                  add_irrelevant_goal "dummy" env FStar_Syntax_Util.t_true
                    opts
                   in
                bind uu____8368
                  (fun uu____8377  ->
                     let uu____8378 = ctrl t1  in
                     bind uu____8378
                       (fun res  ->
                          let uu____8401 = trivial ()  in
                          bind uu____8401 (fun uu____8409  -> ret res)))
                 in
              bind uu____8361
                (fun uu____8425  ->
                   match uu____8425 with
                   | (should_rewrite,ctrl1) ->
                       if Prims.op_Negation should_rewrite
                       then ret (t1, ctrl1)
                       else
                         (let uu____8449 =
                            FStar_TypeChecker_TcTerm.tc_term
                              (let uu___409_8458 = env  in
                               {
                                 FStar_TypeChecker_Env.solver =
                                   (uu___409_8458.FStar_TypeChecker_Env.solver);
                                 FStar_TypeChecker_Env.range =
                                   (uu___409_8458.FStar_TypeChecker_Env.range);
                                 FStar_TypeChecker_Env.curmodule =
                                   (uu___409_8458.FStar_TypeChecker_Env.curmodule);
                                 FStar_TypeChecker_Env.gamma =
                                   (uu___409_8458.FStar_TypeChecker_Env.gamma);
                                 FStar_TypeChecker_Env.gamma_sig =
                                   (uu___409_8458.FStar_TypeChecker_Env.gamma_sig);
                                 FStar_TypeChecker_Env.gamma_cache =
                                   (uu___409_8458.FStar_TypeChecker_Env.gamma_cache);
                                 FStar_TypeChecker_Env.modules =
                                   (uu___409_8458.FStar_TypeChecker_Env.modules);
                                 FStar_TypeChecker_Env.expected_typ =
                                   (uu___409_8458.FStar_TypeChecker_Env.expected_typ);
                                 FStar_TypeChecker_Env.sigtab =
                                   (uu___409_8458.FStar_TypeChecker_Env.sigtab);
                                 FStar_TypeChecker_Env.attrtab =
                                   (uu___409_8458.FStar_TypeChecker_Env.attrtab);
                                 FStar_TypeChecker_Env.is_pattern =
                                   (uu___409_8458.FStar_TypeChecker_Env.is_pattern);
                                 FStar_TypeChecker_Env.instantiate_imp =
                                   (uu___409_8458.FStar_TypeChecker_Env.instantiate_imp);
                                 FStar_TypeChecker_Env.effects =
                                   (uu___409_8458.FStar_TypeChecker_Env.effects);
                                 FStar_TypeChecker_Env.generalize =
                                   (uu___409_8458.FStar_TypeChecker_Env.generalize);
                                 FStar_TypeChecker_Env.letrecs =
                                   (uu___409_8458.FStar_TypeChecker_Env.letrecs);
                                 FStar_TypeChecker_Env.top_level =
                                   (uu___409_8458.FStar_TypeChecker_Env.top_level);
                                 FStar_TypeChecker_Env.check_uvars =
                                   (uu___409_8458.FStar_TypeChecker_Env.check_uvars);
                                 FStar_TypeChecker_Env.use_eq =
                                   (uu___409_8458.FStar_TypeChecker_Env.use_eq);
                                 FStar_TypeChecker_Env.is_iface =
                                   (uu___409_8458.FStar_TypeChecker_Env.is_iface);
                                 FStar_TypeChecker_Env.admit =
                                   (uu___409_8458.FStar_TypeChecker_Env.admit);
                                 FStar_TypeChecker_Env.lax = true;
                                 FStar_TypeChecker_Env.lax_universes =
                                   (uu___409_8458.FStar_TypeChecker_Env.lax_universes);
                                 FStar_TypeChecker_Env.phase1 =
                                   (uu___409_8458.FStar_TypeChecker_Env.phase1);
                                 FStar_TypeChecker_Env.failhard =
                                   (uu___409_8458.FStar_TypeChecker_Env.failhard);
                                 FStar_TypeChecker_Env.nosynth =
                                   (uu___409_8458.FStar_TypeChecker_Env.nosynth);
                                 FStar_TypeChecker_Env.uvar_subtyping =
                                   (uu___409_8458.FStar_TypeChecker_Env.uvar_subtyping);
                                 FStar_TypeChecker_Env.tc_term =
                                   (uu___409_8458.FStar_TypeChecker_Env.tc_term);
                                 FStar_TypeChecker_Env.type_of =
                                   (uu___409_8458.FStar_TypeChecker_Env.type_of);
                                 FStar_TypeChecker_Env.universe_of =
                                   (uu___409_8458.FStar_TypeChecker_Env.universe_of);
                                 FStar_TypeChecker_Env.check_type_of =
                                   (uu___409_8458.FStar_TypeChecker_Env.check_type_of);
                                 FStar_TypeChecker_Env.use_bv_sorts =
                                   (uu___409_8458.FStar_TypeChecker_Env.use_bv_sorts);
                                 FStar_TypeChecker_Env.qtbl_name_and_index =
                                   (uu___409_8458.FStar_TypeChecker_Env.qtbl_name_and_index);
                                 FStar_TypeChecker_Env.normalized_eff_names =
                                   (uu___409_8458.FStar_TypeChecker_Env.normalized_eff_names);
                                 FStar_TypeChecker_Env.proof_ns =
                                   (uu___409_8458.FStar_TypeChecker_Env.proof_ns);
                                 FStar_TypeChecker_Env.synth_hook =
                                   (uu___409_8458.FStar_TypeChecker_Env.synth_hook);
                                 FStar_TypeChecker_Env.splice =
                                   (uu___409_8458.FStar_TypeChecker_Env.splice);
                                 FStar_TypeChecker_Env.is_native_tactic =
                                   (uu___409_8458.FStar_TypeChecker_Env.is_native_tactic);
                                 FStar_TypeChecker_Env.identifier_info =
                                   (uu___409_8458.FStar_TypeChecker_Env.identifier_info);
                                 FStar_TypeChecker_Env.tc_hooks =
                                   (uu___409_8458.FStar_TypeChecker_Env.tc_hooks);
                                 FStar_TypeChecker_Env.dsenv =
                                   (uu___409_8458.FStar_TypeChecker_Env.dsenv);
                                 FStar_TypeChecker_Env.dep_graph =
                                   (uu___409_8458.FStar_TypeChecker_Env.dep_graph);
                                 FStar_TypeChecker_Env.nbe =
                                   (uu___409_8458.FStar_TypeChecker_Env.nbe)
                               }) t1
                             in
                          match uu____8449 with
                          | (t2,lcomp,g) ->
                              let uu____8468 =
                                (let uu____8471 =
                                   FStar_Syntax_Util.is_pure_or_ghost_lcomp
                                     lcomp
                                    in
                                 Prims.op_Negation uu____8471) ||
                                  (let uu____8473 =
                                     FStar_TypeChecker_Env.is_trivial g  in
                                   Prims.op_Negation uu____8473)
                                 in
                              if uu____8468
                              then ret (t2, globalStop)
                              else
                                (let typ = lcomp.FStar_Syntax_Syntax.res_typ
                                    in
                                 let uu____8486 =
                                   new_uvar "pointwise_rec" env typ  in
                                 bind uu____8486
                                   (fun uu____8506  ->
                                      match uu____8506 with
                                      | (ut,uvar_ut) ->
                                          (log ps
                                             (fun uu____8523  ->
                                                let uu____8524 =
                                                  FStar_Syntax_Print.term_to_string
                                                    t2
                                                   in
                                                let uu____8525 =
                                                  FStar_Syntax_Print.term_to_string
                                                    ut
                                                   in
                                                FStar_Util.print2
                                                  "Pointwise_rec: making equality\n\t%s ==\n\t%s\n"
                                                  uu____8524 uu____8525);
                                           (let uu____8526 =
                                              let uu____8529 =
                                                let uu____8530 =
                                                  FStar_TypeChecker_TcTerm.universe_of
                                                    env typ
                                                   in
                                                FStar_Syntax_Util.mk_eq2
                                                  uu____8530 typ t2 ut
                                                 in
                                              add_irrelevant_goal
                                                "rewrite_rec equation" env
                                                uu____8529 opts
                                               in
                                            bind uu____8526
                                              (fun uu____8537  ->
                                                 let uu____8538 =
                                                   bind rewriter
                                                     (fun uu____8552  ->
                                                        let ut1 =
                                                          FStar_TypeChecker_Normalize.reduce_uvar_solutions
                                                            env ut
                                                           in
                                                        log ps
                                                          (fun uu____8558  ->
                                                             let uu____8559 =
                                                               FStar_Syntax_Print.term_to_string
                                                                 t2
                                                                in
                                                             let uu____8560 =
                                                               FStar_Syntax_Print.term_to_string
                                                                 ut1
                                                                in
                                                             FStar_Util.print2
                                                               "rewrite_rec: succeeded rewriting\n\t%s to\n\t%s\n"
                                                               uu____8559
                                                               uu____8560);
                                                        ret (ut1, ctrl1))
                                                    in
                                                 focus uu____8538)))))))
  
let (topdown_rewrite :
  (FStar_Syntax_Syntax.term ->
     (Prims.bool,FStar_BigInt.t) FStar_Pervasives_Native.tuple2 tac)
    -> unit tac -> unit tac)
  =
  fun ctrl  ->
    fun rewriter  ->
      let uu____8601 =
        bind get
          (fun ps  ->
             let uu____8611 =
               match ps.FStar_Tactics_Types.goals with
               | g::gs -> (g, gs)
               | [] -> failwith "no goals"  in
             match uu____8611 with
             | (g,gs) ->
                 let gt1 = FStar_Tactics_Types.goal_type g  in
                 (log ps
                    (fun uu____8648  ->
                       let uu____8649 = FStar_Syntax_Print.term_to_string gt1
                          in
                       FStar_Util.print1 "Topdown_rewrite starting with %s\n"
                         uu____8649);
                  bind dismiss_all
                    (fun uu____8652  ->
                       let uu____8653 =
                         let uu____8660 = FStar_Tactics_Types.goal_env g  in
                         ctrl_tac_fold
                           (rewrite_rec ps ctrl rewriter
                              g.FStar_Tactics_Types.opts) uu____8660
                           keepGoing gt1
                          in
                       bind uu____8653
                         (fun uu____8672  ->
                            match uu____8672 with
                            | (gt',uu____8680) ->
                                (log ps
                                   (fun uu____8684  ->
                                      let uu____8685 =
                                        FStar_Syntax_Print.term_to_string gt'
                                         in
                                      FStar_Util.print1
                                        "Topdown_rewrite seems to have succeded with %s\n"
                                        uu____8685);
                                 (let uu____8686 = push_goals gs  in
                                  bind uu____8686
                                    (fun uu____8691  ->
                                       let uu____8692 =
                                         let uu____8695 =
                                           FStar_Tactics_Types.goal_with_type
                                             g gt'
                                            in
                                         [uu____8695]  in
                                       add_goals uu____8692)))))))
         in
      FStar_All.pipe_left (wrap_err "topdown_rewrite") uu____8601
  
let (pointwise : FStar_Tactics_Types.direction -> unit tac -> unit tac) =
  fun d  ->
    fun tau  ->
      let uu____8718 =
        bind get
          (fun ps  ->
             let uu____8728 =
               match ps.FStar_Tactics_Types.goals with
               | g::gs -> (g, gs)
               | [] -> failwith "no goals"  in
             match uu____8728 with
             | (g,gs) ->
                 let gt1 = FStar_Tactics_Types.goal_type g  in
                 (log ps
                    (fun uu____8765  ->
                       let uu____8766 = FStar_Syntax_Print.term_to_string gt1
                          in
                       FStar_Util.print1 "Pointwise starting with %s\n"
                         uu____8766);
                  bind dismiss_all
                    (fun uu____8769  ->
                       let uu____8770 =
                         let uu____8773 = FStar_Tactics_Types.goal_env g  in
                         tac_fold_env d
                           (pointwise_rec ps tau g.FStar_Tactics_Types.opts)
                           uu____8773 gt1
                          in
                       bind uu____8770
                         (fun gt'  ->
                            log ps
                              (fun uu____8781  ->
                                 let uu____8782 =
                                   FStar_Syntax_Print.term_to_string gt'  in
                                 FStar_Util.print1
                                   "Pointwise seems to have succeded with %s\n"
                                   uu____8782);
                            (let uu____8783 = push_goals gs  in
                             bind uu____8783
                               (fun uu____8788  ->
                                  let uu____8789 =
                                    let uu____8792 =
                                      FStar_Tactics_Types.goal_with_type g
                                        gt'
                                       in
                                    [uu____8792]  in
                                  add_goals uu____8789))))))
         in
      FStar_All.pipe_left (wrap_err "pointwise") uu____8718
  
let (trefl : unit -> unit tac) =
  fun uu____8803  ->
    let uu____8806 =
      let uu____8809 = cur_goal ()  in
      bind uu____8809
        (fun g  ->
           let uu____8827 =
             let uu____8832 = FStar_Tactics_Types.goal_type g  in
             FStar_Syntax_Util.un_squash uu____8832  in
           match uu____8827 with
           | FStar_Pervasives_Native.Some t ->
               let uu____8840 = FStar_Syntax_Util.head_and_args' t  in
               (match uu____8840 with
                | (hd1,args) ->
                    let uu____8879 =
                      let uu____8892 =
                        let uu____8893 = FStar_Syntax_Util.un_uinst hd1  in
                        uu____8893.FStar_Syntax_Syntax.n  in
                      (uu____8892, args)  in
                    (match uu____8879 with
                     | (FStar_Syntax_Syntax.Tm_fvar
                        fv,uu____8907::(l,uu____8909)::(r,uu____8911)::[])
                         when
                         FStar_Syntax_Syntax.fv_eq_lid fv
                           FStar_Parser_Const.eq2_lid
                         ->
                         let uu____8958 =
                           let uu____8961 = FStar_Tactics_Types.goal_env g
                              in
                           do_unify uu____8961 l r  in
                         bind uu____8958
                           (fun b  ->
                              if b
                              then solve' g FStar_Syntax_Util.exp_unit
                              else
                                (let l1 =
                                   let uu____8968 =
                                     FStar_Tactics_Types.goal_env g  in
                                   FStar_TypeChecker_Normalize.normalize
                                     [FStar_TypeChecker_Env.UnfoldUntil
                                        FStar_Syntax_Syntax.delta_constant;
                                     FStar_TypeChecker_Env.Primops;
                                     FStar_TypeChecker_Env.UnfoldTac]
                                     uu____8968 l
                                    in
                                 let r1 =
                                   let uu____8970 =
                                     FStar_Tactics_Types.goal_env g  in
                                   FStar_TypeChecker_Normalize.normalize
                                     [FStar_TypeChecker_Env.UnfoldUntil
                                        FStar_Syntax_Syntax.delta_constant;
                                     FStar_TypeChecker_Env.Primops;
                                     FStar_TypeChecker_Env.UnfoldTac]
                                     uu____8970 r
                                    in
                                 let uu____8971 =
                                   let uu____8974 =
                                     FStar_Tactics_Types.goal_env g  in
                                   do_unify uu____8974 l1 r1  in
                                 bind uu____8971
                                   (fun b1  ->
                                      if b1
                                      then
                                        solve' g FStar_Syntax_Util.exp_unit
                                      else
                                        (let uu____8980 =
                                           let uu____8981 =
                                             FStar_Tactics_Types.goal_env g
                                              in
                                           tts uu____8981 l1  in
                                         let uu____8982 =
                                           let uu____8983 =
                                             FStar_Tactics_Types.goal_env g
                                              in
                                           tts uu____8983 r1  in
                                         fail2
                                           "not a trivial equality ((%s) vs (%s))"
                                           uu____8980 uu____8982))))
                     | (hd2,uu____8985) ->
                         let uu____9002 =
                           let uu____9003 = FStar_Tactics_Types.goal_env g
                              in
                           tts uu____9003 t  in
                         fail1 "trefl: not an equality (%s)" uu____9002))
           | FStar_Pervasives_Native.None  -> fail "not an irrelevant goal")
       in
    FStar_All.pipe_left (wrap_err "trefl") uu____8806
  
let (dup : unit -> unit tac) =
  fun uu____9016  ->
    let uu____9019 = cur_goal ()  in
    bind uu____9019
      (fun g  ->
         let uu____9025 =
           let uu____9032 = FStar_Tactics_Types.goal_env g  in
           let uu____9033 = FStar_Tactics_Types.goal_type g  in
           new_uvar "dup" uu____9032 uu____9033  in
         bind uu____9025
           (fun uu____9042  ->
              match uu____9042 with
              | (u,u_uvar) ->
                  let g' =
                    let uu___410_9052 = g  in
                    {
                      FStar_Tactics_Types.goal_main_env =
                        (uu___410_9052.FStar_Tactics_Types.goal_main_env);
                      FStar_Tactics_Types.goal_ctx_uvar = u_uvar;
                      FStar_Tactics_Types.opts =
                        (uu___410_9052.FStar_Tactics_Types.opts);
                      FStar_Tactics_Types.is_guard =
                        (uu___410_9052.FStar_Tactics_Types.is_guard)
                    }  in
                  bind __dismiss
                    (fun uu____9055  ->
                       let uu____9056 =
                         let uu____9059 = FStar_Tactics_Types.goal_env g  in
                         let uu____9060 =
                           let uu____9061 =
                             let uu____9062 = FStar_Tactics_Types.goal_env g
                                in
                             let uu____9063 = FStar_Tactics_Types.goal_type g
                                in
                             FStar_TypeChecker_TcTerm.universe_of uu____9062
                               uu____9063
                              in
                           let uu____9064 = FStar_Tactics_Types.goal_type g
                              in
                           let uu____9065 =
                             FStar_Tactics_Types.goal_witness g  in
                           FStar_Syntax_Util.mk_eq2 uu____9061 uu____9064 u
                             uu____9065
                            in
                         add_irrelevant_goal "dup equation" uu____9059
                           uu____9060 g.FStar_Tactics_Types.opts
                          in
                       bind uu____9056
                         (fun uu____9068  ->
                            let uu____9069 = add_goals [g']  in
                            bind uu____9069 (fun uu____9073  -> ret ())))))
  
let rec longest_prefix :
  'a .
    ('a -> 'a -> Prims.bool) ->
      'a Prims.list ->
        'a Prims.list ->
          ('a Prims.list,'a Prims.list,'a Prims.list)
            FStar_Pervasives_Native.tuple3
  =
  fun f  ->
    fun l1  ->
      fun l2  ->
        let rec aux acc l11 l21 =
          match (l11, l21) with
          | (x::xs,y::ys) ->
              let uu____9196 = f x y  in
              if uu____9196 then aux (x :: acc) xs ys else (acc, xs, ys)
          | uu____9216 -> (acc, l11, l21)  in
        let uu____9231 = aux [] l1 l2  in
        match uu____9231 with | (pr,t1,t2) -> ((FStar_List.rev pr), t1, t2)
  
let (join_goals :
  FStar_Tactics_Types.goal ->
    FStar_Tactics_Types.goal -> FStar_Tactics_Types.goal tac)
  =
  fun g1  ->
    fun g2  ->
      let close_forall_no_univs1 bs f =
        FStar_List.fold_right
          (fun b  ->
             fun f1  ->
               FStar_Syntax_Util.mk_forall_no_univ
                 (FStar_Pervasives_Native.fst b) f1) bs f
         in
      let uu____9336 = get_phi g1  in
      match uu____9336 with
      | FStar_Pervasives_Native.None  -> fail "goal 1 is not irrelevant"
      | FStar_Pervasives_Native.Some phi1 ->
          let uu____9342 = get_phi g2  in
          (match uu____9342 with
           | FStar_Pervasives_Native.None  -> fail "goal 2 is not irrelevant"
           | FStar_Pervasives_Native.Some phi2 ->
               let gamma1 =
                 (g1.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_gamma
                  in
               let gamma2 =
                 (g2.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_gamma
                  in
               let uu____9354 =
                 longest_prefix FStar_Syntax_Syntax.eq_binding
                   (FStar_List.rev gamma1) (FStar_List.rev gamma2)
                  in
               (match uu____9354 with
                | (gamma,r1,r2) ->
                    let t1 =
                      let uu____9385 =
                        FStar_TypeChecker_Env.binders_of_bindings r1  in
                      close_forall_no_univs1 uu____9385 phi1  in
                    let t2 =
                      let uu____9395 =
                        FStar_TypeChecker_Env.binders_of_bindings r2  in
                      close_forall_no_univs1 uu____9395 phi2  in
                    let uu____9404 =
                      set_solution g1 FStar_Syntax_Util.exp_unit  in
                    bind uu____9404
                      (fun uu____9409  ->
                         let uu____9410 =
                           set_solution g2 FStar_Syntax_Util.exp_unit  in
                         bind uu____9410
                           (fun uu____9417  ->
                              let ng = FStar_Syntax_Util.mk_conj t1 t2  in
                              let nenv =
                                let uu___411_9422 =
                                  FStar_Tactics_Types.goal_env g1  in
                                let uu____9423 =
                                  FStar_Util.smap_create
                                    (Prims.parse_int "100")
                                   in
                                {
                                  FStar_TypeChecker_Env.solver =
                                    (uu___411_9422.FStar_TypeChecker_Env.solver);
                                  FStar_TypeChecker_Env.range =
                                    (uu___411_9422.FStar_TypeChecker_Env.range);
                                  FStar_TypeChecker_Env.curmodule =
                                    (uu___411_9422.FStar_TypeChecker_Env.curmodule);
                                  FStar_TypeChecker_Env.gamma =
                                    (FStar_List.rev gamma);
                                  FStar_TypeChecker_Env.gamma_sig =
                                    (uu___411_9422.FStar_TypeChecker_Env.gamma_sig);
                                  FStar_TypeChecker_Env.gamma_cache =
                                    uu____9423;
                                  FStar_TypeChecker_Env.modules =
                                    (uu___411_9422.FStar_TypeChecker_Env.modules);
                                  FStar_TypeChecker_Env.expected_typ =
                                    (uu___411_9422.FStar_TypeChecker_Env.expected_typ);
                                  FStar_TypeChecker_Env.sigtab =
                                    (uu___411_9422.FStar_TypeChecker_Env.sigtab);
                                  FStar_TypeChecker_Env.attrtab =
                                    (uu___411_9422.FStar_TypeChecker_Env.attrtab);
                                  FStar_TypeChecker_Env.is_pattern =
                                    (uu___411_9422.FStar_TypeChecker_Env.is_pattern);
                                  FStar_TypeChecker_Env.instantiate_imp =
                                    (uu___411_9422.FStar_TypeChecker_Env.instantiate_imp);
                                  FStar_TypeChecker_Env.effects =
                                    (uu___411_9422.FStar_TypeChecker_Env.effects);
                                  FStar_TypeChecker_Env.generalize =
                                    (uu___411_9422.FStar_TypeChecker_Env.generalize);
                                  FStar_TypeChecker_Env.letrecs =
                                    (uu___411_9422.FStar_TypeChecker_Env.letrecs);
                                  FStar_TypeChecker_Env.top_level =
                                    (uu___411_9422.FStar_TypeChecker_Env.top_level);
                                  FStar_TypeChecker_Env.check_uvars =
                                    (uu___411_9422.FStar_TypeChecker_Env.check_uvars);
                                  FStar_TypeChecker_Env.use_eq =
                                    (uu___411_9422.FStar_TypeChecker_Env.use_eq);
                                  FStar_TypeChecker_Env.is_iface =
                                    (uu___411_9422.FStar_TypeChecker_Env.is_iface);
                                  FStar_TypeChecker_Env.admit =
                                    (uu___411_9422.FStar_TypeChecker_Env.admit);
                                  FStar_TypeChecker_Env.lax =
                                    (uu___411_9422.FStar_TypeChecker_Env.lax);
                                  FStar_TypeChecker_Env.lax_universes =
                                    (uu___411_9422.FStar_TypeChecker_Env.lax_universes);
                                  FStar_TypeChecker_Env.phase1 =
                                    (uu___411_9422.FStar_TypeChecker_Env.phase1);
                                  FStar_TypeChecker_Env.failhard =
                                    (uu___411_9422.FStar_TypeChecker_Env.failhard);
                                  FStar_TypeChecker_Env.nosynth =
                                    (uu___411_9422.FStar_TypeChecker_Env.nosynth);
                                  FStar_TypeChecker_Env.uvar_subtyping =
                                    (uu___411_9422.FStar_TypeChecker_Env.uvar_subtyping);
                                  FStar_TypeChecker_Env.tc_term =
                                    (uu___411_9422.FStar_TypeChecker_Env.tc_term);
                                  FStar_TypeChecker_Env.type_of =
                                    (uu___411_9422.FStar_TypeChecker_Env.type_of);
                                  FStar_TypeChecker_Env.universe_of =
                                    (uu___411_9422.FStar_TypeChecker_Env.universe_of);
                                  FStar_TypeChecker_Env.check_type_of =
                                    (uu___411_9422.FStar_TypeChecker_Env.check_type_of);
                                  FStar_TypeChecker_Env.use_bv_sorts =
                                    (uu___411_9422.FStar_TypeChecker_Env.use_bv_sorts);
                                  FStar_TypeChecker_Env.qtbl_name_and_index =
                                    (uu___411_9422.FStar_TypeChecker_Env.qtbl_name_and_index);
                                  FStar_TypeChecker_Env.normalized_eff_names
                                    =
                                    (uu___411_9422.FStar_TypeChecker_Env.normalized_eff_names);
                                  FStar_TypeChecker_Env.proof_ns =
                                    (uu___411_9422.FStar_TypeChecker_Env.proof_ns);
                                  FStar_TypeChecker_Env.synth_hook =
                                    (uu___411_9422.FStar_TypeChecker_Env.synth_hook);
                                  FStar_TypeChecker_Env.splice =
                                    (uu___411_9422.FStar_TypeChecker_Env.splice);
                                  FStar_TypeChecker_Env.is_native_tactic =
                                    (uu___411_9422.FStar_TypeChecker_Env.is_native_tactic);
                                  FStar_TypeChecker_Env.identifier_info =
                                    (uu___411_9422.FStar_TypeChecker_Env.identifier_info);
                                  FStar_TypeChecker_Env.tc_hooks =
                                    (uu___411_9422.FStar_TypeChecker_Env.tc_hooks);
                                  FStar_TypeChecker_Env.dsenv =
                                    (uu___411_9422.FStar_TypeChecker_Env.dsenv);
                                  FStar_TypeChecker_Env.dep_graph =
                                    (uu___411_9422.FStar_TypeChecker_Env.dep_graph);
                                  FStar_TypeChecker_Env.nbe =
                                    (uu___411_9422.FStar_TypeChecker_Env.nbe)
                                }  in
                              let uu____9426 =
                                mk_irrelevant_goal "joined" nenv ng
                                  g1.FStar_Tactics_Types.opts
                                 in
                              bind uu____9426
                                (fun goal  ->
                                   mlog
                                     (fun uu____9435  ->
                                        let uu____9436 =
                                          goal_to_string_verbose g1  in
                                        let uu____9437 =
                                          goal_to_string_verbose g2  in
                                        let uu____9438 =
                                          goal_to_string_verbose goal  in
                                        FStar_Util.print3
                                          "join_goals of\n(%s)\nand\n(%s)\n= (%s)\n"
                                          uu____9436 uu____9437 uu____9438)
                                     (fun uu____9440  -> ret goal))))))
  
let (join : unit -> unit tac) =
  fun uu____9447  ->
    bind get
      (fun ps  ->
         match ps.FStar_Tactics_Types.goals with
         | g1::g2::gs ->
             let uu____9463 =
               set
                 (let uu___412_9468 = ps  in
                  {
                    FStar_Tactics_Types.main_context =
                      (uu___412_9468.FStar_Tactics_Types.main_context);
                    FStar_Tactics_Types.main_goal =
                      (uu___412_9468.FStar_Tactics_Types.main_goal);
                    FStar_Tactics_Types.all_implicits =
                      (uu___412_9468.FStar_Tactics_Types.all_implicits);
                    FStar_Tactics_Types.goals = gs;
                    FStar_Tactics_Types.smt_goals =
                      (uu___412_9468.FStar_Tactics_Types.smt_goals);
                    FStar_Tactics_Types.depth =
                      (uu___412_9468.FStar_Tactics_Types.depth);
                    FStar_Tactics_Types.__dump =
                      (uu___412_9468.FStar_Tactics_Types.__dump);
                    FStar_Tactics_Types.psc =
                      (uu___412_9468.FStar_Tactics_Types.psc);
                    FStar_Tactics_Types.entry_range =
                      (uu___412_9468.FStar_Tactics_Types.entry_range);
                    FStar_Tactics_Types.guard_policy =
                      (uu___412_9468.FStar_Tactics_Types.guard_policy);
                    FStar_Tactics_Types.freshness =
                      (uu___412_9468.FStar_Tactics_Types.freshness);
                    FStar_Tactics_Types.tac_verb_dbg =
                      (uu___412_9468.FStar_Tactics_Types.tac_verb_dbg);
                    FStar_Tactics_Types.local_state =
                      (uu___412_9468.FStar_Tactics_Types.local_state)
                  })
                in
             bind uu____9463
               (fun uu____9471  ->
                  let uu____9472 = join_goals g1 g2  in
                  bind uu____9472 (fun g12  -> add_goals [g12]))
         | uu____9477 -> fail "join: less than 2 goals")
  
let (cases :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 tac)
  =
  fun t  ->
    let uu____9497 =
      let uu____9504 = cur_goal ()  in
      bind uu____9504
        (fun g  ->
           let uu____9514 =
             let uu____9523 = FStar_Tactics_Types.goal_env g  in
             __tc uu____9523 t  in
           bind uu____9514
             (fun uu____9551  ->
                match uu____9551 with
                | (t1,typ,guard) ->
                    let uu____9567 = FStar_Syntax_Util.head_and_args typ  in
                    (match uu____9567 with
                     | (hd1,args) ->
                         let uu____9616 =
                           let uu____9631 =
                             let uu____9632 = FStar_Syntax_Util.un_uinst hd1
                                in
                             uu____9632.FStar_Syntax_Syntax.n  in
                           (uu____9631, args)  in
                         (match uu____9616 with
                          | (FStar_Syntax_Syntax.Tm_fvar
                             fv,(p,uu____9653)::(q,uu____9655)::[]) when
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
                                let uu____9709 =
                                  let uu____9710 =
                                    FStar_Tactics_Types.goal_env g  in
                                  FStar_TypeChecker_Env.push_bv uu____9710
                                    v_p
                                   in
                                FStar_Tactics_Types.goal_with_env g
                                  uu____9709
                                 in
                              let g2 =
                                let uu____9712 =
                                  let uu____9713 =
                                    FStar_Tactics_Types.goal_env g  in
                                  FStar_TypeChecker_Env.push_bv uu____9713
                                    v_q
                                   in
                                FStar_Tactics_Types.goal_with_env g
                                  uu____9712
                                 in
                              bind __dismiss
                                (fun uu____9720  ->
                                   let uu____9721 = add_goals [g1; g2]  in
                                   bind uu____9721
                                     (fun uu____9730  ->
                                        let uu____9731 =
                                          let uu____9736 =
                                            FStar_Syntax_Syntax.bv_to_name
                                              v_p
                                             in
                                          let uu____9737 =
                                            FStar_Syntax_Syntax.bv_to_name
                                              v_q
                                             in
                                          (uu____9736, uu____9737)  in
                                        ret uu____9731))
                          | uu____9742 ->
                              let uu____9757 =
                                let uu____9758 =
                                  FStar_Tactics_Types.goal_env g  in
                                tts uu____9758 typ  in
                              fail1 "Not a disjunction: %s" uu____9757))))
       in
    FStar_All.pipe_left (wrap_err "cases") uu____9497
  
let (set_options : Prims.string -> unit tac) =
  fun s  ->
    let uu____9788 =
      let uu____9791 = cur_goal ()  in
      bind uu____9791
        (fun g  ->
           FStar_Options.push ();
           (let uu____9804 = FStar_Util.smap_copy g.FStar_Tactics_Types.opts
               in
            FStar_Options.set uu____9804);
           (let res = FStar_Options.set_options FStar_Options.Set s  in
            let opts' = FStar_Options.peek ()  in
            FStar_Options.pop ();
            (match res with
             | FStar_Getopt.Success  ->
                 let g' =
                   let uu___413_9811 = g  in
                   {
                     FStar_Tactics_Types.goal_main_env =
                       (uu___413_9811.FStar_Tactics_Types.goal_main_env);
                     FStar_Tactics_Types.goal_ctx_uvar =
                       (uu___413_9811.FStar_Tactics_Types.goal_ctx_uvar);
                     FStar_Tactics_Types.opts = opts';
                     FStar_Tactics_Types.is_guard =
                       (uu___413_9811.FStar_Tactics_Types.is_guard)
                   }  in
                 replace_cur g'
             | FStar_Getopt.Error err ->
                 fail2 "Setting options `%s` failed: %s" s err
             | FStar_Getopt.Help  ->
                 fail1 "Setting options `%s` failed (got `Help`?)" s)))
       in
    FStar_All.pipe_left (wrap_err "set_options") uu____9788
  
let (top_env : unit -> env tac) =
  fun uu____9823  ->
    bind get
      (fun ps  -> FStar_All.pipe_left ret ps.FStar_Tactics_Types.main_context)
  
let (lax_on : unit -> Prims.bool tac) =
  fun uu____9836  ->
    let uu____9839 = cur_goal ()  in
    bind uu____9839
      (fun g  ->
         let uu____9845 =
           (FStar_Options.lax ()) ||
             (let uu____9847 = FStar_Tactics_Types.goal_env g  in
              uu____9847.FStar_TypeChecker_Env.lax)
            in
         ret uu____9845)
  
let (unquote :
  FStar_Reflection_Data.typ ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term tac)
  =
  fun ty  ->
    fun tm  ->
      let uu____9862 =
        mlog
          (fun uu____9867  ->
             let uu____9868 = FStar_Syntax_Print.term_to_string tm  in
             FStar_Util.print1 "unquote: tm = %s\n" uu____9868)
          (fun uu____9871  ->
             let uu____9872 = cur_goal ()  in
             bind uu____9872
               (fun goal  ->
                  let env =
                    let uu____9880 = FStar_Tactics_Types.goal_env goal  in
                    FStar_TypeChecker_Env.set_expected_typ uu____9880 ty  in
                  let uu____9881 = __tc env tm  in
                  bind uu____9881
                    (fun uu____9900  ->
                       match uu____9900 with
                       | (tm1,typ,guard) ->
                           mlog
                             (fun uu____9914  ->
                                let uu____9915 =
                                  FStar_Syntax_Print.term_to_string tm1  in
                                FStar_Util.print1 "unquote: tm' = %s\n"
                                  uu____9915)
                             (fun uu____9917  ->
                                mlog
                                  (fun uu____9920  ->
                                     let uu____9921 =
                                       FStar_Syntax_Print.term_to_string typ
                                        in
                                     FStar_Util.print1 "unquote: typ = %s\n"
                                       uu____9921)
                                  (fun uu____9924  ->
                                     let uu____9925 =
                                       proc_guard "unquote" env guard  in
                                     bind uu____9925
                                       (fun uu____9929  -> ret tm1))))))
         in
      FStar_All.pipe_left (wrap_err "unquote") uu____9862
  
let (uvar_env :
  env ->
    FStar_Reflection_Data.typ FStar_Pervasives_Native.option ->
      FStar_Syntax_Syntax.term tac)
  =
  fun env  ->
    fun ty  ->
      let uu____9952 =
        match ty with
        | FStar_Pervasives_Native.Some ty1 -> ret ty1
        | FStar_Pervasives_Native.None  ->
            let uu____9958 =
              let uu____9965 =
                let uu____9966 = FStar_Syntax_Util.type_u ()  in
                FStar_All.pipe_left FStar_Pervasives_Native.fst uu____9966
                 in
              new_uvar "uvar_env.2" env uu____9965  in
            bind uu____9958
              (fun uu____9982  ->
                 match uu____9982 with | (typ,uvar_typ) -> ret typ)
         in
      bind uu____9952
        (fun typ  ->
           let uu____9994 = new_uvar "uvar_env" env typ  in
           bind uu____9994
             (fun uu____10008  ->
                match uu____10008 with | (t,uvar_t) -> ret t))
  
let (unshelve : FStar_Syntax_Syntax.term -> unit tac) =
  fun t  ->
    let uu____10026 =
      bind get
        (fun ps  ->
           let env = ps.FStar_Tactics_Types.main_context  in
           let opts =
             match ps.FStar_Tactics_Types.goals with
             | g::uu____10045 -> g.FStar_Tactics_Types.opts
             | uu____10048 -> FStar_Options.peek ()  in
           let uu____10051 = FStar_Syntax_Util.head_and_args t  in
           match uu____10051 with
           | ({
                FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                  (ctx_uvar,uu____10071);
                FStar_Syntax_Syntax.pos = uu____10072;
                FStar_Syntax_Syntax.vars = uu____10073;_},uu____10074)
               ->
               let env1 =
                 let uu___414_10116 = env  in
                 {
                   FStar_TypeChecker_Env.solver =
                     (uu___414_10116.FStar_TypeChecker_Env.solver);
                   FStar_TypeChecker_Env.range =
                     (uu___414_10116.FStar_TypeChecker_Env.range);
                   FStar_TypeChecker_Env.curmodule =
                     (uu___414_10116.FStar_TypeChecker_Env.curmodule);
                   FStar_TypeChecker_Env.gamma =
                     (ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_gamma);
                   FStar_TypeChecker_Env.gamma_sig =
                     (uu___414_10116.FStar_TypeChecker_Env.gamma_sig);
                   FStar_TypeChecker_Env.gamma_cache =
                     (uu___414_10116.FStar_TypeChecker_Env.gamma_cache);
                   FStar_TypeChecker_Env.modules =
                     (uu___414_10116.FStar_TypeChecker_Env.modules);
                   FStar_TypeChecker_Env.expected_typ =
                     (uu___414_10116.FStar_TypeChecker_Env.expected_typ);
                   FStar_TypeChecker_Env.sigtab =
                     (uu___414_10116.FStar_TypeChecker_Env.sigtab);
                   FStar_TypeChecker_Env.attrtab =
                     (uu___414_10116.FStar_TypeChecker_Env.attrtab);
                   FStar_TypeChecker_Env.is_pattern =
                     (uu___414_10116.FStar_TypeChecker_Env.is_pattern);
                   FStar_TypeChecker_Env.instantiate_imp =
                     (uu___414_10116.FStar_TypeChecker_Env.instantiate_imp);
                   FStar_TypeChecker_Env.effects =
                     (uu___414_10116.FStar_TypeChecker_Env.effects);
                   FStar_TypeChecker_Env.generalize =
                     (uu___414_10116.FStar_TypeChecker_Env.generalize);
                   FStar_TypeChecker_Env.letrecs =
                     (uu___414_10116.FStar_TypeChecker_Env.letrecs);
                   FStar_TypeChecker_Env.top_level =
                     (uu___414_10116.FStar_TypeChecker_Env.top_level);
                   FStar_TypeChecker_Env.check_uvars =
                     (uu___414_10116.FStar_TypeChecker_Env.check_uvars);
                   FStar_TypeChecker_Env.use_eq =
                     (uu___414_10116.FStar_TypeChecker_Env.use_eq);
                   FStar_TypeChecker_Env.is_iface =
                     (uu___414_10116.FStar_TypeChecker_Env.is_iface);
                   FStar_TypeChecker_Env.admit =
                     (uu___414_10116.FStar_TypeChecker_Env.admit);
                   FStar_TypeChecker_Env.lax =
                     (uu___414_10116.FStar_TypeChecker_Env.lax);
                   FStar_TypeChecker_Env.lax_universes =
                     (uu___414_10116.FStar_TypeChecker_Env.lax_universes);
                   FStar_TypeChecker_Env.phase1 =
                     (uu___414_10116.FStar_TypeChecker_Env.phase1);
                   FStar_TypeChecker_Env.failhard =
                     (uu___414_10116.FStar_TypeChecker_Env.failhard);
                   FStar_TypeChecker_Env.nosynth =
                     (uu___414_10116.FStar_TypeChecker_Env.nosynth);
                   FStar_TypeChecker_Env.uvar_subtyping =
                     (uu___414_10116.FStar_TypeChecker_Env.uvar_subtyping);
                   FStar_TypeChecker_Env.tc_term =
                     (uu___414_10116.FStar_TypeChecker_Env.tc_term);
                   FStar_TypeChecker_Env.type_of =
                     (uu___414_10116.FStar_TypeChecker_Env.type_of);
                   FStar_TypeChecker_Env.universe_of =
                     (uu___414_10116.FStar_TypeChecker_Env.universe_of);
                   FStar_TypeChecker_Env.check_type_of =
                     (uu___414_10116.FStar_TypeChecker_Env.check_type_of);
                   FStar_TypeChecker_Env.use_bv_sorts =
                     (uu___414_10116.FStar_TypeChecker_Env.use_bv_sorts);
                   FStar_TypeChecker_Env.qtbl_name_and_index =
                     (uu___414_10116.FStar_TypeChecker_Env.qtbl_name_and_index);
                   FStar_TypeChecker_Env.normalized_eff_names =
                     (uu___414_10116.FStar_TypeChecker_Env.normalized_eff_names);
                   FStar_TypeChecker_Env.proof_ns =
                     (uu___414_10116.FStar_TypeChecker_Env.proof_ns);
                   FStar_TypeChecker_Env.synth_hook =
                     (uu___414_10116.FStar_TypeChecker_Env.synth_hook);
                   FStar_TypeChecker_Env.splice =
                     (uu___414_10116.FStar_TypeChecker_Env.splice);
                   FStar_TypeChecker_Env.is_native_tactic =
                     (uu___414_10116.FStar_TypeChecker_Env.is_native_tactic);
                   FStar_TypeChecker_Env.identifier_info =
                     (uu___414_10116.FStar_TypeChecker_Env.identifier_info);
                   FStar_TypeChecker_Env.tc_hooks =
                     (uu___414_10116.FStar_TypeChecker_Env.tc_hooks);
                   FStar_TypeChecker_Env.dsenv =
                     (uu___414_10116.FStar_TypeChecker_Env.dsenv);
                   FStar_TypeChecker_Env.dep_graph =
                     (uu___414_10116.FStar_TypeChecker_Env.dep_graph);
                   FStar_TypeChecker_Env.nbe =
                     (uu___414_10116.FStar_TypeChecker_Env.nbe)
                 }  in
               let g = FStar_Tactics_Types.mk_goal env1 ctx_uvar opts false
                  in
               let uu____10118 =
                 let uu____10121 = bnorm_goal g  in [uu____10121]  in
               add_goals uu____10118
           | uu____10122 -> fail "not a uvar")
       in
    FStar_All.pipe_left (wrap_err "unshelve") uu____10026
  
let (tac_and : Prims.bool tac -> Prims.bool tac -> Prims.bool tac) =
  fun t1  ->
    fun t2  ->
      let comp =
        bind t1
          (fun b  ->
             let uu____10171 = if b then t2 else ret false  in
             bind uu____10171 (fun b'  -> if b' then ret b' else fail ""))
         in
      let uu____10182 = trytac comp  in
      bind uu____10182
        (fun uu___350_10190  ->
           match uu___350_10190 with
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
        let uu____10216 =
          bind get
            (fun ps  ->
               let uu____10222 = __tc e t1  in
               bind uu____10222
                 (fun uu____10242  ->
                    match uu____10242 with
                    | (t11,ty1,g1) ->
                        let uu____10254 = __tc e t2  in
                        bind uu____10254
                          (fun uu____10274  ->
                             match uu____10274 with
                             | (t21,ty2,g2) ->
                                 let uu____10286 =
                                   proc_guard "unify_env g1" e g1  in
                                 bind uu____10286
                                   (fun uu____10291  ->
                                      let uu____10292 =
                                        proc_guard "unify_env g2" e g2  in
                                      bind uu____10292
                                        (fun uu____10298  ->
                                           let uu____10299 =
                                             do_unify e ty1 ty2  in
                                           let uu____10302 =
                                             do_unify e t11 t21  in
                                           tac_and uu____10299 uu____10302)))))
           in
        FStar_All.pipe_left (wrap_err "unify_env") uu____10216
  
let (launch_process :
  Prims.string -> Prims.string Prims.list -> Prims.string -> Prims.string tac)
  =
  fun prog  ->
    fun args  ->
      fun input  ->
        bind idtac
          (fun uu____10335  ->
             let uu____10336 = FStar_Options.unsafe_tactic_exec ()  in
             if uu____10336
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
        (fun uu____10357  ->
           let uu____10358 =
             FStar_Syntax_Syntax.gen_bv nm FStar_Pervasives_Native.None t  in
           ret uu____10358)
  
let (change : FStar_Reflection_Data.typ -> unit tac) =
  fun ty  ->
    let uu____10368 =
      mlog
        (fun uu____10373  ->
           let uu____10374 = FStar_Syntax_Print.term_to_string ty  in
           FStar_Util.print1 "change: ty = %s\n" uu____10374)
        (fun uu____10377  ->
           let uu____10378 = cur_goal ()  in
           bind uu____10378
             (fun g  ->
                let uu____10384 =
                  let uu____10393 = FStar_Tactics_Types.goal_env g  in
                  __tc uu____10393 ty  in
                bind uu____10384
                  (fun uu____10405  ->
                     match uu____10405 with
                     | (ty1,uu____10415,guard) ->
                         let uu____10417 =
                           let uu____10420 = FStar_Tactics_Types.goal_env g
                              in
                           proc_guard "change" uu____10420 guard  in
                         bind uu____10417
                           (fun uu____10423  ->
                              let uu____10424 =
                                let uu____10427 =
                                  FStar_Tactics_Types.goal_env g  in
                                let uu____10428 =
                                  FStar_Tactics_Types.goal_type g  in
                                do_unify uu____10427 uu____10428 ty1  in
                              bind uu____10424
                                (fun bb  ->
                                   if bb
                                   then
                                     let uu____10434 =
                                       FStar_Tactics_Types.goal_with_type g
                                         ty1
                                        in
                                     replace_cur uu____10434
                                   else
                                     (let steps =
                                        [FStar_TypeChecker_Env.AllowUnboundUniverses;
                                        FStar_TypeChecker_Env.UnfoldUntil
                                          FStar_Syntax_Syntax.delta_constant;
                                        FStar_TypeChecker_Env.Primops]  in
                                      let ng =
                                        let uu____10440 =
                                          FStar_Tactics_Types.goal_env g  in
                                        let uu____10441 =
                                          FStar_Tactics_Types.goal_type g  in
                                        normalize steps uu____10440
                                          uu____10441
                                         in
                                      let nty =
                                        let uu____10443 =
                                          FStar_Tactics_Types.goal_env g  in
                                        normalize steps uu____10443 ty1  in
                                      let uu____10444 =
                                        let uu____10447 =
                                          FStar_Tactics_Types.goal_env g  in
                                        do_unify uu____10447 ng nty  in
                                      bind uu____10444
                                        (fun b  ->
                                           if b
                                           then
                                             let uu____10453 =
                                               FStar_Tactics_Types.goal_with_type
                                                 g ty1
                                                in
                                             replace_cur uu____10453
                                           else fail "not convertible")))))))
       in
    FStar_All.pipe_left (wrap_err "change") uu____10368
  
let failwhen : 'a . Prims.bool -> Prims.string -> (unit -> 'a tac) -> 'a tac
  = fun b  -> fun msg  -> fun k  -> if b then fail msg else k () 
let (t_destruct :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.fv,FStar_BigInt.t) FStar_Pervasives_Native.tuple2
      Prims.list tac)
  =
  fun s_tm  ->
    let uu____10516 =
      let uu____10525 = cur_goal ()  in
      bind uu____10525
        (fun g  ->
           let uu____10537 =
             let uu____10546 = FStar_Tactics_Types.goal_env g  in
             __tc uu____10546 s_tm  in
           bind uu____10537
             (fun uu____10564  ->
                match uu____10564 with
                | (s_tm1,s_ty,guard) ->
                    let uu____10582 =
                      let uu____10585 = FStar_Tactics_Types.goal_env g  in
                      proc_guard "destruct" uu____10585 guard  in
                    bind uu____10582
                      (fun uu____10597  ->
                         let uu____10598 =
                           FStar_Syntax_Util.head_and_args' s_ty  in
                         match uu____10598 with
                         | (h,args) ->
                             let uu____10643 =
                               let uu____10650 =
                                 let uu____10651 =
                                   FStar_Syntax_Subst.compress h  in
                                 uu____10651.FStar_Syntax_Syntax.n  in
                               match uu____10650 with
                               | FStar_Syntax_Syntax.Tm_fvar fv ->
                                   ret (fv, [])
                               | FStar_Syntax_Syntax.Tm_uinst
                                   ({
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.Tm_fvar fv;
                                      FStar_Syntax_Syntax.pos = uu____10666;
                                      FStar_Syntax_Syntax.vars = uu____10667;_},us)
                                   -> ret (fv, us)
                               | uu____10677 -> fail "type is not an fv"  in
                             bind uu____10643
                               (fun uu____10697  ->
                                  match uu____10697 with
                                  | (fv,a_us) ->
                                      let t_lid =
                                        FStar_Syntax_Syntax.lid_of_fv fv  in
                                      let uu____10713 =
                                        let uu____10716 =
                                          FStar_Tactics_Types.goal_env g  in
                                        FStar_TypeChecker_Env.lookup_sigelt
                                          uu____10716 t_lid
                                         in
                                      (match uu____10713 with
                                       | FStar_Pervasives_Native.None  ->
                                           fail
                                             "type not found in environment"
                                       | FStar_Pervasives_Native.Some se ->
                                           (match se.FStar_Syntax_Syntax.sigel
                                            with
                                            | FStar_Syntax_Syntax.Sig_inductive_typ
                                                (_lid,t_us,t_ps,t_ty,mut,c_lids)
                                                ->
                                                failwhen
                                                  ((FStar_List.length a_us)
                                                     <>
                                                     (FStar_List.length t_us))
                                                  "t_us don't match?"
                                                  (fun uu____10765  ->
                                                     let uu____10766 =
                                                       FStar_Syntax_Subst.open_term
                                                         t_ps t_ty
                                                        in
                                                     match uu____10766 with
                                                     | (t_ps1,t_ty1) ->
                                                         let uu____10781 =
                                                           mapM
                                                             (fun c_lid  ->
                                                                let uu____10809
                                                                  =
                                                                  let uu____10812
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    g  in
                                                                  FStar_TypeChecker_Env.lookup_sigelt
                                                                    uu____10812
                                                                    c_lid
                                                                   in
                                                                match uu____10809
                                                                with
                                                                | FStar_Pervasives_Native.None
                                                                     ->
                                                                    fail
                                                                    "ctor not found?"
                                                                | FStar_Pervasives_Native.Some
                                                                    se1 ->
                                                                    (
                                                                    match 
                                                                    se1.FStar_Syntax_Syntax.sigel
                                                                    with
                                                                    | 
                                                                    FStar_Syntax_Syntax.Sig_datacon
                                                                    (_c_lid,c_us,c_ty,_t_lid,nparam,mut1)
                                                                    ->
                                                                    let fv1 =
                                                                    FStar_Syntax_Syntax.lid_as_fv
                                                                    c_lid
                                                                    FStar_Syntax_Syntax.delta_constant
                                                                    (FStar_Pervasives_Native.Some
                                                                    FStar_Syntax_Syntax.Data_ctor)
                                                                     in
                                                                    failwhen
                                                                    ((FStar_List.length
                                                                    a_us) <>
                                                                    (FStar_List.length
                                                                    c_us))
                                                                    "t_us don't match?"
                                                                    (fun
                                                                    uu____10882
                                                                     ->
                                                                    let s =
                                                                    FStar_TypeChecker_Env.mk_univ_subst
                                                                    c_us a_us
                                                                     in
                                                                    let c_ty1
                                                                    =
                                                                    FStar_Syntax_Subst.subst
                                                                    s c_ty
                                                                     in
                                                                    let uu____10887
                                                                    =
                                                                    FStar_TypeChecker_Env.inst_tscheme
                                                                    (c_us,
                                                                    c_ty1)
                                                                     in
                                                                    match uu____10887
                                                                    with
                                                                    | 
                                                                    (c_us1,c_ty2)
                                                                    ->
                                                                    let uu____10910
                                                                    =
                                                                    FStar_Syntax_Util.arrow_formals_comp
                                                                    c_ty2  in
                                                                    (match uu____10910
                                                                    with
                                                                    | 
                                                                    (bs,comp)
                                                                    ->
                                                                    let uu____10953
                                                                    =
                                                                    FStar_List.splitAt
                                                                    nparam bs
                                                                     in
                                                                    (match uu____10953
                                                                    with
                                                                    | 
                                                                    (d_ps,bs1)
                                                                    ->
                                                                    let uu____11026
                                                                    =
                                                                    let uu____11027
                                                                    =
                                                                    FStar_Syntax_Util.is_total_comp
                                                                    comp  in
                                                                    Prims.op_Negation
                                                                    uu____11027
                                                                     in
                                                                    failwhen
                                                                    uu____11026
                                                                    "not total?"
                                                                    (fun
                                                                    uu____11044
                                                                     ->
                                                                    let mk_pat
                                                                    p =
                                                                    {
                                                                    FStar_Syntax_Syntax.v
                                                                    = p;
                                                                    FStar_Syntax_Syntax.p
                                                                    =
                                                                    (s_tm1.FStar_Syntax_Syntax.pos)
                                                                    }  in
                                                                    let is_imp
                                                                    uu___351_11060
                                                                    =
                                                                    match uu___351_11060
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    (FStar_Syntax_Syntax.Implicit
                                                                    uu____11063)
                                                                    -> true
                                                                    | 
                                                                    uu____11064
                                                                    -> false
                                                                     in
                                                                    let uu____11067
                                                                    =
                                                                    FStar_List.splitAt
                                                                    nparam
                                                                    args  in
                                                                    match uu____11067
                                                                    with
                                                                    | 
                                                                    (a_ps,a_is)
                                                                    ->
                                                                    failwhen
                                                                    ((FStar_List.length
                                                                    a_ps) <>
                                                                    (FStar_List.length
                                                                    d_ps))
                                                                    "params not match?"
                                                                    (fun
                                                                    uu____11200
                                                                     ->
                                                                    let d_ps_a_ps
                                                                    =
                                                                    FStar_List.zip
                                                                    d_ps a_ps
                                                                     in
                                                                    let subst1
                                                                    =
                                                                    FStar_List.map
                                                                    (fun
                                                                    uu____11262
                                                                     ->
                                                                    match uu____11262
                                                                    with
                                                                    | 
                                                                    ((bv,uu____11282),
                                                                    (t,uu____11284))
                                                                    ->
                                                                    FStar_Syntax_Syntax.NT
                                                                    (bv, t))
                                                                    d_ps_a_ps
                                                                     in
                                                                    let bs2 =
                                                                    FStar_Syntax_Subst.subst_binders
                                                                    subst1
                                                                    bs1  in
                                                                    let subpats_1
                                                                    =
                                                                    FStar_List.map
                                                                    (fun
                                                                    uu____11352
                                                                     ->
                                                                    match uu____11352
                                                                    with
                                                                    | 
                                                                    ((bv,uu____11378),
                                                                    (t,uu____11380))
                                                                    ->
                                                                    ((mk_pat
                                                                    (FStar_Syntax_Syntax.Pat_dot_term
                                                                    (bv, t))),
                                                                    true))
                                                                    d_ps_a_ps
                                                                     in
                                                                    let subpats_2
                                                                    =
                                                                    FStar_List.map
                                                                    (fun
                                                                    uu____11435
                                                                     ->
                                                                    match uu____11435
                                                                    with
                                                                    | 
                                                                    (bv,aq)
                                                                    ->
                                                                    ((mk_pat
                                                                    (FStar_Syntax_Syntax.Pat_var
                                                                    bv)),
                                                                    (is_imp
                                                                    aq))) bs2
                                                                     in
                                                                    let subpats
                                                                    =
                                                                    FStar_List.append
                                                                    subpats_1
                                                                    subpats_2
                                                                     in
                                                                    let pat =
                                                                    mk_pat
                                                                    (FStar_Syntax_Syntax.Pat_cons
                                                                    (fv1,
                                                                    subpats))
                                                                     in
                                                                    let env =
                                                                    FStar_Tactics_Types.goal_env
                                                                    g  in
                                                                    let cod =
                                                                    FStar_Tactics_Types.goal_type
                                                                    g  in
                                                                    let equ =
                                                                    env.FStar_TypeChecker_Env.universe_of
                                                                    env s_ty
                                                                     in
                                                                    let uu____11485
                                                                    =
                                                                    FStar_TypeChecker_TcTerm.tc_pat
                                                                    (let uu___415_11502
                                                                    = env  in
                                                                    {
                                                                    FStar_TypeChecker_Env.solver
                                                                    =
                                                                    (uu___415_11502.FStar_TypeChecker_Env.solver);
                                                                    FStar_TypeChecker_Env.range
                                                                    =
                                                                    (uu___415_11502.FStar_TypeChecker_Env.range);
                                                                    FStar_TypeChecker_Env.curmodule
                                                                    =
                                                                    (uu___415_11502.FStar_TypeChecker_Env.curmodule);
                                                                    FStar_TypeChecker_Env.gamma
                                                                    =
                                                                    (uu___415_11502.FStar_TypeChecker_Env.gamma);
                                                                    FStar_TypeChecker_Env.gamma_sig
                                                                    =
                                                                    (uu___415_11502.FStar_TypeChecker_Env.gamma_sig);
                                                                    FStar_TypeChecker_Env.gamma_cache
                                                                    =
                                                                    (uu___415_11502.FStar_TypeChecker_Env.gamma_cache);
                                                                    FStar_TypeChecker_Env.modules
                                                                    =
                                                                    (uu___415_11502.FStar_TypeChecker_Env.modules);
                                                                    FStar_TypeChecker_Env.expected_typ
                                                                    =
                                                                    (uu___415_11502.FStar_TypeChecker_Env.expected_typ);
                                                                    FStar_TypeChecker_Env.sigtab
                                                                    =
                                                                    (uu___415_11502.FStar_TypeChecker_Env.sigtab);
                                                                    FStar_TypeChecker_Env.attrtab
                                                                    =
                                                                    (uu___415_11502.FStar_TypeChecker_Env.attrtab);
                                                                    FStar_TypeChecker_Env.is_pattern
                                                                    =
                                                                    (uu___415_11502.FStar_TypeChecker_Env.is_pattern);
                                                                    FStar_TypeChecker_Env.instantiate_imp
                                                                    =
                                                                    (uu___415_11502.FStar_TypeChecker_Env.instantiate_imp);
                                                                    FStar_TypeChecker_Env.effects
                                                                    =
                                                                    (uu___415_11502.FStar_TypeChecker_Env.effects);
                                                                    FStar_TypeChecker_Env.generalize
                                                                    =
                                                                    (uu___415_11502.FStar_TypeChecker_Env.generalize);
                                                                    FStar_TypeChecker_Env.letrecs
                                                                    =
                                                                    (uu___415_11502.FStar_TypeChecker_Env.letrecs);
                                                                    FStar_TypeChecker_Env.top_level
                                                                    =
                                                                    (uu___415_11502.FStar_TypeChecker_Env.top_level);
                                                                    FStar_TypeChecker_Env.check_uvars
                                                                    =
                                                                    (uu___415_11502.FStar_TypeChecker_Env.check_uvars);
                                                                    FStar_TypeChecker_Env.use_eq
                                                                    =
                                                                    (uu___415_11502.FStar_TypeChecker_Env.use_eq);
                                                                    FStar_TypeChecker_Env.is_iface
                                                                    =
                                                                    (uu___415_11502.FStar_TypeChecker_Env.is_iface);
                                                                    FStar_TypeChecker_Env.admit
                                                                    =
                                                                    (uu___415_11502.FStar_TypeChecker_Env.admit);
                                                                    FStar_TypeChecker_Env.lax
                                                                    = true;
                                                                    FStar_TypeChecker_Env.lax_universes
                                                                    =
                                                                    (uu___415_11502.FStar_TypeChecker_Env.lax_universes);
                                                                    FStar_TypeChecker_Env.phase1
                                                                    =
                                                                    (uu___415_11502.FStar_TypeChecker_Env.phase1);
                                                                    FStar_TypeChecker_Env.failhard
                                                                    =
                                                                    (uu___415_11502.FStar_TypeChecker_Env.failhard);
                                                                    FStar_TypeChecker_Env.nosynth
                                                                    =
                                                                    (uu___415_11502.FStar_TypeChecker_Env.nosynth);
                                                                    FStar_TypeChecker_Env.uvar_subtyping
                                                                    =
                                                                    (uu___415_11502.FStar_TypeChecker_Env.uvar_subtyping);
                                                                    FStar_TypeChecker_Env.tc_term
                                                                    =
                                                                    (uu___415_11502.FStar_TypeChecker_Env.tc_term);
                                                                    FStar_TypeChecker_Env.type_of
                                                                    =
                                                                    (uu___415_11502.FStar_TypeChecker_Env.type_of);
                                                                    FStar_TypeChecker_Env.universe_of
                                                                    =
                                                                    (uu___415_11502.FStar_TypeChecker_Env.universe_of);
                                                                    FStar_TypeChecker_Env.check_type_of
                                                                    =
                                                                    (uu___415_11502.FStar_TypeChecker_Env.check_type_of);
                                                                    FStar_TypeChecker_Env.use_bv_sorts
                                                                    =
                                                                    (uu___415_11502.FStar_TypeChecker_Env.use_bv_sorts);
                                                                    FStar_TypeChecker_Env.qtbl_name_and_index
                                                                    =
                                                                    (uu___415_11502.FStar_TypeChecker_Env.qtbl_name_and_index);
                                                                    FStar_TypeChecker_Env.normalized_eff_names
                                                                    =
                                                                    (uu___415_11502.FStar_TypeChecker_Env.normalized_eff_names);
                                                                    FStar_TypeChecker_Env.proof_ns
                                                                    =
                                                                    (uu___415_11502.FStar_TypeChecker_Env.proof_ns);
                                                                    FStar_TypeChecker_Env.synth_hook
                                                                    =
                                                                    (uu___415_11502.FStar_TypeChecker_Env.synth_hook);
                                                                    FStar_TypeChecker_Env.splice
                                                                    =
                                                                    (uu___415_11502.FStar_TypeChecker_Env.splice);
                                                                    FStar_TypeChecker_Env.is_native_tactic
                                                                    =
                                                                    (uu___415_11502.FStar_TypeChecker_Env.is_native_tactic);
                                                                    FStar_TypeChecker_Env.identifier_info
                                                                    =
                                                                    (uu___415_11502.FStar_TypeChecker_Env.identifier_info);
                                                                    FStar_TypeChecker_Env.tc_hooks
                                                                    =
                                                                    (uu___415_11502.FStar_TypeChecker_Env.tc_hooks);
                                                                    FStar_TypeChecker_Env.dsenv
                                                                    =
                                                                    (uu___415_11502.FStar_TypeChecker_Env.dsenv);
                                                                    FStar_TypeChecker_Env.dep_graph
                                                                    =
                                                                    (uu___415_11502.FStar_TypeChecker_Env.dep_graph);
                                                                    FStar_TypeChecker_Env.nbe
                                                                    =
                                                                    (uu___415_11502.FStar_TypeChecker_Env.nbe)
                                                                    }) true
                                                                    s_ty pat
                                                                     in
                                                                    match uu____11485
                                                                    with
                                                                    | 
                                                                    (uu____11515,uu____11516,uu____11517,pat_t,uu____11519,uu____11520)
                                                                    ->
                                                                    let eq_b
                                                                    =
                                                                    let uu____11526
                                                                    =
                                                                    let uu____11527
                                                                    =
                                                                    FStar_Syntax_Util.mk_eq2
                                                                    equ s_ty
                                                                    s_tm1
                                                                    pat_t  in
                                                                    FStar_Syntax_Util.mk_squash
                                                                    equ
                                                                    uu____11527
                                                                     in
                                                                    FStar_Syntax_Syntax.gen_bv
                                                                    "breq"
                                                                    FStar_Pervasives_Native.None
                                                                    uu____11526
                                                                     in
                                                                    let cod1
                                                                    =
                                                                    let uu____11531
                                                                    =
                                                                    let uu____11540
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_binder
                                                                    eq_b  in
                                                                    [uu____11540]
                                                                     in
                                                                    let uu____11559
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Total
                                                                    cod  in
                                                                    FStar_Syntax_Util.arrow
                                                                    uu____11531
                                                                    uu____11559
                                                                     in
                                                                    let nty =
                                                                    let uu____11565
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Total
                                                                    cod1  in
                                                                    FStar_Syntax_Util.arrow
                                                                    bs2
                                                                    uu____11565
                                                                     in
                                                                    let uu____11568
                                                                    =
                                                                    new_uvar
                                                                    "destruct branch"
                                                                    env nty
                                                                     in
                                                                    bind
                                                                    uu____11568
                                                                    (fun
                                                                    uu____11597
                                                                     ->
                                                                    match uu____11597
                                                                    with
                                                                    | 
                                                                    (uvt,uv)
                                                                    ->
                                                                    let g' =
                                                                    FStar_Tactics_Types.mk_goal
                                                                    env uv
                                                                    g.FStar_Tactics_Types.opts
                                                                    false  in
                                                                    let brt =
                                                                    FStar_Syntax_Util.mk_app_binders
                                                                    uvt bs2
                                                                     in
                                                                    let brt1
                                                                    =
                                                                    let uu____11623
                                                                    =
                                                                    let uu____11634
                                                                    =
                                                                    FStar_Syntax_Syntax.as_arg
                                                                    FStar_Syntax_Util.exp_unit
                                                                     in
                                                                    [uu____11634]
                                                                     in
                                                                    FStar_Syntax_Util.mk_app
                                                                    brt
                                                                    uu____11623
                                                                     in
                                                                    let br =
                                                                    FStar_Syntax_Subst.close_branch
                                                                    (pat,
                                                                    FStar_Pervasives_Native.None,
                                                                    brt1)  in
                                                                    let uu____11670
                                                                    =
                                                                    let uu____11681
                                                                    =
                                                                    let uu____11686
                                                                    =
                                                                    FStar_BigInt.of_int_fs
                                                                    (FStar_List.length
                                                                    bs2)  in
                                                                    (fv1,
                                                                    uu____11686)
                                                                     in
                                                                    (g', br,
                                                                    uu____11681)
                                                                     in
                                                                    ret
                                                                    uu____11670))))))
                                                                    | 
                                                                    uu____11707
                                                                    ->
                                                                    fail
                                                                    "impossible: not a ctor"))
                                                             c_lids
                                                            in
                                                         bind uu____10781
                                                           (fun goal_brs  ->
                                                              let uu____11756
                                                                =
                                                                FStar_List.unzip3
                                                                  goal_brs
                                                                 in
                                                              match uu____11756
                                                              with
                                                              | (goals,brs,infos)
                                                                  ->
                                                                  let w =
                                                                    FStar_Syntax_Syntax.mk
                                                                    (FStar_Syntax_Syntax.Tm_match
                                                                    (s_tm1,
                                                                    brs))
                                                                    FStar_Pervasives_Native.None
                                                                    s_tm1.FStar_Syntax_Syntax.pos
                                                                     in
                                                                  let uu____11829
                                                                    =
                                                                    solve' g
                                                                    w  in
                                                                  bind
                                                                    uu____11829
                                                                    (
                                                                    fun
                                                                    uu____11840
                                                                     ->
                                                                    let uu____11841
                                                                    =
                                                                    add_goals
                                                                    goals  in
                                                                    bind
                                                                    uu____11841
                                                                    (fun
                                                                    uu____11851
                                                                     ->
                                                                    ret infos))))
                                            | uu____11858 ->
                                                fail "not an inductive type"))))))
       in
    FStar_All.pipe_left (wrap_err "destruct") uu____10516
  
let rec last : 'a . 'a Prims.list -> 'a =
  fun l  ->
    match l with
    | [] -> failwith "last: empty list"
    | x::[] -> x
    | uu____11903::xs -> last xs
  
let rec init : 'a . 'a Prims.list -> 'a Prims.list =
  fun l  ->
    match l with
    | [] -> failwith "init: empty list"
    | x::[] -> []
    | x::xs -> let uu____11931 = init xs  in x :: uu____11931
  
let rec (inspect :
  FStar_Syntax_Syntax.term -> FStar_Reflection_Data.term_view tac) =
  fun t  ->
    let uu____11943 =
      let t1 = FStar_Syntax_Util.unascribe t  in
      let t2 = FStar_Syntax_Util.un_uinst t1  in
      let t3 = FStar_Syntax_Util.unlazy_emb t2  in
      match t3.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_meta (t4,uu____11952) -> inspect t4
      | FStar_Syntax_Syntax.Tm_name bv ->
          FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_Var bv)
      | FStar_Syntax_Syntax.Tm_bvar bv ->
          FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_BVar bv)
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_FVar fv)
      | FStar_Syntax_Syntax.Tm_app (hd1,[]) ->
          failwith "empty arguments on Tm_app"
      | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
          let uu____12017 = last args  in
          (match uu____12017 with
           | (a,q) ->
               let q' = FStar_Reflection_Basic.inspect_aqual q  in
               let uu____12047 =
                 let uu____12048 =
                   let uu____12053 =
                     let uu____12054 =
                       let uu____12059 = init args  in
                       FStar_Syntax_Syntax.mk_Tm_app hd1 uu____12059  in
                     uu____12054 FStar_Pervasives_Native.None
                       t3.FStar_Syntax_Syntax.pos
                      in
                   (uu____12053, (a, q'))  in
                 FStar_Reflection_Data.Tv_App uu____12048  in
               FStar_All.pipe_left ret uu____12047)
      | FStar_Syntax_Syntax.Tm_abs ([],uu____12072,uu____12073) ->
          failwith "empty arguments on Tm_abs"
      | FStar_Syntax_Syntax.Tm_abs (bs,t4,k) ->
          let uu____12125 = FStar_Syntax_Subst.open_term bs t4  in
          (match uu____12125 with
           | (bs1,t5) ->
               (match bs1 with
                | [] -> failwith "impossible"
                | b::bs2 ->
                    let uu____12166 =
                      let uu____12167 =
                        let uu____12172 = FStar_Syntax_Util.abs bs2 t5 k  in
                        (b, uu____12172)  in
                      FStar_Reflection_Data.Tv_Abs uu____12167  in
                    FStar_All.pipe_left ret uu____12166))
      | FStar_Syntax_Syntax.Tm_type uu____12175 ->
          FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_Type ())
      | FStar_Syntax_Syntax.Tm_arrow ([],k) ->
          failwith "empty binders on arrow"
      | FStar_Syntax_Syntax.Tm_arrow uu____12199 ->
          let uu____12214 = FStar_Syntax_Util.arrow_one t3  in
          (match uu____12214 with
           | FStar_Pervasives_Native.Some (b,c) ->
               FStar_All.pipe_left ret
                 (FStar_Reflection_Data.Tv_Arrow (b, c))
           | FStar_Pervasives_Native.None  -> failwith "impossible")
      | FStar_Syntax_Syntax.Tm_refine (bv,t4) ->
          let b = FStar_Syntax_Syntax.mk_binder bv  in
          let uu____12244 = FStar_Syntax_Subst.open_term [b] t4  in
          (match uu____12244 with
           | (b',t5) ->
               let b1 =
                 match b' with
                 | b'1::[] -> b'1
                 | uu____12297 -> failwith "impossible"  in
               FStar_All.pipe_left ret
                 (FStar_Reflection_Data.Tv_Refine
                    ((FStar_Pervasives_Native.fst b1), t5)))
      | FStar_Syntax_Syntax.Tm_constant c ->
          let uu____12309 =
            let uu____12310 = FStar_Reflection_Basic.inspect_const c  in
            FStar_Reflection_Data.Tv_Const uu____12310  in
          FStar_All.pipe_left ret uu____12309
      | FStar_Syntax_Syntax.Tm_uvar (ctx_u,s) ->
          let uu____12331 =
            let uu____12332 =
              let uu____12337 =
                let uu____12338 =
                  FStar_Syntax_Unionfind.uvar_id
                    ctx_u.FStar_Syntax_Syntax.ctx_uvar_head
                   in
                FStar_BigInt.of_int_fs uu____12338  in
              (uu____12337, (ctx_u, s))  in
            FStar_Reflection_Data.Tv_Uvar uu____12332  in
          FStar_All.pipe_left ret uu____12331
      | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),t21) ->
          if lb.FStar_Syntax_Syntax.lbunivs <> []
          then FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown
          else
            (match lb.FStar_Syntax_Syntax.lbname with
             | FStar_Util.Inr uu____12372 ->
                 FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown
             | FStar_Util.Inl bv ->
                 let b = FStar_Syntax_Syntax.mk_binder bv  in
                 let uu____12377 = FStar_Syntax_Subst.open_term [b] t21  in
                 (match uu____12377 with
                  | (bs,t22) ->
                      let b1 =
                        match bs with
                        | b1::[] -> b1
                        | uu____12430 ->
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
             | FStar_Util.Inr uu____12464 ->
                 FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown
             | FStar_Util.Inl bv ->
                 let uu____12468 = FStar_Syntax_Subst.open_let_rec [lb] t21
                    in
                 (match uu____12468 with
                  | (lbs,t22) ->
                      (match lbs with
                       | lb1::[] ->
                           (match lb1.FStar_Syntax_Syntax.lbname with
                            | FStar_Util.Inr uu____12488 ->
                                ret FStar_Reflection_Data.Tv_Unknown
                            | FStar_Util.Inl bv1 ->
                                FStar_All.pipe_left ret
                                  (FStar_Reflection_Data.Tv_Let
                                     (true, bv1,
                                       (lb1.FStar_Syntax_Syntax.lbdef), t22)))
                       | uu____12492 ->
                           failwith
                             "impossible: open_term returned different amount of binders")))
      | FStar_Syntax_Syntax.Tm_match (t4,brs) ->
          let rec inspect_pat p =
            match p.FStar_Syntax_Syntax.v with
            | FStar_Syntax_Syntax.Pat_constant c ->
                let uu____12546 = FStar_Reflection_Basic.inspect_const c  in
                FStar_Reflection_Data.Pat_Constant uu____12546
            | FStar_Syntax_Syntax.Pat_cons (fv,ps) ->
                let uu____12565 =
                  let uu____12572 =
                    FStar_List.map
                      (fun uu____12584  ->
                         match uu____12584 with
                         | (p1,uu____12592) -> inspect_pat p1) ps
                     in
                  (fv, uu____12572)  in
                FStar_Reflection_Data.Pat_Cons uu____12565
            | FStar_Syntax_Syntax.Pat_var bv ->
                FStar_Reflection_Data.Pat_Var bv
            | FStar_Syntax_Syntax.Pat_wild bv ->
                FStar_Reflection_Data.Pat_Wild bv
            | FStar_Syntax_Syntax.Pat_dot_term (bv,t5) ->
                FStar_Reflection_Data.Pat_Dot_Term (bv, t5)
             in
          let brs1 = FStar_List.map FStar_Syntax_Subst.open_branch brs  in
          let brs2 =
            FStar_List.map
              (fun uu___352_12686  ->
                 match uu___352_12686 with
                 | (pat,uu____12708,t5) ->
                     let uu____12726 = inspect_pat pat  in (uu____12726, t5))
              brs1
             in
          FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_Match (t4, brs2))
      | FStar_Syntax_Syntax.Tm_unknown  ->
          FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown
      | uu____12735 ->
          ((let uu____12737 =
              let uu____12742 =
                let uu____12743 = FStar_Syntax_Print.tag_of_term t3  in
                let uu____12744 = FStar_Syntax_Print.term_to_string t3  in
                FStar_Util.format2
                  "inspect: outside of expected syntax (%s, %s)\n"
                  uu____12743 uu____12744
                 in
              (FStar_Errors.Warning_CantInspect, uu____12742)  in
            FStar_Errors.log_issue t3.FStar_Syntax_Syntax.pos uu____12737);
           FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown)
       in
    wrap_err "inspect" uu____11943
  
let (pack : FStar_Reflection_Data.term_view -> FStar_Syntax_Syntax.term tac)
  =
  fun tv  ->
    match tv with
    | FStar_Reflection_Data.Tv_Var bv ->
        let uu____12757 = FStar_Syntax_Syntax.bv_to_name bv  in
        FStar_All.pipe_left ret uu____12757
    | FStar_Reflection_Data.Tv_BVar bv ->
        let uu____12761 = FStar_Syntax_Syntax.bv_to_tm bv  in
        FStar_All.pipe_left ret uu____12761
    | FStar_Reflection_Data.Tv_FVar fv ->
        let uu____12765 = FStar_Syntax_Syntax.fv_to_tm fv  in
        FStar_All.pipe_left ret uu____12765
    | FStar_Reflection_Data.Tv_App (l,(r,q)) ->
        let q' = FStar_Reflection_Basic.pack_aqual q  in
        let uu____12772 = FStar_Syntax_Util.mk_app l [(r, q')]  in
        FStar_All.pipe_left ret uu____12772
    | FStar_Reflection_Data.Tv_Abs (b,t) ->
        let uu____12797 =
          FStar_Syntax_Util.abs [b] t FStar_Pervasives_Native.None  in
        FStar_All.pipe_left ret uu____12797
    | FStar_Reflection_Data.Tv_Arrow (b,c) ->
        let uu____12814 = FStar_Syntax_Util.arrow [b] c  in
        FStar_All.pipe_left ret uu____12814
    | FStar_Reflection_Data.Tv_Type () ->
        FStar_All.pipe_left ret FStar_Syntax_Util.ktype
    | FStar_Reflection_Data.Tv_Refine (bv,t) ->
        let uu____12833 = FStar_Syntax_Util.refine bv t  in
        FStar_All.pipe_left ret uu____12833
    | FStar_Reflection_Data.Tv_Const c ->
        let uu____12837 =
          let uu____12838 =
            let uu____12845 =
              let uu____12846 = FStar_Reflection_Basic.pack_const c  in
              FStar_Syntax_Syntax.Tm_constant uu____12846  in
            FStar_Syntax_Syntax.mk uu____12845  in
          uu____12838 FStar_Pervasives_Native.None FStar_Range.dummyRange  in
        FStar_All.pipe_left ret uu____12837
    | FStar_Reflection_Data.Tv_Uvar (_u,ctx_u_s) ->
        let uu____12854 =
          FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_uvar ctx_u_s)
            FStar_Pervasives_Native.None FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____12854
    | FStar_Reflection_Data.Tv_Let (false ,bv,t1,t2) ->
        let lb =
          FStar_Syntax_Util.mk_letbinding (FStar_Util.Inl bv) []
            bv.FStar_Syntax_Syntax.sort FStar_Parser_Const.effect_Tot_lid t1
            [] FStar_Range.dummyRange
           in
        let uu____12863 =
          let uu____12864 =
            let uu____12871 =
              let uu____12872 =
                let uu____12885 =
                  let uu____12888 =
                    let uu____12889 = FStar_Syntax_Syntax.mk_binder bv  in
                    [uu____12889]  in
                  FStar_Syntax_Subst.close uu____12888 t2  in
                ((false, [lb]), uu____12885)  in
              FStar_Syntax_Syntax.Tm_let uu____12872  in
            FStar_Syntax_Syntax.mk uu____12871  in
          uu____12864 FStar_Pervasives_Native.None FStar_Range.dummyRange  in
        FStar_All.pipe_left ret uu____12863
    | FStar_Reflection_Data.Tv_Let (true ,bv,t1,t2) ->
        let lb =
          FStar_Syntax_Util.mk_letbinding (FStar_Util.Inl bv) []
            bv.FStar_Syntax_Syntax.sort FStar_Parser_Const.effect_Tot_lid t1
            [] FStar_Range.dummyRange
           in
        let uu____12929 = FStar_Syntax_Subst.close_let_rec [lb] t2  in
        (match uu____12929 with
         | (lbs,body) ->
             let uu____12944 =
               FStar_Syntax_Syntax.mk
                 (FStar_Syntax_Syntax.Tm_let ((true, lbs), body))
                 FStar_Pervasives_Native.None FStar_Range.dummyRange
                in
             FStar_All.pipe_left ret uu____12944)
    | FStar_Reflection_Data.Tv_Match (t,brs) ->
        let wrap v1 =
          {
            FStar_Syntax_Syntax.v = v1;
            FStar_Syntax_Syntax.p = FStar_Range.dummyRange
          }  in
        let rec pack_pat p =
          match p with
          | FStar_Reflection_Data.Pat_Constant c ->
              let uu____12978 =
                let uu____12979 = FStar_Reflection_Basic.pack_const c  in
                FStar_Syntax_Syntax.Pat_constant uu____12979  in
              FStar_All.pipe_left wrap uu____12978
          | FStar_Reflection_Data.Pat_Cons (fv,ps) ->
              let uu____12986 =
                let uu____12987 =
                  let uu____13000 =
                    FStar_List.map
                      (fun p1  ->
                         let uu____13016 = pack_pat p1  in
                         (uu____13016, false)) ps
                     in
                  (fv, uu____13000)  in
                FStar_Syntax_Syntax.Pat_cons uu____12987  in
              FStar_All.pipe_left wrap uu____12986
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
            (fun uu___353_13062  ->
               match uu___353_13062 with
               | (pat,t1) ->
                   let uu____13079 = pack_pat pat  in
                   (uu____13079, FStar_Pervasives_Native.None, t1)) brs
           in
        let brs2 = FStar_List.map FStar_Syntax_Subst.close_branch brs1  in
        let uu____13127 =
          FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_match (t, brs2))
            FStar_Pervasives_Native.None FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____13127
    | FStar_Reflection_Data.Tv_AscribedT (e,t,tacopt) ->
        let uu____13155 =
          FStar_Syntax_Syntax.mk
            (FStar_Syntax_Syntax.Tm_ascribed
               (e, ((FStar_Util.Inl t), tacopt),
                 FStar_Pervasives_Native.None)) FStar_Pervasives_Native.None
            FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____13155
    | FStar_Reflection_Data.Tv_AscribedC (e,c,tacopt) ->
        let uu____13201 =
          FStar_Syntax_Syntax.mk
            (FStar_Syntax_Syntax.Tm_ascribed
               (e, ((FStar_Util.Inr c), tacopt),
                 FStar_Pervasives_Native.None)) FStar_Pervasives_Native.None
            FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____13201
    | FStar_Reflection_Data.Tv_Unknown  ->
        let uu____13240 =
          FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown
            FStar_Pervasives_Native.None FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____13240
  
let (lget :
  FStar_Reflection_Data.typ -> Prims.string -> FStar_Syntax_Syntax.term tac)
  =
  fun ty  ->
    fun k  ->
      let uu____13257 =
        bind get
          (fun ps  ->
             let uu____13263 =
               FStar_Util.psmap_try_find ps.FStar_Tactics_Types.local_state k
                in
             match uu____13263 with
             | FStar_Pervasives_Native.None  -> fail "not found"
             | FStar_Pervasives_Native.Some t -> unquote ty t)
         in
      FStar_All.pipe_left (wrap_err "lget") uu____13257
  
let (lset :
  FStar_Reflection_Data.typ ->
    Prims.string -> FStar_Syntax_Syntax.term -> unit tac)
  =
  fun _ty  ->
    fun k  ->
      fun t  ->
        let uu____13292 =
          bind get
            (fun ps  ->
               let ps1 =
                 let uu___416_13299 = ps  in
                 let uu____13300 =
                   FStar_Util.psmap_add ps.FStar_Tactics_Types.local_state k
                     t
                    in
                 {
                   FStar_Tactics_Types.main_context =
                     (uu___416_13299.FStar_Tactics_Types.main_context);
                   FStar_Tactics_Types.main_goal =
                     (uu___416_13299.FStar_Tactics_Types.main_goal);
                   FStar_Tactics_Types.all_implicits =
                     (uu___416_13299.FStar_Tactics_Types.all_implicits);
                   FStar_Tactics_Types.goals =
                     (uu___416_13299.FStar_Tactics_Types.goals);
                   FStar_Tactics_Types.smt_goals =
                     (uu___416_13299.FStar_Tactics_Types.smt_goals);
                   FStar_Tactics_Types.depth =
                     (uu___416_13299.FStar_Tactics_Types.depth);
                   FStar_Tactics_Types.__dump =
                     (uu___416_13299.FStar_Tactics_Types.__dump);
                   FStar_Tactics_Types.psc =
                     (uu___416_13299.FStar_Tactics_Types.psc);
                   FStar_Tactics_Types.entry_range =
                     (uu___416_13299.FStar_Tactics_Types.entry_range);
                   FStar_Tactics_Types.guard_policy =
                     (uu___416_13299.FStar_Tactics_Types.guard_policy);
                   FStar_Tactics_Types.freshness =
                     (uu___416_13299.FStar_Tactics_Types.freshness);
                   FStar_Tactics_Types.tac_verb_dbg =
                     (uu___416_13299.FStar_Tactics_Types.tac_verb_dbg);
                   FStar_Tactics_Types.local_state = uu____13300
                 }  in
               set ps1)
           in
        FStar_All.pipe_left (wrap_err "lset") uu____13292
  
let (goal_of_goal_ty :
  env ->
    FStar_Reflection_Data.typ ->
      (FStar_Tactics_Types.goal,FStar_TypeChecker_Env.guard_t)
        FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun typ  ->
      let uu____13325 =
        FStar_TypeChecker_Util.new_implicit_var "proofstate_of_goal_ty"
          typ.FStar_Syntax_Syntax.pos env typ
         in
      match uu____13325 with
      | (u,ctx_uvars,g_u) ->
          let uu____13357 = FStar_List.hd ctx_uvars  in
          (match uu____13357 with
           | (ctx_uvar,uu____13371) ->
               let g =
                 let uu____13373 = FStar_Options.peek ()  in
                 FStar_Tactics_Types.mk_goal env ctx_uvar uu____13373 false
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
        let uu____13393 = goal_of_goal_ty env typ  in
        match uu____13393 with
        | (g,g_u) ->
            let ps =
              let uu____13405 =
                FStar_TypeChecker_Env.debug env
                  (FStar_Options.Other "TacVerbose")
                 in
              let uu____13406 = FStar_Util.psmap_empty ()  in
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
                FStar_Tactics_Types.psc = FStar_TypeChecker_Cfg.null_psc;
                FStar_Tactics_Types.entry_range = rng;
                FStar_Tactics_Types.guard_policy = FStar_Tactics_Types.SMT;
                FStar_Tactics_Types.freshness = (Prims.parse_int "0");
                FStar_Tactics_Types.tac_verb_dbg = uu____13405;
                FStar_Tactics_Types.local_state = uu____13406
              }  in
            let uu____13413 = FStar_Tactics_Types.goal_witness g  in
            (ps, uu____13413)
  