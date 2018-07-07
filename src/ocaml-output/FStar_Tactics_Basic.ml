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
        (try (fun uu___356_158  -> match () with | () -> run t p) ()
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
                 let uu___357_1035 = ps  in
                 {
                   FStar_Tactics_Types.main_context =
                     (uu___357_1035.FStar_Tactics_Types.main_context);
                   FStar_Tactics_Types.main_goal =
                     (uu___357_1035.FStar_Tactics_Types.main_goal);
                   FStar_Tactics_Types.all_implicits =
                     (uu___357_1035.FStar_Tactics_Types.all_implicits);
                   FStar_Tactics_Types.goals =
                     (uu___357_1035.FStar_Tactics_Types.goals);
                   FStar_Tactics_Types.smt_goals =
                     (uu___357_1035.FStar_Tactics_Types.smt_goals);
                   FStar_Tactics_Types.depth =
                     (uu___357_1035.FStar_Tactics_Types.depth);
                   FStar_Tactics_Types.__dump =
                     (uu___357_1035.FStar_Tactics_Types.__dump);
                   FStar_Tactics_Types.psc =
                     (uu___357_1035.FStar_Tactics_Types.psc);
                   FStar_Tactics_Types.entry_range =
                     (uu___357_1035.FStar_Tactics_Types.entry_range);
                   FStar_Tactics_Types.guard_policy =
                     (uu___357_1035.FStar_Tactics_Types.guard_policy);
                   FStar_Tactics_Types.freshness =
                     (q.FStar_Tactics_Types.freshness);
                   FStar_Tactics_Types.tac_verb_dbg =
                     (uu___357_1035.FStar_Tactics_Types.tac_verb_dbg);
                   FStar_Tactics_Types.local_state =
                     (uu___357_1035.FStar_Tactics_Types.local_state)
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
           (fun uu___359_1120  ->
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
           (let uu___360_1221 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___360_1221.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___360_1221.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (FStar_List.append i p.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___360_1221.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (uu___360_1221.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___360_1221.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___360_1221.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___360_1221.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___360_1221.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___360_1221.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___360_1221.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___360_1221.FStar_Tactics_Types.tac_verb_dbg);
              FStar_Tactics_Types.local_state =
                (uu___360_1221.FStar_Tactics_Types.local_state)
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
           (fun uu___362_1251  ->
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
         let uu___363_1302 = FStar_TypeChecker_Env.trivial_guard  in
         {
           FStar_TypeChecker_Env.guard_f =
             (uu___363_1302.FStar_TypeChecker_Env.guard_f);
           FStar_TypeChecker_Env.deferred =
             (uu___363_1302.FStar_TypeChecker_Env.deferred);
           FStar_TypeChecker_Env.univ_ineqs =
             (uu___363_1302.FStar_TypeChecker_Env.univ_ineqs);
           FStar_TypeChecker_Env.implicits = imps
         }  in
       let g1 =
         FStar_TypeChecker_Rel.resolve_implicits_tac
           ps.FStar_Tactics_Types.main_context g
          in
       let ps' =
         let uu___364_1305 = ps  in
         {
           FStar_Tactics_Types.main_context =
             (uu___364_1305.FStar_Tactics_Types.main_context);
           FStar_Tactics_Types.main_goal =
             (uu___364_1305.FStar_Tactics_Types.main_goal);
           FStar_Tactics_Types.all_implicits =
             (g1.FStar_TypeChecker_Env.implicits);
           FStar_Tactics_Types.goals =
             (uu___364_1305.FStar_Tactics_Types.goals);
           FStar_Tactics_Types.smt_goals =
             (uu___364_1305.FStar_Tactics_Types.smt_goals);
           FStar_Tactics_Types.depth =
             (uu___364_1305.FStar_Tactics_Types.depth);
           FStar_Tactics_Types.__dump =
             (uu___364_1305.FStar_Tactics_Types.__dump);
           FStar_Tactics_Types.psc = (uu___364_1305.FStar_Tactics_Types.psc);
           FStar_Tactics_Types.entry_range =
             (uu___364_1305.FStar_Tactics_Types.entry_range);
           FStar_Tactics_Types.guard_policy =
             (uu___364_1305.FStar_Tactics_Types.guard_policy);
           FStar_Tactics_Types.freshness =
             (uu___364_1305.FStar_Tactics_Types.freshness);
           FStar_Tactics_Types.tac_verb_dbg =
             (uu___364_1305.FStar_Tactics_Types.tac_verb_dbg);
           FStar_Tactics_Types.local_state =
             (uu___364_1305.FStar_Tactics_Types.local_state)
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
         let uu___365_1351 = ps  in
         let uu____1352 =
           FStar_List.filter
             (fun g  ->
                let uu____1358 = check_goal_solved g  in
                FStar_Option.isNone uu____1358) ps.FStar_Tactics_Types.goals
            in
         {
           FStar_Tactics_Types.main_context =
             (uu___365_1351.FStar_Tactics_Types.main_context);
           FStar_Tactics_Types.main_goal =
             (uu___365_1351.FStar_Tactics_Types.main_goal);
           FStar_Tactics_Types.all_implicits =
             (uu___365_1351.FStar_Tactics_Types.all_implicits);
           FStar_Tactics_Types.goals = uu____1352;
           FStar_Tactics_Types.smt_goals =
             (uu___365_1351.FStar_Tactics_Types.smt_goals);
           FStar_Tactics_Types.depth =
             (uu___365_1351.FStar_Tactics_Types.depth);
           FStar_Tactics_Types.__dump =
             (uu___365_1351.FStar_Tactics_Types.__dump);
           FStar_Tactics_Types.psc = (uu___365_1351.FStar_Tactics_Types.psc);
           FStar_Tactics_Types.entry_range =
             (uu___365_1351.FStar_Tactics_Types.entry_range);
           FStar_Tactics_Types.guard_policy =
             (uu___365_1351.FStar_Tactics_Types.guard_policy);
           FStar_Tactics_Types.freshness =
             (uu___365_1351.FStar_Tactics_Types.freshness);
           FStar_Tactics_Types.tac_verb_dbg =
             (uu___365_1351.FStar_Tactics_Types.tac_verb_dbg);
           FStar_Tactics_Types.local_state =
             (uu___365_1351.FStar_Tactics_Types.local_state)
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
         let uu___366_1406 = p  in
         let uu____1407 = FStar_List.tl p.FStar_Tactics_Types.goals  in
         {
           FStar_Tactics_Types.main_context =
             (uu___366_1406.FStar_Tactics_Types.main_context);
           FStar_Tactics_Types.main_goal =
             (uu___366_1406.FStar_Tactics_Types.main_goal);
           FStar_Tactics_Types.all_implicits =
             (uu___366_1406.FStar_Tactics_Types.all_implicits);
           FStar_Tactics_Types.goals = uu____1407;
           FStar_Tactics_Types.smt_goals =
             (uu___366_1406.FStar_Tactics_Types.smt_goals);
           FStar_Tactics_Types.depth =
             (uu___366_1406.FStar_Tactics_Types.depth);
           FStar_Tactics_Types.__dump =
             (uu___366_1406.FStar_Tactics_Types.__dump);
           FStar_Tactics_Types.psc = (uu___366_1406.FStar_Tactics_Types.psc);
           FStar_Tactics_Types.entry_range =
             (uu___366_1406.FStar_Tactics_Types.entry_range);
           FStar_Tactics_Types.guard_policy =
             (uu___366_1406.FStar_Tactics_Types.guard_policy);
           FStar_Tactics_Types.freshness =
             (uu___366_1406.FStar_Tactics_Types.freshness);
           FStar_Tactics_Types.tac_verb_dbg =
             (uu___366_1406.FStar_Tactics_Types.tac_verb_dbg);
           FStar_Tactics_Types.local_state =
             (uu___366_1406.FStar_Tactics_Types.local_state)
         }  in
       set uu____1405)
  
let (dismiss : unit -> unit tac) =
  fun uu____1416  ->
    bind get
      (fun p  ->
         match p.FStar_Tactics_Types.goals with
         | [] -> fail "dismiss: no more goals"
         | uu____1423 -> __dismiss)
  
let (solve :
  FStar_Tactics_Types.goal -> FStar_Syntax_Syntax.term -> unit tac) =
  fun goal  ->
    fun solution  ->
      let e = FStar_Tactics_Types.goal_env goal  in
      mlog
        (fun uu____1444  ->
           let uu____1445 =
             let uu____1446 = FStar_Tactics_Types.goal_witness goal  in
             FStar_Syntax_Print.term_to_string uu____1446  in
           let uu____1447 = FStar_Syntax_Print.term_to_string solution  in
           FStar_Util.print2 "solve %s := %s\n" uu____1445 uu____1447)
        (fun uu____1450  ->
           let uu____1451 = trysolve goal solution  in
           bind uu____1451
             (fun b  ->
                if b
                then bind __dismiss (fun uu____1459  -> remove_solved_goals)
                else
                  (let uu____1461 =
                     let uu____1462 =
                       let uu____1463 = FStar_Tactics_Types.goal_env goal  in
                       tts uu____1463 solution  in
                     let uu____1464 =
                       let uu____1465 = FStar_Tactics_Types.goal_env goal  in
                       let uu____1466 = FStar_Tactics_Types.goal_witness goal
                          in
                       tts uu____1465 uu____1466  in
                     let uu____1467 =
                       let uu____1468 = FStar_Tactics_Types.goal_env goal  in
                       let uu____1469 = FStar_Tactics_Types.goal_type goal
                          in
                       tts uu____1468 uu____1469  in
                     FStar_Util.format3 "%s does not solve %s : %s"
                       uu____1462 uu____1464 uu____1467
                      in
                   fail uu____1461)))
  
let (solve' :
  FStar_Tactics_Types.goal -> FStar_Syntax_Syntax.term -> unit tac) =
  fun goal  ->
    fun solution  ->
      let uu____1484 = set_solution goal solution  in
      bind uu____1484
        (fun uu____1488  ->
           bind __dismiss (fun uu____1490  -> remove_solved_goals))
  
let (dismiss_all : unit tac) =
  bind get
    (fun p  ->
       set
         (let uu___367_1497 = p  in
          {
            FStar_Tactics_Types.main_context =
              (uu___367_1497.FStar_Tactics_Types.main_context);
            FStar_Tactics_Types.main_goal =
              (uu___367_1497.FStar_Tactics_Types.main_goal);
            FStar_Tactics_Types.all_implicits =
              (uu___367_1497.FStar_Tactics_Types.all_implicits);
            FStar_Tactics_Types.goals = [];
            FStar_Tactics_Types.smt_goals =
              (uu___367_1497.FStar_Tactics_Types.smt_goals);
            FStar_Tactics_Types.depth =
              (uu___367_1497.FStar_Tactics_Types.depth);
            FStar_Tactics_Types.__dump =
              (uu___367_1497.FStar_Tactics_Types.__dump);
            FStar_Tactics_Types.psc = (uu___367_1497.FStar_Tactics_Types.psc);
            FStar_Tactics_Types.entry_range =
              (uu___367_1497.FStar_Tactics_Types.entry_range);
            FStar_Tactics_Types.guard_policy =
              (uu___367_1497.FStar_Tactics_Types.guard_policy);
            FStar_Tactics_Types.freshness =
              (uu___367_1497.FStar_Tactics_Types.freshness);
            FStar_Tactics_Types.tac_verb_dbg =
              (uu___367_1497.FStar_Tactics_Types.tac_verb_dbg);
            FStar_Tactics_Types.local_state =
              (uu___367_1497.FStar_Tactics_Types.local_state)
          }))
  
let (nwarn : Prims.int FStar_ST.ref) =
  FStar_Util.mk_ref (Prims.parse_int "0") 
let (check_valid_goal : FStar_Tactics_Types.goal -> unit) =
  fun g  ->
    let uu____1516 = FStar_Options.defensive ()  in
    if uu____1516
    then
      let b = true  in
      let env = FStar_Tactics_Types.goal_env g  in
      let b1 =
        b &&
          (let uu____1521 = FStar_Tactics_Types.goal_witness g  in
           FStar_TypeChecker_Env.closed env uu____1521)
         in
      let b2 =
        b1 &&
          (let uu____1524 = FStar_Tactics_Types.goal_type g  in
           FStar_TypeChecker_Env.closed env uu____1524)
         in
      let rec aux b3 e =
        let uu____1536 = FStar_TypeChecker_Env.pop_bv e  in
        match uu____1536 with
        | FStar_Pervasives_Native.None  -> b3
        | FStar_Pervasives_Native.Some (bv,e1) ->
            let b4 =
              b3 &&
                (FStar_TypeChecker_Env.closed e1 bv.FStar_Syntax_Syntax.sort)
               in
            aux b4 e1
         in
      let uu____1554 =
        (let uu____1557 = aux b2 env  in Prims.op_Negation uu____1557) &&
          (let uu____1559 = FStar_ST.op_Bang nwarn  in
           uu____1559 < (Prims.parse_int "5"))
         in
      (if uu____1554
       then
         ((let uu____1580 =
             let uu____1581 = FStar_Tactics_Types.goal_type g  in
             uu____1581.FStar_Syntax_Syntax.pos  in
           let uu____1584 =
             let uu____1589 =
               let uu____1590 = goal_to_string_verbose g  in
               FStar_Util.format1
                 "The following goal is ill-formed. Keeping calm and carrying on...\n<%s>\n\n"
                 uu____1590
                in
             (FStar_Errors.Warning_IllFormedGoal, uu____1589)  in
           FStar_Errors.log_issue uu____1580 uu____1584);
          (let uu____1591 =
             let uu____1592 = FStar_ST.op_Bang nwarn  in
             uu____1592 + (Prims.parse_int "1")  in
           FStar_ST.op_Colon_Equals nwarn uu____1591))
       else ())
    else ()
  
let (add_goals : FStar_Tactics_Types.goal Prims.list -> unit tac) =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___368_1652 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___368_1652.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___368_1652.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___368_1652.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (FStar_List.append gs p.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (uu___368_1652.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___368_1652.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___368_1652.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___368_1652.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___368_1652.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___368_1652.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___368_1652.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___368_1652.FStar_Tactics_Types.tac_verb_dbg);
              FStar_Tactics_Types.local_state =
                (uu___368_1652.FStar_Tactics_Types.local_state)
            }))
  
let (add_smt_goals : FStar_Tactics_Types.goal Prims.list -> unit tac) =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___369_1672 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___369_1672.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___369_1672.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___369_1672.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___369_1672.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (FStar_List.append gs p.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___369_1672.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___369_1672.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___369_1672.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___369_1672.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___369_1672.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___369_1672.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___369_1672.FStar_Tactics_Types.tac_verb_dbg);
              FStar_Tactics_Types.local_state =
                (uu___369_1672.FStar_Tactics_Types.local_state)
            }))
  
let (push_goals : FStar_Tactics_Types.goal Prims.list -> unit tac) =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___370_1692 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___370_1692.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___370_1692.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___370_1692.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (FStar_List.append p.FStar_Tactics_Types.goals gs);
              FStar_Tactics_Types.smt_goals =
                (uu___370_1692.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___370_1692.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___370_1692.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___370_1692.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___370_1692.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___370_1692.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___370_1692.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___370_1692.FStar_Tactics_Types.tac_verb_dbg);
              FStar_Tactics_Types.local_state =
                (uu___370_1692.FStar_Tactics_Types.local_state)
            }))
  
let (push_smt_goals : FStar_Tactics_Types.goal Prims.list -> unit tac) =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___371_1712 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___371_1712.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___371_1712.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___371_1712.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___371_1712.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (FStar_List.append p.FStar_Tactics_Types.smt_goals gs);
              FStar_Tactics_Types.depth =
                (uu___371_1712.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___371_1712.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___371_1712.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___371_1712.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___371_1712.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___371_1712.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___371_1712.FStar_Tactics_Types.tac_verb_dbg);
              FStar_Tactics_Types.local_state =
                (uu___371_1712.FStar_Tactics_Types.local_state)
            }))
  
let (replace_cur : FStar_Tactics_Types.goal -> unit tac) =
  fun g  -> bind __dismiss (fun uu____1723  -> add_goals [g]) 
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
        let uu____1751 =
          FStar_TypeChecker_Env.new_implicit_var_aux reason
            typ.FStar_Syntax_Syntax.pos env typ
            FStar_Syntax_Syntax.Allow_untyped
           in
        match uu____1751 with
        | (u,ctx_uvar,g_u) ->
            let uu____1785 =
              add_implicits g_u.FStar_TypeChecker_Env.implicits  in
            bind uu____1785
              (fun uu____1794  ->
                 let uu____1795 =
                   let uu____1800 =
                     let uu____1801 = FStar_List.hd ctx_uvar  in
                     FStar_Pervasives_Native.fst uu____1801  in
                   (u, uu____1800)  in
                 ret uu____1795)
  
let (is_true : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____1819 = FStar_Syntax_Util.un_squash t  in
    match uu____1819 with
    | FStar_Pervasives_Native.Some t' ->
        let uu____1829 =
          let uu____1830 = FStar_Syntax_Subst.compress t'  in
          uu____1830.FStar_Syntax_Syntax.n  in
        (match uu____1829 with
         | FStar_Syntax_Syntax.Tm_fvar fv ->
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.true_lid
         | uu____1834 -> false)
    | uu____1835 -> false
  
let (is_false : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____1845 = FStar_Syntax_Util.un_squash t  in
    match uu____1845 with
    | FStar_Pervasives_Native.Some t' ->
        let uu____1855 =
          let uu____1856 = FStar_Syntax_Subst.compress t'  in
          uu____1856.FStar_Syntax_Syntax.n  in
        (match uu____1855 with
         | FStar_Syntax_Syntax.Tm_fvar fv ->
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.false_lid
         | uu____1860 -> false)
    | uu____1861 -> false
  
let (cur_goal : unit -> FStar_Tactics_Types.goal tac) =
  fun uu____1872  ->
    bind get
      (fun p  ->
         match p.FStar_Tactics_Types.goals with
         | [] -> fail "No more goals (1)"
         | hd1::tl1 ->
             let uu____1883 =
               FStar_Syntax_Unionfind.find
                 (hd1.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_head
                in
             (match uu____1883 with
              | FStar_Pervasives_Native.None  -> ret hd1
              | FStar_Pervasives_Native.Some t ->
                  ((let uu____1890 = goal_to_string_verbose hd1  in
                    let uu____1891 = FStar_Syntax_Print.term_to_string t  in
                    FStar_Util.print2
                      "!!!!!!!!!!!! GOAL IS ALREADY SOLVED! %s\nsol is %s\n"
                      uu____1890 uu____1891);
                   ret hd1)))
  
let (tadmit : unit -> unit tac) =
  fun uu____1898  ->
    let uu____1901 =
      bind get
        (fun ps  ->
           let uu____1907 = cur_goal ()  in
           bind uu____1907
             (fun g  ->
                (let uu____1914 =
                   let uu____1915 = FStar_Tactics_Types.goal_type g  in
                   uu____1915.FStar_Syntax_Syntax.pos  in
                 let uu____1918 =
                   let uu____1923 =
                     let uu____1924 = goal_to_string ps g  in
                     FStar_Util.format1 "Tactics admitted goal <%s>\n\n"
                       uu____1924
                      in
                   (FStar_Errors.Warning_TacAdmit, uu____1923)  in
                 FStar_Errors.log_issue uu____1914 uu____1918);
                solve' g FStar_Syntax_Util.exp_unit))
       in
    FStar_All.pipe_left (wrap_err "tadmit") uu____1901
  
let (fresh : unit -> FStar_BigInt.t tac) =
  fun uu____1935  ->
    bind get
      (fun ps  ->
         let n1 = ps.FStar_Tactics_Types.freshness  in
         let ps1 =
           let uu___372_1945 = ps  in
           {
             FStar_Tactics_Types.main_context =
               (uu___372_1945.FStar_Tactics_Types.main_context);
             FStar_Tactics_Types.main_goal =
               (uu___372_1945.FStar_Tactics_Types.main_goal);
             FStar_Tactics_Types.all_implicits =
               (uu___372_1945.FStar_Tactics_Types.all_implicits);
             FStar_Tactics_Types.goals =
               (uu___372_1945.FStar_Tactics_Types.goals);
             FStar_Tactics_Types.smt_goals =
               (uu___372_1945.FStar_Tactics_Types.smt_goals);
             FStar_Tactics_Types.depth =
               (uu___372_1945.FStar_Tactics_Types.depth);
             FStar_Tactics_Types.__dump =
               (uu___372_1945.FStar_Tactics_Types.__dump);
             FStar_Tactics_Types.psc =
               (uu___372_1945.FStar_Tactics_Types.psc);
             FStar_Tactics_Types.entry_range =
               (uu___372_1945.FStar_Tactics_Types.entry_range);
             FStar_Tactics_Types.guard_policy =
               (uu___372_1945.FStar_Tactics_Types.guard_policy);
             FStar_Tactics_Types.freshness = (n1 + (Prims.parse_int "1"));
             FStar_Tactics_Types.tac_verb_dbg =
               (uu___372_1945.FStar_Tactics_Types.tac_verb_dbg);
             FStar_Tactics_Types.local_state =
               (uu___372_1945.FStar_Tactics_Types.local_state)
           }  in
         let uu____1946 = set ps1  in
         bind uu____1946
           (fun uu____1951  ->
              let uu____1952 = FStar_BigInt.of_int_fs n1  in ret uu____1952))
  
let (is_guard : unit -> Prims.bool tac) =
  fun uu____1959  ->
    let uu____1962 = cur_goal ()  in
    bind uu____1962 (fun g  -> ret g.FStar_Tactics_Types.is_guard)
  
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
            let uu____1994 = env.FStar_TypeChecker_Env.universe_of env phi
               in
            FStar_Syntax_Util.mk_squash uu____1994 phi  in
          let uu____1995 = new_uvar reason env typ  in
          bind uu____1995
            (fun uu____2010  ->
               match uu____2010 with
               | (uu____2017,ctx_uvar) ->
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
             (fun uu____2062  ->
                let uu____2063 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.print1 "Tac> __tc(%s)\n" uu____2063)
             (fun uu____2066  ->
                let e1 =
                  let uu___373_2068 = e  in
                  {
                    FStar_TypeChecker_Env.solver =
                      (uu___373_2068.FStar_TypeChecker_Env.solver);
                    FStar_TypeChecker_Env.range =
                      (uu___373_2068.FStar_TypeChecker_Env.range);
                    FStar_TypeChecker_Env.curmodule =
                      (uu___373_2068.FStar_TypeChecker_Env.curmodule);
                    FStar_TypeChecker_Env.gamma =
                      (uu___373_2068.FStar_TypeChecker_Env.gamma);
                    FStar_TypeChecker_Env.gamma_sig =
                      (uu___373_2068.FStar_TypeChecker_Env.gamma_sig);
                    FStar_TypeChecker_Env.gamma_cache =
                      (uu___373_2068.FStar_TypeChecker_Env.gamma_cache);
                    FStar_TypeChecker_Env.modules =
                      (uu___373_2068.FStar_TypeChecker_Env.modules);
                    FStar_TypeChecker_Env.expected_typ =
                      (uu___373_2068.FStar_TypeChecker_Env.expected_typ);
                    FStar_TypeChecker_Env.sigtab =
                      (uu___373_2068.FStar_TypeChecker_Env.sigtab);
                    FStar_TypeChecker_Env.attrtab =
                      (uu___373_2068.FStar_TypeChecker_Env.attrtab);
                    FStar_TypeChecker_Env.is_pattern =
                      (uu___373_2068.FStar_TypeChecker_Env.is_pattern);
                    FStar_TypeChecker_Env.instantiate_imp =
                      (uu___373_2068.FStar_TypeChecker_Env.instantiate_imp);
                    FStar_TypeChecker_Env.effects =
                      (uu___373_2068.FStar_TypeChecker_Env.effects);
                    FStar_TypeChecker_Env.generalize =
                      (uu___373_2068.FStar_TypeChecker_Env.generalize);
                    FStar_TypeChecker_Env.letrecs =
                      (uu___373_2068.FStar_TypeChecker_Env.letrecs);
                    FStar_TypeChecker_Env.top_level =
                      (uu___373_2068.FStar_TypeChecker_Env.top_level);
                    FStar_TypeChecker_Env.check_uvars =
                      (uu___373_2068.FStar_TypeChecker_Env.check_uvars);
                    FStar_TypeChecker_Env.use_eq =
                      (uu___373_2068.FStar_TypeChecker_Env.use_eq);
                    FStar_TypeChecker_Env.is_iface =
                      (uu___373_2068.FStar_TypeChecker_Env.is_iface);
                    FStar_TypeChecker_Env.admit =
                      (uu___373_2068.FStar_TypeChecker_Env.admit);
                    FStar_TypeChecker_Env.lax =
                      (uu___373_2068.FStar_TypeChecker_Env.lax);
                    FStar_TypeChecker_Env.lax_universes =
                      (uu___373_2068.FStar_TypeChecker_Env.lax_universes);
                    FStar_TypeChecker_Env.phase1 =
                      (uu___373_2068.FStar_TypeChecker_Env.phase1);
                    FStar_TypeChecker_Env.failhard =
                      (uu___373_2068.FStar_TypeChecker_Env.failhard);
                    FStar_TypeChecker_Env.nosynth =
                      (uu___373_2068.FStar_TypeChecker_Env.nosynth);
                    FStar_TypeChecker_Env.uvar_subtyping = false;
                    FStar_TypeChecker_Env.tc_term =
                      (uu___373_2068.FStar_TypeChecker_Env.tc_term);
                    FStar_TypeChecker_Env.type_of =
                      (uu___373_2068.FStar_TypeChecker_Env.type_of);
                    FStar_TypeChecker_Env.universe_of =
                      (uu___373_2068.FStar_TypeChecker_Env.universe_of);
                    FStar_TypeChecker_Env.check_type_of =
                      (uu___373_2068.FStar_TypeChecker_Env.check_type_of);
                    FStar_TypeChecker_Env.use_bv_sorts =
                      (uu___373_2068.FStar_TypeChecker_Env.use_bv_sorts);
                    FStar_TypeChecker_Env.qtbl_name_and_index =
                      (uu___373_2068.FStar_TypeChecker_Env.qtbl_name_and_index);
                    FStar_TypeChecker_Env.normalized_eff_names =
                      (uu___373_2068.FStar_TypeChecker_Env.normalized_eff_names);
                    FStar_TypeChecker_Env.proof_ns =
                      (uu___373_2068.FStar_TypeChecker_Env.proof_ns);
                    FStar_TypeChecker_Env.synth_hook =
                      (uu___373_2068.FStar_TypeChecker_Env.synth_hook);
                    FStar_TypeChecker_Env.splice =
                      (uu___373_2068.FStar_TypeChecker_Env.splice);
                    FStar_TypeChecker_Env.is_native_tactic =
                      (uu___373_2068.FStar_TypeChecker_Env.is_native_tactic);
                    FStar_TypeChecker_Env.identifier_info =
                      (uu___373_2068.FStar_TypeChecker_Env.identifier_info);
                    FStar_TypeChecker_Env.tc_hooks =
                      (uu___373_2068.FStar_TypeChecker_Env.tc_hooks);
                    FStar_TypeChecker_Env.dsenv =
                      (uu___373_2068.FStar_TypeChecker_Env.dsenv);
                    FStar_TypeChecker_Env.dep_graph =
                      (uu___373_2068.FStar_TypeChecker_Env.dep_graph);
                    FStar_TypeChecker_Env.nbe =
                      (uu___373_2068.FStar_TypeChecker_Env.nbe)
                  }  in
                try
                  (fun uu___375_2079  ->
                     match () with
                     | () ->
                         let uu____2088 =
                           (ps.FStar_Tactics_Types.main_context).FStar_TypeChecker_Env.type_of
                             e1 t
                            in
                         ret uu____2088) ()
                with
                | FStar_Errors.Err (uu____2115,msg) ->
                    let uu____2117 = tts e1 t  in
                    let uu____2118 =
                      let uu____2119 = FStar_TypeChecker_Env.all_binders e1
                         in
                      FStar_All.pipe_right uu____2119
                        (FStar_Syntax_Print.binders_to_string ", ")
                       in
                    fail3 "Cannot type %s in context (%s). Error = (%s)"
                      uu____2117 uu____2118 msg
                | FStar_Errors.Error (uu____2126,msg,uu____2128) ->
                    let uu____2129 = tts e1 t  in
                    let uu____2130 =
                      let uu____2131 = FStar_TypeChecker_Env.all_binders e1
                         in
                      FStar_All.pipe_right uu____2131
                        (FStar_Syntax_Print.binders_to_string ", ")
                       in
                    fail3 "Cannot type %s in context (%s). Error = (%s)"
                      uu____2129 uu____2130 msg))
  
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
  fun uu____2158  ->
    bind get (fun ps  -> ret ps.FStar_Tactics_Types.guard_policy)
  
let (set_guard_policy : FStar_Tactics_Types.guard_policy -> unit tac) =
  fun pol  ->
    bind get
      (fun ps  ->
         set
           (let uu___376_2176 = ps  in
            {
              FStar_Tactics_Types.main_context =
                (uu___376_2176.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___376_2176.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___376_2176.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___376_2176.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (uu___376_2176.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___376_2176.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___376_2176.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___376_2176.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___376_2176.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy = pol;
              FStar_Tactics_Types.freshness =
                (uu___376_2176.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___376_2176.FStar_Tactics_Types.tac_verb_dbg);
              FStar_Tactics_Types.local_state =
                (uu___376_2176.FStar_Tactics_Types.local_state)
            }))
  
let with_policy : 'a . FStar_Tactics_Types.guard_policy -> 'a tac -> 'a tac =
  fun pol  ->
    fun t  ->
      let uu____2200 = get_guard_policy ()  in
      bind uu____2200
        (fun old_pol  ->
           let uu____2206 = set_guard_policy pol  in
           bind uu____2206
             (fun uu____2210  ->
                bind t
                  (fun r  ->
                     let uu____2214 = set_guard_policy old_pol  in
                     bind uu____2214 (fun uu____2218  -> ret r))))
  
let (getopts : FStar_Options.optionstate tac) =
  let uu____2221 = let uu____2226 = cur_goal ()  in trytac uu____2226  in
  bind uu____2221
    (fun uu___347_2233  ->
       match uu___347_2233 with
       | FStar_Pervasives_Native.Some g -> ret g.FStar_Tactics_Types.opts
       | FStar_Pervasives_Native.None  ->
           let uu____2239 = FStar_Options.peek ()  in ret uu____2239)
  
let (proc_guard :
  Prims.string -> env -> FStar_TypeChecker_Env.guard_t -> unit tac) =
  fun reason  ->
    fun e  ->
      fun g  ->
        mlog
          (fun uu____2261  ->
             let uu____2262 = FStar_TypeChecker_Rel.guard_to_string e g  in
             FStar_Util.print2 "Processing guard (%s:%s)\n" reason uu____2262)
          (fun uu____2265  ->
             let uu____2266 = add_implicits g.FStar_TypeChecker_Env.implicits
                in
             bind uu____2266
               (fun uu____2270  ->
                  bind getopts
                    (fun opts  ->
                       let uu____2274 =
                         let uu____2275 =
                           FStar_TypeChecker_Rel.simplify_guard e g  in
                         uu____2275.FStar_TypeChecker_Env.guard_f  in
                       match uu____2274 with
                       | FStar_TypeChecker_Common.Trivial  -> ret ()
                       | FStar_TypeChecker_Common.NonTrivial f ->
                           let uu____2279 = istrivial e f  in
                           if uu____2279
                           then ret ()
                           else
                             bind get
                               (fun ps  ->
                                  match ps.FStar_Tactics_Types.guard_policy
                                  with
                                  | FStar_Tactics_Types.Drop  ->
                                      ((let uu____2289 =
                                          let uu____2294 =
                                            let uu____2295 =
                                              FStar_TypeChecker_Rel.guard_to_string
                                                e g
                                               in
                                            FStar_Util.format1
                                              "Tactics admitted guard <%s>\n\n"
                                              uu____2295
                                             in
                                          (FStar_Errors.Warning_TacAdmit,
                                            uu____2294)
                                           in
                                        FStar_Errors.log_issue
                                          e.FStar_TypeChecker_Env.range
                                          uu____2289);
                                       ret ())
                                  | FStar_Tactics_Types.Goal  ->
                                      mlog
                                        (fun uu____2298  ->
                                           let uu____2299 =
                                             FStar_TypeChecker_Rel.guard_to_string
                                               e g
                                              in
                                           FStar_Util.print2
                                             "Making guard (%s:%s) into a goal\n"
                                             reason uu____2299)
                                        (fun uu____2302  ->
                                           let uu____2303 =
                                             mk_irrelevant_goal reason e f
                                               opts
                                              in
                                           bind uu____2303
                                             (fun goal  ->
                                                let goal1 =
                                                  let uu___377_2310 = goal
                                                     in
                                                  {
                                                    FStar_Tactics_Types.goal_main_env
                                                      =
                                                      (uu___377_2310.FStar_Tactics_Types.goal_main_env);
                                                    FStar_Tactics_Types.goal_ctx_uvar
                                                      =
                                                      (uu___377_2310.FStar_Tactics_Types.goal_ctx_uvar);
                                                    FStar_Tactics_Types.opts
                                                      =
                                                      (uu___377_2310.FStar_Tactics_Types.opts);
                                                    FStar_Tactics_Types.is_guard
                                                      = true
                                                  }  in
                                                push_goals [goal1]))
                                  | FStar_Tactics_Types.SMT  ->
                                      mlog
                                        (fun uu____2313  ->
                                           let uu____2314 =
                                             FStar_TypeChecker_Rel.guard_to_string
                                               e g
                                              in
                                           FStar_Util.print2
                                             "Sending guard (%s:%s) to SMT goal\n"
                                             reason uu____2314)
                                        (fun uu____2317  ->
                                           let uu____2318 =
                                             mk_irrelevant_goal reason e f
                                               opts
                                              in
                                           bind uu____2318
                                             (fun goal  ->
                                                let goal1 =
                                                  let uu___378_2325 = goal
                                                     in
                                                  {
                                                    FStar_Tactics_Types.goal_main_env
                                                      =
                                                      (uu___378_2325.FStar_Tactics_Types.goal_main_env);
                                                    FStar_Tactics_Types.goal_ctx_uvar
                                                      =
                                                      (uu___378_2325.FStar_Tactics_Types.goal_ctx_uvar);
                                                    FStar_Tactics_Types.opts
                                                      =
                                                      (uu___378_2325.FStar_Tactics_Types.opts);
                                                    FStar_Tactics_Types.is_guard
                                                      = true
                                                  }  in
                                                push_smt_goals [goal1]))
                                  | FStar_Tactics_Types.Force  ->
                                      mlog
                                        (fun uu____2328  ->
                                           let uu____2329 =
                                             FStar_TypeChecker_Rel.guard_to_string
                                               e g
                                              in
                                           FStar_Util.print2
                                             "Forcing guard (%s:%s)\n" reason
                                             uu____2329)
                                        (fun uu____2331  ->
                                           try
                                             (fun uu___380_2336  ->
                                                match () with
                                                | () ->
                                                    let uu____2339 =
                                                      let uu____2340 =
                                                        let uu____2341 =
                                                          FStar_TypeChecker_Rel.discharge_guard_no_smt
                                                            e g
                                                           in
                                                        FStar_All.pipe_left
                                                          FStar_TypeChecker_Env.is_trivial
                                                          uu____2341
                                                         in
                                                      Prims.op_Negation
                                                        uu____2340
                                                       in
                                                    if uu____2339
                                                    then
                                                      mlog
                                                        (fun uu____2346  ->
                                                           let uu____2347 =
                                                             FStar_TypeChecker_Rel.guard_to_string
                                                               e g
                                                              in
                                                           FStar_Util.print1
                                                             "guard = %s\n"
                                                             uu____2347)
                                                        (fun uu____2349  ->
                                                           fail1
                                                             "Forcing the guard failed (%s)"
                                                             reason)
                                                    else ret ()) ()
                                           with
                                           | uu___379_2352 ->
                                               mlog
                                                 (fun uu____2357  ->
                                                    let uu____2358 =
                                                      FStar_TypeChecker_Rel.guard_to_string
                                                        e g
                                                       in
                                                    FStar_Util.print1
                                                      "guard = %s\n"
                                                      uu____2358)
                                                 (fun uu____2360  ->
                                                    fail1
                                                      "Forcing the guard failed (%s)"
                                                      reason))))))
  
let (tc : FStar_Syntax_Syntax.term -> FStar_Reflection_Data.typ tac) =
  fun t  ->
    let uu____2370 =
      let uu____2373 = cur_goal ()  in
      bind uu____2373
        (fun goal  ->
           let uu____2379 =
             let uu____2388 = FStar_Tactics_Types.goal_env goal  in
             __tc uu____2388 t  in
           bind uu____2379
             (fun uu____2399  ->
                match uu____2399 with
                | (uu____2408,typ,uu____2410) -> ret typ))
       in
    FStar_All.pipe_left (wrap_err "tc") uu____2370
  
let (add_irrelevant_goal :
  Prims.string ->
    env -> FStar_Reflection_Data.typ -> FStar_Options.optionstate -> unit tac)
  =
  fun reason  ->
    fun env  ->
      fun phi  ->
        fun opts  ->
          let uu____2439 = mk_irrelevant_goal reason env phi opts  in
          bind uu____2439 (fun goal  -> add_goals [goal])
  
let (trivial : unit -> unit tac) =
  fun uu____2450  ->
    let uu____2453 = cur_goal ()  in
    bind uu____2453
      (fun goal  ->
         let uu____2459 =
           let uu____2460 = FStar_Tactics_Types.goal_env goal  in
           let uu____2461 = FStar_Tactics_Types.goal_type goal  in
           istrivial uu____2460 uu____2461  in
         if uu____2459
         then solve' goal FStar_Syntax_Util.exp_unit
         else
           (let uu____2465 =
              let uu____2466 = FStar_Tactics_Types.goal_env goal  in
              let uu____2467 = FStar_Tactics_Types.goal_type goal  in
              tts uu____2466 uu____2467  in
            fail1 "Not a trivial goal: %s" uu____2465))
  
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
          let uu____2496 =
            let uu____2497 = FStar_TypeChecker_Rel.simplify_guard e g  in
            uu____2497.FStar_TypeChecker_Env.guard_f  in
          match uu____2496 with
          | FStar_TypeChecker_Common.Trivial  ->
              ret FStar_Pervasives_Native.None
          | FStar_TypeChecker_Common.NonTrivial f ->
              let uu____2505 = istrivial e f  in
              if uu____2505
              then ret FStar_Pervasives_Native.None
              else
                (let uu____2513 = mk_irrelevant_goal reason e f opts  in
                 bind uu____2513
                   (fun goal  ->
                      ret
                        (FStar_Pervasives_Native.Some
                           (let uu___381_2523 = goal  in
                            {
                              FStar_Tactics_Types.goal_main_env =
                                (uu___381_2523.FStar_Tactics_Types.goal_main_env);
                              FStar_Tactics_Types.goal_ctx_uvar =
                                (uu___381_2523.FStar_Tactics_Types.goal_ctx_uvar);
                              FStar_Tactics_Types.opts =
                                (uu___381_2523.FStar_Tactics_Types.opts);
                              FStar_Tactics_Types.is_guard = true
                            }))))
  
let (smt : unit -> unit tac) =
  fun uu____2530  ->
    let uu____2533 = cur_goal ()  in
    bind uu____2533
      (fun g  ->
         let uu____2539 = is_irrelevant g  in
         if uu____2539
         then bind __dismiss (fun uu____2543  -> add_smt_goals [g])
         else
           (let uu____2545 =
              let uu____2546 = FStar_Tactics_Types.goal_env g  in
              let uu____2547 = FStar_Tactics_Types.goal_type g  in
              tts uu____2546 uu____2547  in
            fail1 "goal is not irrelevant: cannot dispatch to smt (%s)"
              uu____2545))
  
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
             let uu____2596 =
               try
                 (fun uu___386_2619  ->
                    match () with
                    | () ->
                        let uu____2630 =
                          let uu____2639 = FStar_BigInt.to_int_fs n1  in
                          FStar_List.splitAt uu____2639
                            p.FStar_Tactics_Types.goals
                           in
                        ret uu____2630) ()
               with | uu___385_2649 -> fail "divide: not enough goals"  in
             bind uu____2596
               (fun uu____2685  ->
                  match uu____2685 with
                  | (lgs,rgs) ->
                      let lp =
                        let uu___382_2711 = p  in
                        {
                          FStar_Tactics_Types.main_context =
                            (uu___382_2711.FStar_Tactics_Types.main_context);
                          FStar_Tactics_Types.main_goal =
                            (uu___382_2711.FStar_Tactics_Types.main_goal);
                          FStar_Tactics_Types.all_implicits =
                            (uu___382_2711.FStar_Tactics_Types.all_implicits);
                          FStar_Tactics_Types.goals = lgs;
                          FStar_Tactics_Types.smt_goals = [];
                          FStar_Tactics_Types.depth =
                            (uu___382_2711.FStar_Tactics_Types.depth);
                          FStar_Tactics_Types.__dump =
                            (uu___382_2711.FStar_Tactics_Types.__dump);
                          FStar_Tactics_Types.psc =
                            (uu___382_2711.FStar_Tactics_Types.psc);
                          FStar_Tactics_Types.entry_range =
                            (uu___382_2711.FStar_Tactics_Types.entry_range);
                          FStar_Tactics_Types.guard_policy =
                            (uu___382_2711.FStar_Tactics_Types.guard_policy);
                          FStar_Tactics_Types.freshness =
                            (uu___382_2711.FStar_Tactics_Types.freshness);
                          FStar_Tactics_Types.tac_verb_dbg =
                            (uu___382_2711.FStar_Tactics_Types.tac_verb_dbg);
                          FStar_Tactics_Types.local_state =
                            (uu___382_2711.FStar_Tactics_Types.local_state)
                        }  in
                      let uu____2712 = set lp  in
                      bind uu____2712
                        (fun uu____2720  ->
                           bind l
                             (fun a  ->
                                bind get
                                  (fun lp'  ->
                                     let rp =
                                       let uu___383_2736 = lp'  in
                                       {
                                         FStar_Tactics_Types.main_context =
                                           (uu___383_2736.FStar_Tactics_Types.main_context);
                                         FStar_Tactics_Types.main_goal =
                                           (uu___383_2736.FStar_Tactics_Types.main_goal);
                                         FStar_Tactics_Types.all_implicits =
                                           (uu___383_2736.FStar_Tactics_Types.all_implicits);
                                         FStar_Tactics_Types.goals = rgs;
                                         FStar_Tactics_Types.smt_goals = [];
                                         FStar_Tactics_Types.depth =
                                           (uu___383_2736.FStar_Tactics_Types.depth);
                                         FStar_Tactics_Types.__dump =
                                           (uu___383_2736.FStar_Tactics_Types.__dump);
                                         FStar_Tactics_Types.psc =
                                           (uu___383_2736.FStar_Tactics_Types.psc);
                                         FStar_Tactics_Types.entry_range =
                                           (uu___383_2736.FStar_Tactics_Types.entry_range);
                                         FStar_Tactics_Types.guard_policy =
                                           (uu___383_2736.FStar_Tactics_Types.guard_policy);
                                         FStar_Tactics_Types.freshness =
                                           (uu___383_2736.FStar_Tactics_Types.freshness);
                                         FStar_Tactics_Types.tac_verb_dbg =
                                           (uu___383_2736.FStar_Tactics_Types.tac_verb_dbg);
                                         FStar_Tactics_Types.local_state =
                                           (uu___383_2736.FStar_Tactics_Types.local_state)
                                       }  in
                                     let uu____2737 = set rp  in
                                     bind uu____2737
                                       (fun uu____2745  ->
                                          bind r
                                            (fun b  ->
                                               bind get
                                                 (fun rp'  ->
                                                    let p' =
                                                      let uu___384_2761 = rp'
                                                         in
                                                      {
                                                        FStar_Tactics_Types.main_context
                                                          =
                                                          (uu___384_2761.FStar_Tactics_Types.main_context);
                                                        FStar_Tactics_Types.main_goal
                                                          =
                                                          (uu___384_2761.FStar_Tactics_Types.main_goal);
                                                        FStar_Tactics_Types.all_implicits
                                                          =
                                                          (uu___384_2761.FStar_Tactics_Types.all_implicits);
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
                                                          (uu___384_2761.FStar_Tactics_Types.depth);
                                                        FStar_Tactics_Types.__dump
                                                          =
                                                          (uu___384_2761.FStar_Tactics_Types.__dump);
                                                        FStar_Tactics_Types.psc
                                                          =
                                                          (uu___384_2761.FStar_Tactics_Types.psc);
                                                        FStar_Tactics_Types.entry_range
                                                          =
                                                          (uu___384_2761.FStar_Tactics_Types.entry_range);
                                                        FStar_Tactics_Types.guard_policy
                                                          =
                                                          (uu___384_2761.FStar_Tactics_Types.guard_policy);
                                                        FStar_Tactics_Types.freshness
                                                          =
                                                          (uu___384_2761.FStar_Tactics_Types.freshness);
                                                        FStar_Tactics_Types.tac_verb_dbg
                                                          =
                                                          (uu___384_2761.FStar_Tactics_Types.tac_verb_dbg);
                                                        FStar_Tactics_Types.local_state
                                                          =
                                                          (uu___384_2761.FStar_Tactics_Types.local_state)
                                                      }  in
                                                    let uu____2762 = set p'
                                                       in
                                                    bind uu____2762
                                                      (fun uu____2770  ->
                                                         bind
                                                           remove_solved_goals
                                                           (fun uu____2776 
                                                              -> ret (a, b)))))))))))
  
let focus : 'a . 'a tac -> 'a tac =
  fun f  ->
    let uu____2797 = divide FStar_BigInt.one f idtac  in
    bind uu____2797
      (fun uu____2810  -> match uu____2810 with | (a,()) -> ret a)
  
let rec map : 'a . 'a tac -> 'a Prims.list tac =
  fun tau  ->
    bind get
      (fun p  ->
         match p.FStar_Tactics_Types.goals with
         | [] -> ret []
         | uu____2847::uu____2848 ->
             let uu____2851 =
               let uu____2860 = map tau  in
               divide FStar_BigInt.one tau uu____2860  in
             bind uu____2851
               (fun uu____2878  ->
                  match uu____2878 with | (h,t) -> ret (h :: t)))
  
let (seq : unit tac -> unit tac -> unit tac) =
  fun t1  ->
    fun t2  ->
      let uu____2919 =
        bind t1
          (fun uu____2924  ->
             let uu____2925 = map t2  in
             bind uu____2925 (fun uu____2933  -> ret ()))
         in
      focus uu____2919
  
let (intro : unit -> FStar_Syntax_Syntax.binder tac) =
  fun uu____2942  ->
    let uu____2945 =
      let uu____2948 = cur_goal ()  in
      bind uu____2948
        (fun goal  ->
           let uu____2957 =
             let uu____2964 = FStar_Tactics_Types.goal_type goal  in
             FStar_Syntax_Util.arrow_one uu____2964  in
           match uu____2957 with
           | FStar_Pervasives_Native.Some (b,c) ->
               let uu____2973 =
                 let uu____2974 = FStar_Syntax_Util.is_total_comp c  in
                 Prims.op_Negation uu____2974  in
               if uu____2973
               then fail "Codomain is effectful"
               else
                 (let env' =
                    let uu____2979 = FStar_Tactics_Types.goal_env goal  in
                    FStar_TypeChecker_Env.push_binders uu____2979 [b]  in
                  let typ' = comp_to_typ c  in
                  let uu____2993 = new_uvar "intro" env' typ'  in
                  bind uu____2993
                    (fun uu____3009  ->
                       match uu____3009 with
                       | (body,ctx_uvar) ->
                           let sol =
                             FStar_Syntax_Util.abs [b] body
                               (FStar_Pervasives_Native.Some
                                  (FStar_Syntax_Util.residual_comp_of_comp c))
                              in
                           let uu____3033 = set_solution goal sol  in
                           bind uu____3033
                             (fun uu____3039  ->
                                let g =
                                  FStar_Tactics_Types.mk_goal env' ctx_uvar
                                    goal.FStar_Tactics_Types.opts
                                    goal.FStar_Tactics_Types.is_guard
                                   in
                                let uu____3041 =
                                  let uu____3044 = bnorm_goal g  in
                                  replace_cur uu____3044  in
                                bind uu____3041 (fun uu____3046  -> ret b))))
           | FStar_Pervasives_Native.None  ->
               let uu____3051 =
                 let uu____3052 = FStar_Tactics_Types.goal_env goal  in
                 let uu____3053 = FStar_Tactics_Types.goal_type goal  in
                 tts uu____3052 uu____3053  in
               fail1 "goal is not an arrow (%s)" uu____3051)
       in
    FStar_All.pipe_left (wrap_err "intro") uu____2945
  
let (intro_rec :
  unit ->
    (FStar_Syntax_Syntax.binder,FStar_Syntax_Syntax.binder)
      FStar_Pervasives_Native.tuple2 tac)
  =
  fun uu____3068  ->
    let uu____3075 = cur_goal ()  in
    bind uu____3075
      (fun goal  ->
         FStar_Util.print_string
           "WARNING (intro_rec): calling this is known to cause normalizer loops\n";
         FStar_Util.print_string
           "WARNING (intro_rec): proceed at your own risk...\n";
         (let uu____3092 =
            let uu____3099 = FStar_Tactics_Types.goal_type goal  in
            FStar_Syntax_Util.arrow_one uu____3099  in
          match uu____3092 with
          | FStar_Pervasives_Native.Some (b,c) ->
              let uu____3112 =
                let uu____3113 = FStar_Syntax_Util.is_total_comp c  in
                Prims.op_Negation uu____3113  in
              if uu____3112
              then fail "Codomain is effectful"
              else
                (let bv =
                   let uu____3126 = FStar_Tactics_Types.goal_type goal  in
                   FStar_Syntax_Syntax.gen_bv "__recf"
                     FStar_Pervasives_Native.None uu____3126
                    in
                 let bs =
                   let uu____3136 = FStar_Syntax_Syntax.mk_binder bv  in
                   [uu____3136; b]  in
                 let env' =
                   let uu____3162 = FStar_Tactics_Types.goal_env goal  in
                   FStar_TypeChecker_Env.push_binders uu____3162 bs  in
                 let uu____3163 =
                   let uu____3170 = comp_to_typ c  in
                   new_uvar "intro_rec" env' uu____3170  in
                 bind uu____3163
                   (fun uu____3189  ->
                      match uu____3189 with
                      | (u,ctx_uvar_u) ->
                          let lb =
                            let uu____3203 =
                              FStar_Tactics_Types.goal_type goal  in
                            let uu____3206 =
                              FStar_Syntax_Util.abs [b] u
                                FStar_Pervasives_Native.None
                               in
                            FStar_Syntax_Util.mk_letbinding
                              (FStar_Util.Inl bv) [] uu____3203
                              FStar_Parser_Const.effect_Tot_lid uu____3206 []
                              FStar_Range.dummyRange
                             in
                          let body = FStar_Syntax_Syntax.bv_to_name bv  in
                          let uu____3224 =
                            FStar_Syntax_Subst.close_let_rec [lb] body  in
                          (match uu____3224 with
                           | (lbs,body1) ->
                               let tm =
                                 let uu____3246 =
                                   let uu____3247 =
                                     FStar_Tactics_Types.goal_witness goal
                                      in
                                   uu____3247.FStar_Syntax_Syntax.pos  in
                                 FStar_Syntax_Syntax.mk
                                   (FStar_Syntax_Syntax.Tm_let
                                      ((true, lbs), body1))
                                   FStar_Pervasives_Native.None uu____3246
                                  in
                               let uu____3260 = set_solution goal tm  in
                               bind uu____3260
                                 (fun uu____3269  ->
                                    let uu____3270 =
                                      let uu____3273 =
                                        bnorm_goal
                                          (let uu___387_3276 = goal  in
                                           {
                                             FStar_Tactics_Types.goal_main_env
                                               =
                                               (uu___387_3276.FStar_Tactics_Types.goal_main_env);
                                             FStar_Tactics_Types.goal_ctx_uvar
                                               = ctx_uvar_u;
                                             FStar_Tactics_Types.opts =
                                               (uu___387_3276.FStar_Tactics_Types.opts);
                                             FStar_Tactics_Types.is_guard =
                                               (uu___387_3276.FStar_Tactics_Types.is_guard)
                                           })
                                         in
                                      replace_cur uu____3273  in
                                    bind uu____3270
                                      (fun uu____3283  ->
                                         let uu____3284 =
                                           let uu____3289 =
                                             FStar_Syntax_Syntax.mk_binder bv
                                              in
                                           (uu____3289, b)  in
                                         ret uu____3284)))))
          | FStar_Pervasives_Native.None  ->
              let uu____3298 =
                let uu____3299 = FStar_Tactics_Types.goal_env goal  in
                let uu____3300 = FStar_Tactics_Types.goal_type goal  in
                tts uu____3299 uu____3300  in
              fail1 "intro_rec: goal is not an arrow (%s)" uu____3298))
  
let (norm : FStar_Syntax_Embeddings.norm_step Prims.list -> unit tac) =
  fun s  ->
    let uu____3318 = cur_goal ()  in
    bind uu____3318
      (fun goal  ->
         mlog
           (fun uu____3325  ->
              let uu____3326 =
                let uu____3327 = FStar_Tactics_Types.goal_witness goal  in
                FStar_Syntax_Print.term_to_string uu____3327  in
              FStar_Util.print1 "norm: witness = %s\n" uu____3326)
           (fun uu____3332  ->
              let steps =
                let uu____3336 = FStar_TypeChecker_Normalize.tr_norm_steps s
                   in
                FStar_List.append
                  [FStar_TypeChecker_Env.Reify;
                  FStar_TypeChecker_Env.UnfoldTac] uu____3336
                 in
              let t =
                let uu____3340 = FStar_Tactics_Types.goal_env goal  in
                let uu____3341 = FStar_Tactics_Types.goal_type goal  in
                normalize steps uu____3340 uu____3341  in
              let uu____3342 = FStar_Tactics_Types.goal_with_type goal t  in
              replace_cur uu____3342))
  
let (norm_term_env :
  env ->
    FStar_Syntax_Embeddings.norm_step Prims.list ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term tac)
  =
  fun e  ->
    fun s  ->
      fun t  ->
        let uu____3366 =
          mlog
            (fun uu____3371  ->
               let uu____3372 = FStar_Syntax_Print.term_to_string t  in
               FStar_Util.print1 "norm_term: tm = %s\n" uu____3372)
            (fun uu____3374  ->
               bind get
                 (fun ps  ->
                    let opts =
                      match ps.FStar_Tactics_Types.goals with
                      | g::uu____3380 -> g.FStar_Tactics_Types.opts
                      | uu____3383 -> FStar_Options.peek ()  in
                    mlog
                      (fun uu____3388  ->
                         let uu____3389 = FStar_Syntax_Print.term_to_string t
                            in
                         FStar_Util.print1 "norm_term_env: t = %s\n"
                           uu____3389)
                      (fun uu____3392  ->
                         let uu____3393 = __tc e t  in
                         bind uu____3393
                           (fun uu____3414  ->
                              match uu____3414 with
                              | (t1,uu____3424,uu____3425) ->
                                  let steps =
                                    let uu____3429 =
                                      FStar_TypeChecker_Normalize.tr_norm_steps
                                        s
                                       in
                                    FStar_List.append
                                      [FStar_TypeChecker_Env.Reify;
                                      FStar_TypeChecker_Env.UnfoldTac]
                                      uu____3429
                                     in
                                  let t2 =
                                    normalize steps
                                      ps.FStar_Tactics_Types.main_context t1
                                     in
                                  ret t2))))
           in
        FStar_All.pipe_left (wrap_err "norm_term") uu____3366
  
let (refine_intro : unit -> unit tac) =
  fun uu____3443  ->
    let uu____3446 =
      let uu____3449 = cur_goal ()  in
      bind uu____3449
        (fun g  ->
           let uu____3456 =
             let uu____3467 = FStar_Tactics_Types.goal_env g  in
             let uu____3468 = FStar_Tactics_Types.goal_type g  in
             FStar_TypeChecker_Rel.base_and_refinement uu____3467 uu____3468
              in
           match uu____3456 with
           | (uu____3471,FStar_Pervasives_Native.None ) ->
               fail "not a refinement"
           | (t,FStar_Pervasives_Native.Some (bv,phi)) ->
               let g1 = FStar_Tactics_Types.goal_with_type g t  in
               let uu____3496 =
                 let uu____3501 =
                   let uu____3506 =
                     let uu____3507 = FStar_Syntax_Syntax.mk_binder bv  in
                     [uu____3507]  in
                   FStar_Syntax_Subst.open_term uu____3506 phi  in
                 match uu____3501 with
                 | (bvs,phi1) ->
                     let uu____3532 =
                       let uu____3533 = FStar_List.hd bvs  in
                       FStar_Pervasives_Native.fst uu____3533  in
                     (uu____3532, phi1)
                  in
               (match uu____3496 with
                | (bv1,phi1) ->
                    let uu____3552 =
                      let uu____3555 = FStar_Tactics_Types.goal_env g  in
                      let uu____3556 =
                        let uu____3557 =
                          let uu____3560 =
                            let uu____3561 =
                              let uu____3568 =
                                FStar_Tactics_Types.goal_witness g  in
                              (bv1, uu____3568)  in
                            FStar_Syntax_Syntax.NT uu____3561  in
                          [uu____3560]  in
                        FStar_Syntax_Subst.subst uu____3557 phi1  in
                      mk_irrelevant_goal "refine_intro refinement" uu____3555
                        uu____3556 g.FStar_Tactics_Types.opts
                       in
                    bind uu____3552
                      (fun g2  ->
                         bind __dismiss
                           (fun uu____3576  -> add_goals [g1; g2]))))
       in
    FStar_All.pipe_left (wrap_err "refine_intro") uu____3446
  
let (__exact_now : Prims.bool -> FStar_Syntax_Syntax.term -> unit tac) =
  fun set_expected_typ1  ->
    fun t  ->
      let uu____3595 = cur_goal ()  in
      bind uu____3595
        (fun goal  ->
           let env =
             if set_expected_typ1
             then
               let uu____3603 = FStar_Tactics_Types.goal_env goal  in
               let uu____3604 = FStar_Tactics_Types.goal_type goal  in
               FStar_TypeChecker_Env.set_expected_typ uu____3603 uu____3604
             else FStar_Tactics_Types.goal_env goal  in
           let uu____3606 = __tc env t  in
           bind uu____3606
             (fun uu____3625  ->
                match uu____3625 with
                | (t1,typ,guard) ->
                    mlog
                      (fun uu____3640  ->
                         let uu____3641 =
                           FStar_Syntax_Print.term_to_string typ  in
                         let uu____3642 =
                           let uu____3643 = FStar_Tactics_Types.goal_env goal
                              in
                           FStar_TypeChecker_Rel.guard_to_string uu____3643
                             guard
                            in
                         FStar_Util.print2
                           "__exact_now: got type %s\n__exact_now: and guard %s\n"
                           uu____3641 uu____3642)
                      (fun uu____3646  ->
                         let uu____3647 =
                           let uu____3650 = FStar_Tactics_Types.goal_env goal
                              in
                           proc_guard "__exact typing" uu____3650 guard  in
                         bind uu____3647
                           (fun uu____3652  ->
                              mlog
                                (fun uu____3656  ->
                                   let uu____3657 =
                                     FStar_Syntax_Print.term_to_string typ
                                      in
                                   let uu____3658 =
                                     let uu____3659 =
                                       FStar_Tactics_Types.goal_type goal  in
                                     FStar_Syntax_Print.term_to_string
                                       uu____3659
                                      in
                                   FStar_Util.print2
                                     "__exact_now: unifying %s and %s\n"
                                     uu____3657 uu____3658)
                                (fun uu____3662  ->
                                   let uu____3663 =
                                     let uu____3666 =
                                       FStar_Tactics_Types.goal_env goal  in
                                     let uu____3667 =
                                       FStar_Tactics_Types.goal_type goal  in
                                     do_unify uu____3666 typ uu____3667  in
                                   bind uu____3663
                                     (fun b  ->
                                        if b
                                        then solve goal t1
                                        else
                                          (let uu____3673 =
                                             let uu____3674 =
                                               FStar_Tactics_Types.goal_env
                                                 goal
                                                in
                                             tts uu____3674 t1  in
                                           let uu____3675 =
                                             let uu____3676 =
                                               FStar_Tactics_Types.goal_env
                                                 goal
                                                in
                                             tts uu____3676 typ  in
                                           let uu____3677 =
                                             let uu____3678 =
                                               FStar_Tactics_Types.goal_env
                                                 goal
                                                in
                                             let uu____3679 =
                                               FStar_Tactics_Types.goal_type
                                                 goal
                                                in
                                             tts uu____3678 uu____3679  in
                                           let uu____3680 =
                                             let uu____3681 =
                                               FStar_Tactics_Types.goal_env
                                                 goal
                                                in
                                             let uu____3682 =
                                               FStar_Tactics_Types.goal_witness
                                                 goal
                                                in
                                             tts uu____3681 uu____3682  in
                                           fail4
                                             "%s : %s does not exactly solve the goal %s (witness = %s)"
                                             uu____3673 uu____3675 uu____3677
                                             uu____3680)))))))
  
let (t_exact :
  Prims.bool -> Prims.bool -> FStar_Syntax_Syntax.term -> unit tac) =
  fun try_refine  ->
    fun set_expected_typ1  ->
      fun tm  ->
        let uu____3702 =
          mlog
            (fun uu____3707  ->
               let uu____3708 = FStar_Syntax_Print.term_to_string tm  in
               FStar_Util.print1 "t_exact: tm = %s\n" uu____3708)
            (fun uu____3711  ->
               let uu____3712 =
                 let uu____3719 = __exact_now set_expected_typ1 tm  in
                 catch uu____3719  in
               bind uu____3712
                 (fun uu___349_3728  ->
                    match uu___349_3728 with
                    | FStar_Util.Inr r -> ret ()
                    | FStar_Util.Inl e when Prims.op_Negation try_refine ->
                        fail e
                    | FStar_Util.Inl e ->
                        mlog
                          (fun uu____3739  ->
                             FStar_Util.print_string
                               "__exact_now failed, trying refine...\n")
                          (fun uu____3742  ->
                             let uu____3743 =
                               let uu____3750 =
                                 let uu____3753 =
                                   norm [FStar_Syntax_Embeddings.Delta]  in
                                 bind uu____3753
                                   (fun uu____3758  ->
                                      let uu____3759 = refine_intro ()  in
                                      bind uu____3759
                                        (fun uu____3763  ->
                                           __exact_now set_expected_typ1 tm))
                                  in
                               catch uu____3750  in
                             bind uu____3743
                               (fun uu___348_3770  ->
                                  match uu___348_3770 with
                                  | FStar_Util.Inr r -> ret ()
                                  | FStar_Util.Inl uu____3778 -> fail e))))
           in
        FStar_All.pipe_left (wrap_err "exact") uu____3702
  
let rec mapM : 'a 'b . ('a -> 'b tac) -> 'a Prims.list -> 'b Prims.list tac =
  fun f  ->
    fun l  ->
      match l with
      | [] -> ret []
      | x::xs ->
          let uu____3828 = f x  in
          bind uu____3828
            (fun y  ->
               let uu____3836 = mapM f xs  in
               bind uu____3836 (fun ys  -> ret (y :: ys)))
  
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
          let uu____3907 = do_unify e ty1 ty2  in
          bind uu____3907
            (fun uu___350_3919  ->
               if uu___350_3919
               then ret acc
               else
                 (let uu____3938 = FStar_Syntax_Util.arrow_one ty1  in
                  match uu____3938 with
                  | FStar_Pervasives_Native.None  ->
                      let uu____3959 = FStar_Syntax_Print.term_to_string ty1
                         in
                      let uu____3960 = FStar_Syntax_Print.term_to_string ty2
                         in
                      fail2 "Could not instantiate, %s to %s" uu____3959
                        uu____3960
                  | FStar_Pervasives_Native.Some (b,c) ->
                      let uu____3975 =
                        let uu____3976 = FStar_Syntax_Util.is_total_comp c
                           in
                        Prims.op_Negation uu____3976  in
                      if uu____3975
                      then fail "Codomain is effectful"
                      else
                        (let uu____3996 =
                           new_uvar "apply arg" e
                             (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                            in
                         bind uu____3996
                           (fun uu____4022  ->
                              match uu____4022 with
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
      let uu____4108 =
        mlog
          (fun uu____4113  ->
             let uu____4114 = FStar_Syntax_Print.term_to_string tm  in
             FStar_Util.print1 "t_apply: tm = %s\n" uu____4114)
          (fun uu____4117  ->
             let uu____4118 = cur_goal ()  in
             bind uu____4118
               (fun goal  ->
                  let e = FStar_Tactics_Types.goal_env goal  in
                  let uu____4126 = __tc e tm  in
                  bind uu____4126
                    (fun uu____4147  ->
                       match uu____4147 with
                       | (tm1,typ,guard) ->
                           let typ1 = bnorm e typ  in
                           let uu____4160 =
                             let uu____4171 =
                               FStar_Tactics_Types.goal_type goal  in
                             try_match_by_application e typ1 uu____4171  in
                           bind uu____4160
                             (fun uvs  ->
                                let w =
                                  FStar_List.fold_right
                                    (fun uu____4214  ->
                                       fun w  ->
                                         match uu____4214 with
                                         | (uvt,q,uu____4232) ->
                                             FStar_Syntax_Util.mk_app w
                                               [(uvt, q)]) uvs tm1
                                   in
                                let uvset =
                                  let uu____4264 =
                                    FStar_Syntax_Free.new_uv_set ()  in
                                  FStar_List.fold_right
                                    (fun uu____4281  ->
                                       fun s  ->
                                         match uu____4281 with
                                         | (uu____4293,uu____4294,uv) ->
                                             let uu____4296 =
                                               FStar_Syntax_Free.uvars
                                                 uv.FStar_Syntax_Syntax.ctx_uvar_typ
                                                in
                                             FStar_Util.set_union s
                                               uu____4296) uvs uu____4264
                                   in
                                let free_in_some_goal uv =
                                  FStar_Util.set_mem uv uvset  in
                                let uu____4305 = solve' goal w  in
                                bind uu____4305
                                  (fun uu____4310  ->
                                     let uu____4311 =
                                       mapM
                                         (fun uu____4328  ->
                                            match uu____4328 with
                                            | (uvt,q,uv) ->
                                                let uu____4340 =
                                                  FStar_Syntax_Unionfind.find
                                                    uv.FStar_Syntax_Syntax.ctx_uvar_head
                                                   in
                                                (match uu____4340 with
                                                 | FStar_Pervasives_Native.Some
                                                     uu____4345 -> ret ()
                                                 | FStar_Pervasives_Native.None
                                                      ->
                                                     let uu____4346 =
                                                       uopt &&
                                                         (free_in_some_goal
                                                            uv)
                                                        in
                                                     if uu____4346
                                                     then ret ()
                                                     else
                                                       (let uu____4350 =
                                                          let uu____4353 =
                                                            bnorm_goal
                                                              (let uu___388_4356
                                                                 = goal  in
                                                               {
                                                                 FStar_Tactics_Types.goal_main_env
                                                                   =
                                                                   (uu___388_4356.FStar_Tactics_Types.goal_main_env);
                                                                 FStar_Tactics_Types.goal_ctx_uvar
                                                                   = uv;
                                                                 FStar_Tactics_Types.opts
                                                                   =
                                                                   (uu___388_4356.FStar_Tactics_Types.opts);
                                                                 FStar_Tactics_Types.is_guard
                                                                   = false
                                                               })
                                                             in
                                                          [uu____4353]  in
                                                        add_goals uu____4350)))
                                         uvs
                                        in
                                     bind uu____4311
                                       (fun uu____4360  ->
                                          proc_guard "apply guard" e guard))))))
         in
      FStar_All.pipe_left (wrap_err "apply") uu____4108
  
let (lemma_or_sq :
  FStar_Syntax_Syntax.comp ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun c  ->
    let ct = FStar_Syntax_Util.comp_to_comp_typ_nouniv c  in
    let uu____4385 =
      FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
        FStar_Parser_Const.effect_Lemma_lid
       in
    if uu____4385
    then
      let uu____4392 =
        match ct.FStar_Syntax_Syntax.effect_args with
        | pre::post::uu____4407 ->
            ((FStar_Pervasives_Native.fst pre),
              (FStar_Pervasives_Native.fst post))
        | uu____4460 -> failwith "apply_lemma: impossible: not a lemma"  in
      match uu____4392 with
      | (pre,post) ->
          let post1 =
            let uu____4492 =
              let uu____4503 =
                FStar_Syntax_Syntax.as_arg FStar_Syntax_Util.exp_unit  in
              [uu____4503]  in
            FStar_Syntax_Util.mk_app post uu____4492  in
          FStar_Pervasives_Native.Some (pre, post1)
    else
      (let uu____4533 =
         FStar_Syntax_Util.is_pure_effect ct.FStar_Syntax_Syntax.effect_name
          in
       if uu____4533
       then
         let uu____4540 =
           FStar_Syntax_Util.un_squash ct.FStar_Syntax_Syntax.result_typ  in
         FStar_Util.map_opt uu____4540
           (fun post  -> (FStar_Syntax_Util.t_true, post))
       else FStar_Pervasives_Native.None)
  
let (apply_lemma : FStar_Syntax_Syntax.term -> unit tac) =
  fun tm  ->
    let uu____4573 =
      let uu____4576 =
        bind get
          (fun ps  ->
             mlog
               (fun uu____4583  ->
                  let uu____4584 = FStar_Syntax_Print.term_to_string tm  in
                  FStar_Util.print1 "apply_lemma: tm = %s\n" uu____4584)
               (fun uu____4588  ->
                  let is_unit_t t =
                    let uu____4595 =
                      let uu____4596 = FStar_Syntax_Subst.compress t  in
                      uu____4596.FStar_Syntax_Syntax.n  in
                    match uu____4595 with
                    | FStar_Syntax_Syntax.Tm_fvar fv when
                        FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.unit_lid
                        -> true
                    | uu____4600 -> false  in
                  let uu____4601 = cur_goal ()  in
                  bind uu____4601
                    (fun goal  ->
                       let uu____4607 =
                         let uu____4616 = FStar_Tactics_Types.goal_env goal
                            in
                         __tc uu____4616 tm  in
                       bind uu____4607
                         (fun uu____4631  ->
                            match uu____4631 with
                            | (tm1,t,guard) ->
                                let uu____4643 =
                                  FStar_Syntax_Util.arrow_formals_comp t  in
                                (match uu____4643 with
                                 | (bs,comp) ->
                                     let uu____4676 = lemma_or_sq comp  in
                                     (match uu____4676 with
                                      | FStar_Pervasives_Native.None  ->
                                          fail
                                            "not a lemma or squashed function"
                                      | FStar_Pervasives_Native.Some
                                          (pre,post) ->
                                          let uu____4695 =
                                            FStar_List.fold_left
                                              (fun uu____4743  ->
                                                 fun uu____4744  ->
                                                   match (uu____4743,
                                                           uu____4744)
                                                   with
                                                   | ((uvs,guard1,subst1),
                                                      (b,aq)) ->
                                                       let b_t =
                                                         FStar_Syntax_Subst.subst
                                                           subst1
                                                           b.FStar_Syntax_Syntax.sort
                                                          in
                                                       let uu____4857 =
                                                         is_unit_t b_t  in
                                                       if uu____4857
                                                       then
                                                         (((FStar_Syntax_Util.exp_unit,
                                                             aq) :: uvs),
                                                           guard1,
                                                           ((FStar_Syntax_Syntax.NT
                                                               (b,
                                                                 FStar_Syntax_Util.exp_unit))
                                                           :: subst1))
                                                       else
                                                         (let uu____4895 =
                                                            let uu____4908 =
                                                              let uu____4909
                                                                =
                                                                FStar_Tactics_Types.goal_type
                                                                  goal
                                                                 in
                                                              uu____4909.FStar_Syntax_Syntax.pos
                                                               in
                                                            let uu____4912 =
                                                              FStar_Tactics_Types.goal_env
                                                                goal
                                                               in
                                                            FStar_TypeChecker_Util.new_implicit_var
                                                              "apply_lemma"
                                                              uu____4908
                                                              uu____4912 b_t
                                                             in
                                                          match uu____4895
                                                          with
                                                          | (u,uu____4930,g_u)
                                                              ->
                                                              let uu____4944
                                                                =
                                                                FStar_TypeChecker_Env.conj_guard
                                                                  guard1 g_u
                                                                 in
                                                              (((u, aq) ::
                                                                uvs),
                                                                uu____4944,
                                                                ((FStar_Syntax_Syntax.NT
                                                                    (b, u))
                                                                :: subst1))))
                                              ([], guard, []) bs
                                             in
                                          (match uu____4695 with
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
                                               let uu____5023 =
                                                 let uu____5026 =
                                                   FStar_Tactics_Types.goal_env
                                                     goal
                                                    in
                                                 let uu____5027 =
                                                   FStar_Syntax_Util.mk_squash
                                                     FStar_Syntax_Syntax.U_zero
                                                     post1
                                                    in
                                                 let uu____5028 =
                                                   FStar_Tactics_Types.goal_type
                                                     goal
                                                    in
                                                 do_unify uu____5026
                                                   uu____5027 uu____5028
                                                  in
                                               bind uu____5023
                                                 (fun b  ->
                                                    if Prims.op_Negation b
                                                    then
                                                      let uu____5036 =
                                                        let uu____5037 =
                                                          FStar_Tactics_Types.goal_env
                                                            goal
                                                           in
                                                        tts uu____5037 tm1
                                                         in
                                                      let uu____5038 =
                                                        let uu____5039 =
                                                          FStar_Tactics_Types.goal_env
                                                            goal
                                                           in
                                                        let uu____5040 =
                                                          FStar_Syntax_Util.mk_squash
                                                            FStar_Syntax_Syntax.U_zero
                                                            post1
                                                           in
                                                        tts uu____5039
                                                          uu____5040
                                                         in
                                                      let uu____5041 =
                                                        let uu____5042 =
                                                          FStar_Tactics_Types.goal_env
                                                            goal
                                                           in
                                                        let uu____5043 =
                                                          FStar_Tactics_Types.goal_type
                                                            goal
                                                           in
                                                        tts uu____5042
                                                          uu____5043
                                                         in
                                                      fail3
                                                        "Cannot instantiate lemma %s (with postcondition: %s) to match goal (%s)"
                                                        uu____5036 uu____5038
                                                        uu____5041
                                                    else
                                                      (let uu____5045 =
                                                         add_implicits
                                                           implicits.FStar_TypeChecker_Env.implicits
                                                          in
                                                       bind uu____5045
                                                         (fun uu____5050  ->
                                                            let uu____5051 =
                                                              solve' goal
                                                                FStar_Syntax_Util.exp_unit
                                                               in
                                                            bind uu____5051
                                                              (fun uu____5059
                                                                  ->
                                                                 let is_free_uvar
                                                                   uv t1 =
                                                                   let free_uvars
                                                                    =
                                                                    let uu____5084
                                                                    =
                                                                    let uu____5087
                                                                    =
                                                                    FStar_Syntax_Free.uvars
                                                                    t1  in
                                                                    FStar_Util.set_elements
                                                                    uu____5087
                                                                     in
                                                                    FStar_List.map
                                                                    (fun x 
                                                                    ->
                                                                    x.FStar_Syntax_Syntax.ctx_uvar_head)
                                                                    uu____5084
                                                                     in
                                                                   FStar_List.existsML
                                                                    (fun u 
                                                                    ->
                                                                    FStar_Syntax_Unionfind.equiv
                                                                    u uv)
                                                                    free_uvars
                                                                    in
                                                                 let appears
                                                                   uv goals1
                                                                   =
                                                                   FStar_List.existsML
                                                                    (fun g' 
                                                                    ->
                                                                    let uu____5122
                                                                    =
                                                                    FStar_Tactics_Types.goal_type
                                                                    g'  in
                                                                    is_free_uvar
                                                                    uv
                                                                    uu____5122)
                                                                    goals1
                                                                    in
                                                                 let checkone
                                                                   t1 goals1
                                                                   =
                                                                   let uu____5138
                                                                    =
                                                                    FStar_Syntax_Util.head_and_args
                                                                    t1  in
                                                                   match uu____5138
                                                                   with
                                                                   | 
                                                                   (hd1,uu____5156)
                                                                    ->
                                                                    (match 
                                                                    hd1.FStar_Syntax_Syntax.n
                                                                    with
                                                                    | 
                                                                    FStar_Syntax_Syntax.Tm_uvar
                                                                    (uv,uu____5182)
                                                                    ->
                                                                    appears
                                                                    uv.FStar_Syntax_Syntax.ctx_uvar_head
                                                                    goals1
                                                                    | 
                                                                    uu____5199
                                                                    -> false)
                                                                    in
                                                                 let uu____5200
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
                                                                    let uu____5230
                                                                    =
                                                                    FStar_Syntax_Util.head_and_args
                                                                    term  in
                                                                    match uu____5230
                                                                    with
                                                                    | 
                                                                    (hd1,uu____5252)
                                                                    ->
                                                                    let uu____5277
                                                                    =
                                                                    let uu____5278
                                                                    =
                                                                    FStar_Syntax_Subst.compress
                                                                    hd1  in
                                                                    uu____5278.FStar_Syntax_Syntax.n
                                                                     in
                                                                    (match uu____5277
                                                                    with
                                                                    | 
                                                                    FStar_Syntax_Syntax.Tm_uvar
                                                                    (ctx_uvar1,uu____5286)
                                                                    ->
                                                                    let goal1
                                                                    =
                                                                    bnorm_goal
                                                                    (let uu___389_5306
                                                                    = goal
                                                                     in
                                                                    {
                                                                    FStar_Tactics_Types.goal_main_env
                                                                    =
                                                                    (uu___389_5306.FStar_Tactics_Types.goal_main_env);
                                                                    FStar_Tactics_Types.goal_ctx_uvar
                                                                    =
                                                                    ctx_uvar1;
                                                                    FStar_Tactics_Types.opts
                                                                    =
                                                                    (uu___389_5306.FStar_Tactics_Types.opts);
                                                                    FStar_Tactics_Types.is_guard
                                                                    =
                                                                    (uu___389_5306.FStar_Tactics_Types.is_guard)
                                                                    })  in
                                                                    ret
                                                                    [goal1]
                                                                    | 
                                                                    uu____5309
                                                                    ->
                                                                    mlog
                                                                    (fun
                                                                    uu____5315
                                                                     ->
                                                                    let uu____5316
                                                                    =
                                                                    FStar_Syntax_Print.uvar_to_string
                                                                    ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_head
                                                                     in
                                                                    let uu____5317
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    term  in
                                                                    FStar_Util.print2
                                                                    "apply_lemma: arg %s unified to (%s)\n"
                                                                    uu____5316
                                                                    uu____5317)
                                                                    (fun
                                                                    uu____5322
                                                                     ->
                                                                    let env =
                                                                    let uu___390_5324
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    goal  in
                                                                    {
                                                                    FStar_TypeChecker_Env.solver
                                                                    =
                                                                    (uu___390_5324.FStar_TypeChecker_Env.solver);
                                                                    FStar_TypeChecker_Env.range
                                                                    =
                                                                    (uu___390_5324.FStar_TypeChecker_Env.range);
                                                                    FStar_TypeChecker_Env.curmodule
                                                                    =
                                                                    (uu___390_5324.FStar_TypeChecker_Env.curmodule);
                                                                    FStar_TypeChecker_Env.gamma
                                                                    =
                                                                    (ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_gamma);
                                                                    FStar_TypeChecker_Env.gamma_sig
                                                                    =
                                                                    (uu___390_5324.FStar_TypeChecker_Env.gamma_sig);
                                                                    FStar_TypeChecker_Env.gamma_cache
                                                                    =
                                                                    (uu___390_5324.FStar_TypeChecker_Env.gamma_cache);
                                                                    FStar_TypeChecker_Env.modules
                                                                    =
                                                                    (uu___390_5324.FStar_TypeChecker_Env.modules);
                                                                    FStar_TypeChecker_Env.expected_typ
                                                                    =
                                                                    (uu___390_5324.FStar_TypeChecker_Env.expected_typ);
                                                                    FStar_TypeChecker_Env.sigtab
                                                                    =
                                                                    (uu___390_5324.FStar_TypeChecker_Env.sigtab);
                                                                    FStar_TypeChecker_Env.attrtab
                                                                    =
                                                                    (uu___390_5324.FStar_TypeChecker_Env.attrtab);
                                                                    FStar_TypeChecker_Env.is_pattern
                                                                    =
                                                                    (uu___390_5324.FStar_TypeChecker_Env.is_pattern);
                                                                    FStar_TypeChecker_Env.instantiate_imp
                                                                    =
                                                                    (uu___390_5324.FStar_TypeChecker_Env.instantiate_imp);
                                                                    FStar_TypeChecker_Env.effects
                                                                    =
                                                                    (uu___390_5324.FStar_TypeChecker_Env.effects);
                                                                    FStar_TypeChecker_Env.generalize
                                                                    =
                                                                    (uu___390_5324.FStar_TypeChecker_Env.generalize);
                                                                    FStar_TypeChecker_Env.letrecs
                                                                    =
                                                                    (uu___390_5324.FStar_TypeChecker_Env.letrecs);
                                                                    FStar_TypeChecker_Env.top_level
                                                                    =
                                                                    (uu___390_5324.FStar_TypeChecker_Env.top_level);
                                                                    FStar_TypeChecker_Env.check_uvars
                                                                    =
                                                                    (uu___390_5324.FStar_TypeChecker_Env.check_uvars);
                                                                    FStar_TypeChecker_Env.use_eq
                                                                    =
                                                                    (uu___390_5324.FStar_TypeChecker_Env.use_eq);
                                                                    FStar_TypeChecker_Env.is_iface
                                                                    =
                                                                    (uu___390_5324.FStar_TypeChecker_Env.is_iface);
                                                                    FStar_TypeChecker_Env.admit
                                                                    =
                                                                    (uu___390_5324.FStar_TypeChecker_Env.admit);
                                                                    FStar_TypeChecker_Env.lax
                                                                    =
                                                                    (uu___390_5324.FStar_TypeChecker_Env.lax);
                                                                    FStar_TypeChecker_Env.lax_universes
                                                                    =
                                                                    (uu___390_5324.FStar_TypeChecker_Env.lax_universes);
                                                                    FStar_TypeChecker_Env.phase1
                                                                    =
                                                                    (uu___390_5324.FStar_TypeChecker_Env.phase1);
                                                                    FStar_TypeChecker_Env.failhard
                                                                    =
                                                                    (uu___390_5324.FStar_TypeChecker_Env.failhard);
                                                                    FStar_TypeChecker_Env.nosynth
                                                                    =
                                                                    (uu___390_5324.FStar_TypeChecker_Env.nosynth);
                                                                    FStar_TypeChecker_Env.uvar_subtyping
                                                                    =
                                                                    (uu___390_5324.FStar_TypeChecker_Env.uvar_subtyping);
                                                                    FStar_TypeChecker_Env.tc_term
                                                                    =
                                                                    (uu___390_5324.FStar_TypeChecker_Env.tc_term);
                                                                    FStar_TypeChecker_Env.type_of
                                                                    =
                                                                    (uu___390_5324.FStar_TypeChecker_Env.type_of);
                                                                    FStar_TypeChecker_Env.universe_of
                                                                    =
                                                                    (uu___390_5324.FStar_TypeChecker_Env.universe_of);
                                                                    FStar_TypeChecker_Env.check_type_of
                                                                    =
                                                                    (uu___390_5324.FStar_TypeChecker_Env.check_type_of);
                                                                    FStar_TypeChecker_Env.use_bv_sorts
                                                                    =
                                                                    (uu___390_5324.FStar_TypeChecker_Env.use_bv_sorts);
                                                                    FStar_TypeChecker_Env.qtbl_name_and_index
                                                                    =
                                                                    (uu___390_5324.FStar_TypeChecker_Env.qtbl_name_and_index);
                                                                    FStar_TypeChecker_Env.normalized_eff_names
                                                                    =
                                                                    (uu___390_5324.FStar_TypeChecker_Env.normalized_eff_names);
                                                                    FStar_TypeChecker_Env.proof_ns
                                                                    =
                                                                    (uu___390_5324.FStar_TypeChecker_Env.proof_ns);
                                                                    FStar_TypeChecker_Env.synth_hook
                                                                    =
                                                                    (uu___390_5324.FStar_TypeChecker_Env.synth_hook);
                                                                    FStar_TypeChecker_Env.splice
                                                                    =
                                                                    (uu___390_5324.FStar_TypeChecker_Env.splice);
                                                                    FStar_TypeChecker_Env.is_native_tactic
                                                                    =
                                                                    (uu___390_5324.FStar_TypeChecker_Env.is_native_tactic);
                                                                    FStar_TypeChecker_Env.identifier_info
                                                                    =
                                                                    (uu___390_5324.FStar_TypeChecker_Env.identifier_info);
                                                                    FStar_TypeChecker_Env.tc_hooks
                                                                    =
                                                                    (uu___390_5324.FStar_TypeChecker_Env.tc_hooks);
                                                                    FStar_TypeChecker_Env.dsenv
                                                                    =
                                                                    (uu___390_5324.FStar_TypeChecker_Env.dsenv);
                                                                    FStar_TypeChecker_Env.dep_graph
                                                                    =
                                                                    (uu___390_5324.FStar_TypeChecker_Env.dep_graph);
                                                                    FStar_TypeChecker_Env.nbe
                                                                    =
                                                                    (uu___390_5324.FStar_TypeChecker_Env.nbe)
                                                                    }  in
                                                                    let g_typ
                                                                    =
                                                                    FStar_TypeChecker_TcTerm.check_type_of_well_typed_term'
                                                                    true env
                                                                    term
                                                                    ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_typ
                                                                     in
                                                                    let uu____5326
                                                                    =
                                                                    let uu____5329
                                                                    =
                                                                    if
                                                                    ps.FStar_Tactics_Types.tac_verb_dbg
                                                                    then
                                                                    let uu____5330
                                                                    =
                                                                    FStar_Syntax_Print.ctx_uvar_to_string
                                                                    ctx_uvar
                                                                     in
                                                                    let uu____5331
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    term  in
                                                                    FStar_Util.format2
                                                                    "apply_lemma solved arg %s to %s\n"
                                                                    uu____5330
                                                                    uu____5331
                                                                    else
                                                                    "apply_lemma solved arg"
                                                                     in
                                                                    let uu____5333
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    goal  in
                                                                    proc_guard
                                                                    uu____5329
                                                                    uu____5333
                                                                    g_typ  in
                                                                    bind
                                                                    uu____5326
                                                                    (fun
                                                                    uu____5337
                                                                     ->
                                                                    ret [])))))
                                                                    in
                                                                 bind
                                                                   uu____5200
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
                                                                    let uu____5399
                                                                    = f x xs1
                                                                     in
                                                                    if
                                                                    uu____5399
                                                                    then
                                                                    let uu____5402
                                                                    =
                                                                    filter' f
                                                                    xs1  in x
                                                                    ::
                                                                    uu____5402
                                                                    else
                                                                    filter' f
                                                                    xs1  in
                                                                    let sub_goals2
                                                                    =
                                                                    filter'
                                                                    (fun g 
                                                                    ->
                                                                    fun
                                                                    goals1 
                                                                    ->
                                                                    let uu____5416
                                                                    =
                                                                    let uu____5417
                                                                    =
                                                                    FStar_Tactics_Types.goal_witness
                                                                    g  in
                                                                    checkone
                                                                    uu____5417
                                                                    goals1
                                                                     in
                                                                    Prims.op_Negation
                                                                    uu____5416)
                                                                    sub_goals1
                                                                     in
                                                                    let uu____5418
                                                                    =
                                                                    let uu____5421
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    goal  in
                                                                    proc_guard
                                                                    "apply_lemma guard"
                                                                    uu____5421
                                                                    guard  in
                                                                    bind
                                                                    uu____5418
                                                                    (fun
                                                                    uu____5424
                                                                     ->
                                                                    let uu____5425
                                                                    =
                                                                    let uu____5428
                                                                    =
                                                                    let uu____5429
                                                                    =
                                                                    let uu____5430
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    goal  in
                                                                    let uu____5431
                                                                    =
                                                                    FStar_Syntax_Util.mk_squash
                                                                    FStar_Syntax_Syntax.U_zero
                                                                    pre1  in
                                                                    istrivial
                                                                    uu____5430
                                                                    uu____5431
                                                                     in
                                                                    Prims.op_Negation
                                                                    uu____5429
                                                                     in
                                                                    if
                                                                    uu____5428
                                                                    then
                                                                    let uu____5434
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    goal  in
                                                                    add_irrelevant_goal
                                                                    "apply_lemma precondition"
                                                                    uu____5434
                                                                    pre1
                                                                    goal.FStar_Tactics_Types.opts
                                                                    else
                                                                    ret ()
                                                                     in
                                                                    bind
                                                                    uu____5425
                                                                    (fun
                                                                    uu____5437
                                                                     ->
                                                                    add_goals
                                                                    sub_goals2))))))))))))))
         in
      focus uu____4576  in
    FStar_All.pipe_left (wrap_err "apply_lemma") uu____4573
  
let (destruct_eq' :
  FStar_Reflection_Data.typ ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun typ  ->
    let uu____5459 = FStar_Syntax_Util.destruct_typ_as_formula typ  in
    match uu____5459 with
    | FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn
        (l,uu____5469::(e1,uu____5471)::(e2,uu____5473)::[])) when
        FStar_Ident.lid_equals l FStar_Parser_Const.eq2_lid ->
        FStar_Pervasives_Native.Some (e1, e2)
    | uu____5534 -> FStar_Pervasives_Native.None
  
let (destruct_eq :
  FStar_Reflection_Data.typ ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun typ  ->
    let uu____5558 = destruct_eq' typ  in
    match uu____5558 with
    | FStar_Pervasives_Native.Some t -> FStar_Pervasives_Native.Some t
    | FStar_Pervasives_Native.None  ->
        let uu____5588 = FStar_Syntax_Util.un_squash typ  in
        (match uu____5588 with
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
        let uu____5650 = FStar_TypeChecker_Env.pop_bv e1  in
        match uu____5650 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (bv',e') ->
            if FStar_Syntax_Syntax.bv_eq bvar bv'
            then FStar_Pervasives_Native.Some (e', [])
            else
              (let uu____5698 = aux e'  in
               FStar_Util.map_opt uu____5698
                 (fun uu____5722  ->
                    match uu____5722 with | (e'',bvs) -> (e'', (bv' :: bvs))))
         in
      let uu____5743 = aux e  in
      FStar_Util.map_opt uu____5743
        (fun uu____5767  ->
           match uu____5767 with | (e',bvs) -> (e', (FStar_List.rev bvs)))
  
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
          let uu____5834 =
            let uu____5843 = FStar_Tactics_Types.goal_env g  in
            split_env b1 uu____5843  in
          FStar_Util.map_opt uu____5834
            (fun uu____5858  ->
               match uu____5858 with
               | (e0,bvs) ->
                   let s1 bv =
                     let uu___391_5877 = bv  in
                     let uu____5878 =
                       FStar_Syntax_Subst.subst s bv.FStar_Syntax_Syntax.sort
                        in
                     {
                       FStar_Syntax_Syntax.ppname =
                         (uu___391_5877.FStar_Syntax_Syntax.ppname);
                       FStar_Syntax_Syntax.index =
                         (uu___391_5877.FStar_Syntax_Syntax.index);
                       FStar_Syntax_Syntax.sort = uu____5878
                     }  in
                   let bvs1 = FStar_List.map s1 bvs  in
                   let new_env = push_bvs e0 (b2 :: bvs1)  in
                   let new_goal =
                     let uu___392_5886 = g.FStar_Tactics_Types.goal_ctx_uvar
                        in
                     let uu____5887 =
                       FStar_TypeChecker_Env.all_binders new_env  in
                     let uu____5896 =
                       let uu____5899 = FStar_Tactics_Types.goal_type g  in
                       FStar_Syntax_Subst.subst s uu____5899  in
                     {
                       FStar_Syntax_Syntax.ctx_uvar_head =
                         (uu___392_5886.FStar_Syntax_Syntax.ctx_uvar_head);
                       FStar_Syntax_Syntax.ctx_uvar_gamma =
                         (new_env.FStar_TypeChecker_Env.gamma);
                       FStar_Syntax_Syntax.ctx_uvar_binders = uu____5887;
                       FStar_Syntax_Syntax.ctx_uvar_typ = uu____5896;
                       FStar_Syntax_Syntax.ctx_uvar_reason =
                         (uu___392_5886.FStar_Syntax_Syntax.ctx_uvar_reason);
                       FStar_Syntax_Syntax.ctx_uvar_should_check =
                         (uu___392_5886.FStar_Syntax_Syntax.ctx_uvar_should_check);
                       FStar_Syntax_Syntax.ctx_uvar_range =
                         (uu___392_5886.FStar_Syntax_Syntax.ctx_uvar_range)
                     }  in
                   let uu___393_5900 = g  in
                   {
                     FStar_Tactics_Types.goal_main_env =
                       (uu___393_5900.FStar_Tactics_Types.goal_main_env);
                     FStar_Tactics_Types.goal_ctx_uvar = new_goal;
                     FStar_Tactics_Types.opts =
                       (uu___393_5900.FStar_Tactics_Types.opts);
                     FStar_Tactics_Types.is_guard =
                       (uu___393_5900.FStar_Tactics_Types.is_guard)
                   })
  
let (rewrite : FStar_Syntax_Syntax.binder -> unit tac) =
  fun h  ->
    let uu____5910 =
      let uu____5913 = cur_goal ()  in
      bind uu____5913
        (fun goal  ->
           let uu____5921 = h  in
           match uu____5921 with
           | (bv,uu____5925) ->
               mlog
                 (fun uu____5933  ->
                    let uu____5934 = FStar_Syntax_Print.bv_to_string bv  in
                    let uu____5935 =
                      FStar_Syntax_Print.term_to_string
                        bv.FStar_Syntax_Syntax.sort
                       in
                    FStar_Util.print2 "+++Rewrite %s : %s\n" uu____5934
                      uu____5935)
                 (fun uu____5938  ->
                    let uu____5939 =
                      let uu____5948 = FStar_Tactics_Types.goal_env goal  in
                      split_env bv uu____5948  in
                    match uu____5939 with
                    | FStar_Pervasives_Native.None  ->
                        fail "binder not found in environment"
                    | FStar_Pervasives_Native.Some (e0,bvs) ->
                        let uu____5969 =
                          destruct_eq bv.FStar_Syntax_Syntax.sort  in
                        (match uu____5969 with
                         | FStar_Pervasives_Native.Some (x,e) ->
                             let uu____5984 =
                               let uu____5985 = FStar_Syntax_Subst.compress x
                                  in
                               uu____5985.FStar_Syntax_Syntax.n  in
                             (match uu____5984 with
                              | FStar_Syntax_Syntax.Tm_name x1 ->
                                  let s = [FStar_Syntax_Syntax.NT (x1, e)]
                                     in
                                  let s1 bv1 =
                                    let uu___394_6002 = bv1  in
                                    let uu____6003 =
                                      FStar_Syntax_Subst.subst s
                                        bv1.FStar_Syntax_Syntax.sort
                                       in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___394_6002.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___394_6002.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = uu____6003
                                    }  in
                                  let bvs1 = FStar_List.map s1 bvs  in
                                  let new_env = push_bvs e0 (bv :: bvs1)  in
                                  let new_goal =
                                    let uu___395_6011 =
                                      goal.FStar_Tactics_Types.goal_ctx_uvar
                                       in
                                    let uu____6012 =
                                      FStar_TypeChecker_Env.all_binders
                                        new_env
                                       in
                                    let uu____6021 =
                                      let uu____6024 =
                                        FStar_Tactics_Types.goal_type goal
                                         in
                                      FStar_Syntax_Subst.subst s uu____6024
                                       in
                                    {
                                      FStar_Syntax_Syntax.ctx_uvar_head =
                                        (uu___395_6011.FStar_Syntax_Syntax.ctx_uvar_head);
                                      FStar_Syntax_Syntax.ctx_uvar_gamma =
                                        (new_env.FStar_TypeChecker_Env.gamma);
                                      FStar_Syntax_Syntax.ctx_uvar_binders =
                                        uu____6012;
                                      FStar_Syntax_Syntax.ctx_uvar_typ =
                                        uu____6021;
                                      FStar_Syntax_Syntax.ctx_uvar_reason =
                                        (uu___395_6011.FStar_Syntax_Syntax.ctx_uvar_reason);
                                      FStar_Syntax_Syntax.ctx_uvar_should_check
                                        =
                                        (uu___395_6011.FStar_Syntax_Syntax.ctx_uvar_should_check);
                                      FStar_Syntax_Syntax.ctx_uvar_range =
                                        (uu___395_6011.FStar_Syntax_Syntax.ctx_uvar_range)
                                    }  in
                                  replace_cur
                                    (let uu___396_6027 = goal  in
                                     {
                                       FStar_Tactics_Types.goal_main_env =
                                         (uu___396_6027.FStar_Tactics_Types.goal_main_env);
                                       FStar_Tactics_Types.goal_ctx_uvar =
                                         new_goal;
                                       FStar_Tactics_Types.opts =
                                         (uu___396_6027.FStar_Tactics_Types.opts);
                                       FStar_Tactics_Types.is_guard =
                                         (uu___396_6027.FStar_Tactics_Types.is_guard)
                                     })
                              | uu____6028 ->
                                  fail
                                    "Not an equality hypothesis with a variable on the LHS")
                         | uu____6029 -> fail "Not an equality hypothesis")))
       in
    FStar_All.pipe_left (wrap_err "rewrite") uu____5910
  
let (rename_to : FStar_Syntax_Syntax.binder -> Prims.string -> unit tac) =
  fun b  ->
    fun s  ->
      let uu____6054 =
        let uu____6057 = cur_goal ()  in
        bind uu____6057
          (fun goal  ->
             let uu____6068 = b  in
             match uu____6068 with
             | (bv,uu____6072) ->
                 let bv' =
                   let uu____6078 =
                     let uu___397_6079 = bv  in
                     let uu____6080 =
                       FStar_Ident.mk_ident
                         (s,
                           ((bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange))
                        in
                     {
                       FStar_Syntax_Syntax.ppname = uu____6080;
                       FStar_Syntax_Syntax.index =
                         (uu___397_6079.FStar_Syntax_Syntax.index);
                       FStar_Syntax_Syntax.sort =
                         (uu___397_6079.FStar_Syntax_Syntax.sort)
                     }  in
                   FStar_Syntax_Syntax.freshen_bv uu____6078  in
                 let s1 =
                   let uu____6084 =
                     let uu____6085 =
                       let uu____6092 = FStar_Syntax_Syntax.bv_to_name bv'
                          in
                       (bv, uu____6092)  in
                     FStar_Syntax_Syntax.NT uu____6085  in
                   [uu____6084]  in
                 let uu____6097 = subst_goal bv bv' s1 goal  in
                 (match uu____6097 with
                  | FStar_Pervasives_Native.None  ->
                      fail "binder not found in environment"
                  | FStar_Pervasives_Native.Some goal1 -> replace_cur goal1))
         in
      FStar_All.pipe_left (wrap_err "rename_to") uu____6054
  
let (binder_retype : FStar_Syntax_Syntax.binder -> unit tac) =
  fun b  ->
    let uu____6116 =
      let uu____6119 = cur_goal ()  in
      bind uu____6119
        (fun goal  ->
           let uu____6128 = b  in
           match uu____6128 with
           | (bv,uu____6132) ->
               let uu____6137 =
                 let uu____6146 = FStar_Tactics_Types.goal_env goal  in
                 split_env bv uu____6146  in
               (match uu____6137 with
                | FStar_Pervasives_Native.None  ->
                    fail "binder is not present in environment"
                | FStar_Pervasives_Native.Some (e0,bvs) ->
                    let uu____6167 = FStar_Syntax_Util.type_u ()  in
                    (match uu____6167 with
                     | (ty,u) ->
                         let uu____6176 = new_uvar "binder_retype" e0 ty  in
                         bind uu____6176
                           (fun uu____6194  ->
                              match uu____6194 with
                              | (t',u_t') ->
                                  let bv'' =
                                    let uu___398_6204 = bv  in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___398_6204.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___398_6204.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = t'
                                    }  in
                                  let s =
                                    let uu____6208 =
                                      let uu____6209 =
                                        let uu____6216 =
                                          FStar_Syntax_Syntax.bv_to_name bv''
                                           in
                                        (bv, uu____6216)  in
                                      FStar_Syntax_Syntax.NT uu____6209  in
                                    [uu____6208]  in
                                  let bvs1 =
                                    FStar_List.map
                                      (fun b1  ->
                                         let uu___399_6228 = b1  in
                                         let uu____6229 =
                                           FStar_Syntax_Subst.subst s
                                             b1.FStar_Syntax_Syntax.sort
                                            in
                                         {
                                           FStar_Syntax_Syntax.ppname =
                                             (uu___399_6228.FStar_Syntax_Syntax.ppname);
                                           FStar_Syntax_Syntax.index =
                                             (uu___399_6228.FStar_Syntax_Syntax.index);
                                           FStar_Syntax_Syntax.sort =
                                             uu____6229
                                         }) bvs
                                     in
                                  let env' = push_bvs e0 (bv'' :: bvs1)  in
                                  bind __dismiss
                                    (fun uu____6236  ->
                                       let new_goal =
                                         let uu____6238 =
                                           FStar_Tactics_Types.goal_with_env
                                             goal env'
                                            in
                                         let uu____6239 =
                                           let uu____6240 =
                                             FStar_Tactics_Types.goal_type
                                               goal
                                              in
                                           FStar_Syntax_Subst.subst s
                                             uu____6240
                                            in
                                         FStar_Tactics_Types.goal_with_type
                                           uu____6238 uu____6239
                                          in
                                       let uu____6241 = add_goals [new_goal]
                                          in
                                       bind uu____6241
                                         (fun uu____6246  ->
                                            let uu____6247 =
                                              FStar_Syntax_Util.mk_eq2
                                                (FStar_Syntax_Syntax.U_succ u)
                                                ty
                                                bv.FStar_Syntax_Syntax.sort
                                                t'
                                               in
                                            add_irrelevant_goal
                                              "binder_retype equation" e0
                                              uu____6247
                                              goal.FStar_Tactics_Types.opts))))))
       in
    FStar_All.pipe_left (wrap_err "binder_retype") uu____6116
  
let (norm_binder_type :
  FStar_Syntax_Embeddings.norm_step Prims.list ->
    FStar_Syntax_Syntax.binder -> unit tac)
  =
  fun s  ->
    fun b  ->
      let uu____6270 =
        let uu____6273 = cur_goal ()  in
        bind uu____6273
          (fun goal  ->
             let uu____6282 = b  in
             match uu____6282 with
             | (bv,uu____6286) ->
                 let uu____6291 =
                   let uu____6300 = FStar_Tactics_Types.goal_env goal  in
                   split_env bv uu____6300  in
                 (match uu____6291 with
                  | FStar_Pervasives_Native.None  ->
                      fail "binder is not present in environment"
                  | FStar_Pervasives_Native.Some (e0,bvs) ->
                      let steps =
                        let uu____6324 =
                          FStar_TypeChecker_Normalize.tr_norm_steps s  in
                        FStar_List.append
                          [FStar_TypeChecker_Env.Reify;
                          FStar_TypeChecker_Env.UnfoldTac] uu____6324
                         in
                      let sort' =
                        normalize steps e0 bv.FStar_Syntax_Syntax.sort  in
                      let bv' =
                        let uu___400_6329 = bv  in
                        {
                          FStar_Syntax_Syntax.ppname =
                            (uu___400_6329.FStar_Syntax_Syntax.ppname);
                          FStar_Syntax_Syntax.index =
                            (uu___400_6329.FStar_Syntax_Syntax.index);
                          FStar_Syntax_Syntax.sort = sort'
                        }  in
                      let env' = push_bvs e0 (bv' :: bvs)  in
                      let uu____6331 =
                        FStar_Tactics_Types.goal_with_env goal env'  in
                      replace_cur uu____6331))
         in
      FStar_All.pipe_left (wrap_err "norm_binder_type") uu____6270
  
let (revert : unit -> unit tac) =
  fun uu____6342  ->
    let uu____6345 = cur_goal ()  in
    bind uu____6345
      (fun goal  ->
         let uu____6351 =
           let uu____6358 = FStar_Tactics_Types.goal_env goal  in
           FStar_TypeChecker_Env.pop_bv uu____6358  in
         match uu____6351 with
         | FStar_Pervasives_Native.None  ->
             fail "Cannot revert; empty context"
         | FStar_Pervasives_Native.Some (x,env') ->
             let typ' =
               let uu____6374 =
                 let uu____6377 = FStar_Tactics_Types.goal_type goal  in
                 FStar_Syntax_Syntax.mk_Total uu____6377  in
               FStar_Syntax_Util.arrow [(x, FStar_Pervasives_Native.None)]
                 uu____6374
                in
             let uu____6392 = new_uvar "revert" env' typ'  in
             bind uu____6392
               (fun uu____6407  ->
                  match uu____6407 with
                  | (r,u_r) ->
                      let uu____6416 =
                        let uu____6419 =
                          let uu____6420 =
                            let uu____6421 =
                              FStar_Tactics_Types.goal_type goal  in
                            uu____6421.FStar_Syntax_Syntax.pos  in
                          let uu____6424 =
                            let uu____6429 =
                              let uu____6430 =
                                let uu____6439 =
                                  FStar_Syntax_Syntax.bv_to_name x  in
                                FStar_Syntax_Syntax.as_arg uu____6439  in
                              [uu____6430]  in
                            FStar_Syntax_Syntax.mk_Tm_app r uu____6429  in
                          uu____6424 FStar_Pervasives_Native.None uu____6420
                           in
                        set_solution goal uu____6419  in
                      bind uu____6416
                        (fun uu____6460  ->
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
      let uu____6472 = FStar_Syntax_Free.names t  in
      FStar_Util.set_mem bv uu____6472
  
let rec (clear : FStar_Syntax_Syntax.binder -> unit tac) =
  fun b  ->
    let bv = FStar_Pervasives_Native.fst b  in
    let uu____6487 = cur_goal ()  in
    bind uu____6487
      (fun goal  ->
         mlog
           (fun uu____6495  ->
              let uu____6496 = FStar_Syntax_Print.binder_to_string b  in
              let uu____6497 =
                let uu____6498 =
                  let uu____6499 =
                    let uu____6508 = FStar_Tactics_Types.goal_env goal  in
                    FStar_TypeChecker_Env.all_binders uu____6508  in
                  FStar_All.pipe_right uu____6499 FStar_List.length  in
                FStar_All.pipe_right uu____6498 FStar_Util.string_of_int  in
              FStar_Util.print2 "Clear of (%s), env has %s binders\n"
                uu____6496 uu____6497)
           (fun uu____6525  ->
              let uu____6526 =
                let uu____6535 = FStar_Tactics_Types.goal_env goal  in
                split_env bv uu____6535  in
              match uu____6526 with
              | FStar_Pervasives_Native.None  ->
                  fail "Cannot clear; binder not in environment"
              | FStar_Pervasives_Native.Some (e',bvs) ->
                  let rec check1 bvs1 =
                    match bvs1 with
                    | [] -> ret ()
                    | bv'::bvs2 ->
                        let uu____6574 =
                          free_in bv bv'.FStar_Syntax_Syntax.sort  in
                        if uu____6574
                        then
                          let uu____6577 =
                            let uu____6578 =
                              FStar_Syntax_Print.bv_to_string bv'  in
                            FStar_Util.format1
                              "Cannot clear; binder present in the type of %s"
                              uu____6578
                             in
                          fail uu____6577
                        else check1 bvs2
                     in
                  let uu____6580 =
                    let uu____6581 = FStar_Tactics_Types.goal_type goal  in
                    free_in bv uu____6581  in
                  if uu____6580
                  then fail "Cannot clear; binder present in goal"
                  else
                    (let uu____6585 = check1 bvs  in
                     bind uu____6585
                       (fun uu____6591  ->
                          let env' = push_bvs e' bvs  in
                          let uu____6593 =
                            let uu____6600 =
                              FStar_Tactics_Types.goal_type goal  in
                            new_uvar "clear.witness" env' uu____6600  in
                          bind uu____6593
                            (fun uu____6609  ->
                               match uu____6609 with
                               | (ut,uvar_ut) ->
                                   let uu____6618 = set_solution goal ut  in
                                   bind uu____6618
                                     (fun uu____6623  ->
                                        let uu____6624 =
                                          FStar_Tactics_Types.mk_goal env'
                                            uvar_ut
                                            goal.FStar_Tactics_Types.opts
                                            goal.FStar_Tactics_Types.is_guard
                                           in
                                        replace_cur uu____6624))))))
  
let (clear_top : unit -> unit tac) =
  fun uu____6631  ->
    let uu____6634 = cur_goal ()  in
    bind uu____6634
      (fun goal  ->
         let uu____6640 =
           let uu____6647 = FStar_Tactics_Types.goal_env goal  in
           FStar_TypeChecker_Env.pop_bv uu____6647  in
         match uu____6640 with
         | FStar_Pervasives_Native.None  ->
             fail "Cannot clear; empty context"
         | FStar_Pervasives_Native.Some (x,uu____6655) ->
             let uu____6660 = FStar_Syntax_Syntax.mk_binder x  in
             clear uu____6660)
  
let (prune : Prims.string -> unit tac) =
  fun s  ->
    let uu____6670 = cur_goal ()  in
    bind uu____6670
      (fun g  ->
         let ctx = FStar_Tactics_Types.goal_env g  in
         let ctx' =
           let uu____6680 = FStar_Ident.path_of_text s  in
           FStar_TypeChecker_Env.rem_proof_ns ctx uu____6680  in
         let g' = FStar_Tactics_Types.goal_with_env g ctx'  in
         bind __dismiss (fun uu____6683  -> add_goals [g']))
  
let (addns : Prims.string -> unit tac) =
  fun s  ->
    let uu____6693 = cur_goal ()  in
    bind uu____6693
      (fun g  ->
         let ctx = FStar_Tactics_Types.goal_env g  in
         let ctx' =
           let uu____6703 = FStar_Ident.path_of_text s  in
           FStar_TypeChecker_Env.add_proof_ns ctx uu____6703  in
         let g' = FStar_Tactics_Types.goal_with_env g ctx'  in
         bind __dismiss (fun uu____6706  -> add_goals [g']))
  
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
            let uu____6746 = FStar_Syntax_Subst.compress t  in
            uu____6746.FStar_Syntax_Syntax.n  in
          let uu____6749 =
            if d = FStar_Tactics_Types.TopDown
            then
              f env
                (let uu___404_6755 = t  in
                 {
                   FStar_Syntax_Syntax.n = tn;
                   FStar_Syntax_Syntax.pos =
                     (uu___404_6755.FStar_Syntax_Syntax.pos);
                   FStar_Syntax_Syntax.vars =
                     (uu___404_6755.FStar_Syntax_Syntax.vars)
                 })
            else ret t  in
          bind uu____6749
            (fun t1  ->
               let ff = tac_fold_env d f env  in
               let tn1 =
                 let uu____6771 =
                   let uu____6772 = FStar_Syntax_Subst.compress t1  in
                   uu____6772.FStar_Syntax_Syntax.n  in
                 match uu____6771 with
                 | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
                     let uu____6803 = ff hd1  in
                     bind uu____6803
                       (fun hd2  ->
                          let fa uu____6829 =
                            match uu____6829 with
                            | (a,q) ->
                                let uu____6850 = ff a  in
                                bind uu____6850 (fun a1  -> ret (a1, q))
                             in
                          let uu____6869 = mapM fa args  in
                          bind uu____6869
                            (fun args1  ->
                               ret (FStar_Syntax_Syntax.Tm_app (hd2, args1))))
                 | FStar_Syntax_Syntax.Tm_abs (bs,t2,k) ->
                     let uu____6951 = FStar_Syntax_Subst.open_term bs t2  in
                     (match uu____6951 with
                      | (bs1,t') ->
                          let uu____6960 =
                            let uu____6963 =
                              FStar_TypeChecker_Env.push_binders env bs1  in
                            tac_fold_env d f uu____6963 t'  in
                          bind uu____6960
                            (fun t''  ->
                               let uu____6967 =
                                 let uu____6968 =
                                   let uu____6987 =
                                     FStar_Syntax_Subst.close_binders bs1  in
                                   let uu____6996 =
                                     FStar_Syntax_Subst.close bs1 t''  in
                                   (uu____6987, uu____6996, k)  in
                                 FStar_Syntax_Syntax.Tm_abs uu____6968  in
                               ret uu____6967))
                 | FStar_Syntax_Syntax.Tm_arrow (bs,k) -> ret tn
                 | FStar_Syntax_Syntax.Tm_match (hd1,brs) ->
                     let uu____7071 = ff hd1  in
                     bind uu____7071
                       (fun hd2  ->
                          let ffb br =
                            let uu____7086 =
                              FStar_Syntax_Subst.open_branch br  in
                            match uu____7086 with
                            | (pat,w,e) ->
                                let bvs = FStar_Syntax_Syntax.pat_bvs pat  in
                                let ff1 =
                                  let uu____7118 =
                                    FStar_TypeChecker_Env.push_bvs env bvs
                                     in
                                  tac_fold_env d f uu____7118  in
                                let uu____7119 = ff1 e  in
                                bind uu____7119
                                  (fun e1  ->
                                     let br1 =
                                       FStar_Syntax_Subst.close_branch
                                         (pat, w, e1)
                                        in
                                     ret br1)
                             in
                          let uu____7134 = mapM ffb brs  in
                          bind uu____7134
                            (fun brs1  ->
                               ret (FStar_Syntax_Syntax.Tm_match (hd2, brs1))))
                 | FStar_Syntax_Syntax.Tm_let
                     ((false
                       ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inl bv;
                          FStar_Syntax_Syntax.lbunivs = uu____7178;
                          FStar_Syntax_Syntax.lbtyp = uu____7179;
                          FStar_Syntax_Syntax.lbeff = uu____7180;
                          FStar_Syntax_Syntax.lbdef = def;
                          FStar_Syntax_Syntax.lbattrs = uu____7182;
                          FStar_Syntax_Syntax.lbpos = uu____7183;_}::[]),e)
                     ->
                     let lb =
                       let uu____7208 =
                         let uu____7209 = FStar_Syntax_Subst.compress t1  in
                         uu____7209.FStar_Syntax_Syntax.n  in
                       match uu____7208 with
                       | FStar_Syntax_Syntax.Tm_let
                           ((false ,lb::[]),uu____7213) -> lb
                       | uu____7226 -> failwith "impossible"  in
                     let fflb lb1 =
                       let uu____7235 = ff lb1.FStar_Syntax_Syntax.lbdef  in
                       bind uu____7235
                         (fun def1  ->
                            ret
                              (let uu___401_7241 = lb1  in
                               {
                                 FStar_Syntax_Syntax.lbname =
                                   (uu___401_7241.FStar_Syntax_Syntax.lbname);
                                 FStar_Syntax_Syntax.lbunivs =
                                   (uu___401_7241.FStar_Syntax_Syntax.lbunivs);
                                 FStar_Syntax_Syntax.lbtyp =
                                   (uu___401_7241.FStar_Syntax_Syntax.lbtyp);
                                 FStar_Syntax_Syntax.lbeff =
                                   (uu___401_7241.FStar_Syntax_Syntax.lbeff);
                                 FStar_Syntax_Syntax.lbdef = def1;
                                 FStar_Syntax_Syntax.lbattrs =
                                   (uu___401_7241.FStar_Syntax_Syntax.lbattrs);
                                 FStar_Syntax_Syntax.lbpos =
                                   (uu___401_7241.FStar_Syntax_Syntax.lbpos)
                               }))
                        in
                     let uu____7242 = fflb lb  in
                     bind uu____7242
                       (fun lb1  ->
                          let uu____7252 =
                            let uu____7257 =
                              let uu____7258 =
                                FStar_Syntax_Syntax.mk_binder bv  in
                              [uu____7258]  in
                            FStar_Syntax_Subst.open_term uu____7257 e  in
                          match uu____7252 with
                          | (bs,e1) ->
                              let ff1 =
                                let uu____7288 =
                                  FStar_TypeChecker_Env.push_binders env bs
                                   in
                                tac_fold_env d f uu____7288  in
                              let uu____7289 = ff1 e1  in
                              bind uu____7289
                                (fun e2  ->
                                   let e3 = FStar_Syntax_Subst.close bs e2
                                      in
                                   ret
                                     (FStar_Syntax_Syntax.Tm_let
                                        ((false, [lb1]), e3))))
                 | FStar_Syntax_Syntax.Tm_let ((true ,lbs),e) ->
                     let fflb lb =
                       let uu____7330 = ff lb.FStar_Syntax_Syntax.lbdef  in
                       bind uu____7330
                         (fun def  ->
                            ret
                              (let uu___402_7336 = lb  in
                               {
                                 FStar_Syntax_Syntax.lbname =
                                   (uu___402_7336.FStar_Syntax_Syntax.lbname);
                                 FStar_Syntax_Syntax.lbunivs =
                                   (uu___402_7336.FStar_Syntax_Syntax.lbunivs);
                                 FStar_Syntax_Syntax.lbtyp =
                                   (uu___402_7336.FStar_Syntax_Syntax.lbtyp);
                                 FStar_Syntax_Syntax.lbeff =
                                   (uu___402_7336.FStar_Syntax_Syntax.lbeff);
                                 FStar_Syntax_Syntax.lbdef = def;
                                 FStar_Syntax_Syntax.lbattrs =
                                   (uu___402_7336.FStar_Syntax_Syntax.lbattrs);
                                 FStar_Syntax_Syntax.lbpos =
                                   (uu___402_7336.FStar_Syntax_Syntax.lbpos)
                               }))
                        in
                     let uu____7337 = FStar_Syntax_Subst.open_let_rec lbs e
                        in
                     (match uu____7337 with
                      | (lbs1,e1) ->
                          let uu____7352 = mapM fflb lbs1  in
                          bind uu____7352
                            (fun lbs2  ->
                               let uu____7364 = ff e1  in
                               bind uu____7364
                                 (fun e2  ->
                                    let uu____7372 =
                                      FStar_Syntax_Subst.close_let_rec lbs2
                                        e2
                                       in
                                    match uu____7372 with
                                    | (lbs3,e3) ->
                                        ret
                                          (FStar_Syntax_Syntax.Tm_let
                                             ((true, lbs3), e3)))))
                 | FStar_Syntax_Syntax.Tm_ascribed (t2,asc,eff) ->
                     let uu____7440 = ff t2  in
                     bind uu____7440
                       (fun t3  ->
                          ret
                            (FStar_Syntax_Syntax.Tm_ascribed (t3, asc, eff)))
                 | FStar_Syntax_Syntax.Tm_meta (t2,m) ->
                     let uu____7471 = ff t2  in
                     bind uu____7471
                       (fun t3  -> ret (FStar_Syntax_Syntax.Tm_meta (t3, m)))
                 | uu____7478 -> ret tn  in
               bind tn1
                 (fun tn2  ->
                    let t' =
                      let uu___403_7485 = t1  in
                      {
                        FStar_Syntax_Syntax.n = tn2;
                        FStar_Syntax_Syntax.pos =
                          (uu___403_7485.FStar_Syntax_Syntax.pos);
                        FStar_Syntax_Syntax.vars =
                          (uu___403_7485.FStar_Syntax_Syntax.vars)
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
            let uu____7522 =
              FStar_TypeChecker_TcTerm.tc_term
                (let uu___405_7531 = env  in
                 {
                   FStar_TypeChecker_Env.solver =
                     (uu___405_7531.FStar_TypeChecker_Env.solver);
                   FStar_TypeChecker_Env.range =
                     (uu___405_7531.FStar_TypeChecker_Env.range);
                   FStar_TypeChecker_Env.curmodule =
                     (uu___405_7531.FStar_TypeChecker_Env.curmodule);
                   FStar_TypeChecker_Env.gamma =
                     (uu___405_7531.FStar_TypeChecker_Env.gamma);
                   FStar_TypeChecker_Env.gamma_sig =
                     (uu___405_7531.FStar_TypeChecker_Env.gamma_sig);
                   FStar_TypeChecker_Env.gamma_cache =
                     (uu___405_7531.FStar_TypeChecker_Env.gamma_cache);
                   FStar_TypeChecker_Env.modules =
                     (uu___405_7531.FStar_TypeChecker_Env.modules);
                   FStar_TypeChecker_Env.expected_typ =
                     (uu___405_7531.FStar_TypeChecker_Env.expected_typ);
                   FStar_TypeChecker_Env.sigtab =
                     (uu___405_7531.FStar_TypeChecker_Env.sigtab);
                   FStar_TypeChecker_Env.attrtab =
                     (uu___405_7531.FStar_TypeChecker_Env.attrtab);
                   FStar_TypeChecker_Env.is_pattern =
                     (uu___405_7531.FStar_TypeChecker_Env.is_pattern);
                   FStar_TypeChecker_Env.instantiate_imp =
                     (uu___405_7531.FStar_TypeChecker_Env.instantiate_imp);
                   FStar_TypeChecker_Env.effects =
                     (uu___405_7531.FStar_TypeChecker_Env.effects);
                   FStar_TypeChecker_Env.generalize =
                     (uu___405_7531.FStar_TypeChecker_Env.generalize);
                   FStar_TypeChecker_Env.letrecs =
                     (uu___405_7531.FStar_TypeChecker_Env.letrecs);
                   FStar_TypeChecker_Env.top_level =
                     (uu___405_7531.FStar_TypeChecker_Env.top_level);
                   FStar_TypeChecker_Env.check_uvars =
                     (uu___405_7531.FStar_TypeChecker_Env.check_uvars);
                   FStar_TypeChecker_Env.use_eq =
                     (uu___405_7531.FStar_TypeChecker_Env.use_eq);
                   FStar_TypeChecker_Env.is_iface =
                     (uu___405_7531.FStar_TypeChecker_Env.is_iface);
                   FStar_TypeChecker_Env.admit =
                     (uu___405_7531.FStar_TypeChecker_Env.admit);
                   FStar_TypeChecker_Env.lax = true;
                   FStar_TypeChecker_Env.lax_universes =
                     (uu___405_7531.FStar_TypeChecker_Env.lax_universes);
                   FStar_TypeChecker_Env.phase1 =
                     (uu___405_7531.FStar_TypeChecker_Env.phase1);
                   FStar_TypeChecker_Env.failhard =
                     (uu___405_7531.FStar_TypeChecker_Env.failhard);
                   FStar_TypeChecker_Env.nosynth =
                     (uu___405_7531.FStar_TypeChecker_Env.nosynth);
                   FStar_TypeChecker_Env.uvar_subtyping =
                     (uu___405_7531.FStar_TypeChecker_Env.uvar_subtyping);
                   FStar_TypeChecker_Env.tc_term =
                     (uu___405_7531.FStar_TypeChecker_Env.tc_term);
                   FStar_TypeChecker_Env.type_of =
                     (uu___405_7531.FStar_TypeChecker_Env.type_of);
                   FStar_TypeChecker_Env.universe_of =
                     (uu___405_7531.FStar_TypeChecker_Env.universe_of);
                   FStar_TypeChecker_Env.check_type_of =
                     (uu___405_7531.FStar_TypeChecker_Env.check_type_of);
                   FStar_TypeChecker_Env.use_bv_sorts =
                     (uu___405_7531.FStar_TypeChecker_Env.use_bv_sorts);
                   FStar_TypeChecker_Env.qtbl_name_and_index =
                     (uu___405_7531.FStar_TypeChecker_Env.qtbl_name_and_index);
                   FStar_TypeChecker_Env.normalized_eff_names =
                     (uu___405_7531.FStar_TypeChecker_Env.normalized_eff_names);
                   FStar_TypeChecker_Env.proof_ns =
                     (uu___405_7531.FStar_TypeChecker_Env.proof_ns);
                   FStar_TypeChecker_Env.synth_hook =
                     (uu___405_7531.FStar_TypeChecker_Env.synth_hook);
                   FStar_TypeChecker_Env.splice =
                     (uu___405_7531.FStar_TypeChecker_Env.splice);
                   FStar_TypeChecker_Env.is_native_tactic =
                     (uu___405_7531.FStar_TypeChecker_Env.is_native_tactic);
                   FStar_TypeChecker_Env.identifier_info =
                     (uu___405_7531.FStar_TypeChecker_Env.identifier_info);
                   FStar_TypeChecker_Env.tc_hooks =
                     (uu___405_7531.FStar_TypeChecker_Env.tc_hooks);
                   FStar_TypeChecker_Env.dsenv =
                     (uu___405_7531.FStar_TypeChecker_Env.dsenv);
                   FStar_TypeChecker_Env.dep_graph =
                     (uu___405_7531.FStar_TypeChecker_Env.dep_graph);
                   FStar_TypeChecker_Env.nbe =
                     (uu___405_7531.FStar_TypeChecker_Env.nbe)
                 }) t
               in
            match uu____7522 with
            | (t1,lcomp,g) ->
                let uu____7537 =
                  (let uu____7540 =
                     FStar_Syntax_Util.is_pure_or_ghost_lcomp lcomp  in
                   Prims.op_Negation uu____7540) ||
                    (let uu____7542 = FStar_TypeChecker_Env.is_trivial g  in
                     Prims.op_Negation uu____7542)
                   in
                if uu____7537
                then ret t1
                else
                  (let rewrite_eq =
                     let typ = lcomp.FStar_Syntax_Syntax.res_typ  in
                     let uu____7550 = new_uvar "pointwise_rec" env typ  in
                     bind uu____7550
                       (fun uu____7566  ->
                          match uu____7566 with
                          | (ut,uvar_ut) ->
                              (log ps
                                 (fun uu____7579  ->
                                    let uu____7580 =
                                      FStar_Syntax_Print.term_to_string t1
                                       in
                                    let uu____7581 =
                                      FStar_Syntax_Print.term_to_string ut
                                       in
                                    FStar_Util.print2
                                      "Pointwise_rec: making equality\n\t%s ==\n\t%s\n"
                                      uu____7580 uu____7581);
                               (let uu____7582 =
                                  let uu____7585 =
                                    let uu____7586 =
                                      FStar_TypeChecker_TcTerm.universe_of
                                        env typ
                                       in
                                    FStar_Syntax_Util.mk_eq2 uu____7586 typ
                                      t1 ut
                                     in
                                  add_irrelevant_goal
                                    "pointwise_rec equation" env uu____7585
                                    opts
                                   in
                                bind uu____7582
                                  (fun uu____7589  ->
                                     let uu____7590 =
                                       bind tau
                                         (fun uu____7596  ->
                                            let ut1 =
                                              FStar_TypeChecker_Normalize.reduce_uvar_solutions
                                                env ut
                                               in
                                            log ps
                                              (fun uu____7602  ->
                                                 let uu____7603 =
                                                   FStar_Syntax_Print.term_to_string
                                                     t1
                                                    in
                                                 let uu____7604 =
                                                   FStar_Syntax_Print.term_to_string
                                                     ut1
                                                    in
                                                 FStar_Util.print2
                                                   "Pointwise_rec: succeeded rewriting\n\t%s to\n\t%s\n"
                                                   uu____7603 uu____7604);
                                            ret ut1)
                                        in
                                     focus uu____7590))))
                      in
                   let uu____7605 = catch rewrite_eq  in
                   bind uu____7605
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
          let uu____7803 = FStar_Syntax_Subst.compress t  in
          maybe_continue ctrl uu____7803
            (fun t1  ->
               let uu____7811 =
                 f env
                   (let uu___408_7820 = t1  in
                    {
                      FStar_Syntax_Syntax.n = (t1.FStar_Syntax_Syntax.n);
                      FStar_Syntax_Syntax.pos =
                        (uu___408_7820.FStar_Syntax_Syntax.pos);
                      FStar_Syntax_Syntax.vars =
                        (uu___408_7820.FStar_Syntax_Syntax.vars)
                    })
                  in
               bind uu____7811
                 (fun uu____7836  ->
                    match uu____7836 with
                    | (t2,ctrl1) ->
                        maybe_continue ctrl1 t2
                          (fun t3  ->
                             let uu____7859 =
                               let uu____7860 =
                                 FStar_Syntax_Subst.compress t3  in
                               uu____7860.FStar_Syntax_Syntax.n  in
                             match uu____7859 with
                             | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
                                 let uu____7897 =
                                   ctrl_tac_fold f env ctrl1 hd1  in
                                 bind uu____7897
                                   (fun uu____7922  ->
                                      match uu____7922 with
                                      | (hd2,ctrl2) ->
                                          let ctrl3 = keep_going ctrl2  in
                                          let uu____7938 =
                                            ctrl_tac_fold_args f env ctrl3
                                              args
                                             in
                                          bind uu____7938
                                            (fun uu____7965  ->
                                               match uu____7965 with
                                               | (args1,ctrl4) ->
                                                   ret
                                                     ((let uu___406_7995 = t3
                                                          in
                                                       {
                                                         FStar_Syntax_Syntax.n
                                                           =
                                                           (FStar_Syntax_Syntax.Tm_app
                                                              (hd2, args1));
                                                         FStar_Syntax_Syntax.pos
                                                           =
                                                           (uu___406_7995.FStar_Syntax_Syntax.pos);
                                                         FStar_Syntax_Syntax.vars
                                                           =
                                                           (uu___406_7995.FStar_Syntax_Syntax.vars)
                                                       }), ctrl4)))
                             | FStar_Syntax_Syntax.Tm_abs (bs,t4,k) ->
                                 let uu____8037 =
                                   FStar_Syntax_Subst.open_term bs t4  in
                                 (match uu____8037 with
                                  | (bs1,t') ->
                                      let uu____8052 =
                                        let uu____8059 =
                                          FStar_TypeChecker_Env.push_binders
                                            env bs1
                                           in
                                        ctrl_tac_fold f uu____8059 ctrl1 t'
                                         in
                                      bind uu____8052
                                        (fun uu____8077  ->
                                           match uu____8077 with
                                           | (t'',ctrl2) ->
                                               let uu____8092 =
                                                 let uu____8099 =
                                                   let uu___407_8102 = t4  in
                                                   let uu____8105 =
                                                     let uu____8106 =
                                                       let uu____8125 =
                                                         FStar_Syntax_Subst.close_binders
                                                           bs1
                                                          in
                                                       let uu____8134 =
                                                         FStar_Syntax_Subst.close
                                                           bs1 t''
                                                          in
                                                       (uu____8125,
                                                         uu____8134, k)
                                                        in
                                                     FStar_Syntax_Syntax.Tm_abs
                                                       uu____8106
                                                      in
                                                   {
                                                     FStar_Syntax_Syntax.n =
                                                       uu____8105;
                                                     FStar_Syntax_Syntax.pos
                                                       =
                                                       (uu___407_8102.FStar_Syntax_Syntax.pos);
                                                     FStar_Syntax_Syntax.vars
                                                       =
                                                       (uu___407_8102.FStar_Syntax_Syntax.vars)
                                                   }  in
                                                 (uu____8099, ctrl2)  in
                                               ret uu____8092))
                             | FStar_Syntax_Syntax.Tm_arrow (bs,k) ->
                                 ret (t3, ctrl1)
                             | uu____8187 -> ret (t3, ctrl1))))

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
              let uu____8234 = ctrl_tac_fold f env ctrl t  in
              bind uu____8234
                (fun uu____8258  ->
                   match uu____8258 with
                   | (t1,ctrl1) ->
                       let uu____8273 = ctrl_tac_fold_args f env ctrl1 ts1
                          in
                       bind uu____8273
                         (fun uu____8300  ->
                            match uu____8300 with
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
              let uu____8384 =
                let uu____8391 =
                  add_irrelevant_goal "dummy" env FStar_Syntax_Util.t_true
                    opts
                   in
                bind uu____8391
                  (fun uu____8400  ->
                     let uu____8401 = ctrl t1  in
                     bind uu____8401
                       (fun res  ->
                          let uu____8424 = trivial ()  in
                          bind uu____8424 (fun uu____8432  -> ret res)))
                 in
              bind uu____8384
                (fun uu____8448  ->
                   match uu____8448 with
                   | (should_rewrite,ctrl1) ->
                       if Prims.op_Negation should_rewrite
                       then ret (t1, ctrl1)
                       else
                         (let uu____8472 =
                            FStar_TypeChecker_TcTerm.tc_term
                              (let uu___409_8481 = env  in
                               {
                                 FStar_TypeChecker_Env.solver =
                                   (uu___409_8481.FStar_TypeChecker_Env.solver);
                                 FStar_TypeChecker_Env.range =
                                   (uu___409_8481.FStar_TypeChecker_Env.range);
                                 FStar_TypeChecker_Env.curmodule =
                                   (uu___409_8481.FStar_TypeChecker_Env.curmodule);
                                 FStar_TypeChecker_Env.gamma =
                                   (uu___409_8481.FStar_TypeChecker_Env.gamma);
                                 FStar_TypeChecker_Env.gamma_sig =
                                   (uu___409_8481.FStar_TypeChecker_Env.gamma_sig);
                                 FStar_TypeChecker_Env.gamma_cache =
                                   (uu___409_8481.FStar_TypeChecker_Env.gamma_cache);
                                 FStar_TypeChecker_Env.modules =
                                   (uu___409_8481.FStar_TypeChecker_Env.modules);
                                 FStar_TypeChecker_Env.expected_typ =
                                   (uu___409_8481.FStar_TypeChecker_Env.expected_typ);
                                 FStar_TypeChecker_Env.sigtab =
                                   (uu___409_8481.FStar_TypeChecker_Env.sigtab);
                                 FStar_TypeChecker_Env.attrtab =
                                   (uu___409_8481.FStar_TypeChecker_Env.attrtab);
                                 FStar_TypeChecker_Env.is_pattern =
                                   (uu___409_8481.FStar_TypeChecker_Env.is_pattern);
                                 FStar_TypeChecker_Env.instantiate_imp =
                                   (uu___409_8481.FStar_TypeChecker_Env.instantiate_imp);
                                 FStar_TypeChecker_Env.effects =
                                   (uu___409_8481.FStar_TypeChecker_Env.effects);
                                 FStar_TypeChecker_Env.generalize =
                                   (uu___409_8481.FStar_TypeChecker_Env.generalize);
                                 FStar_TypeChecker_Env.letrecs =
                                   (uu___409_8481.FStar_TypeChecker_Env.letrecs);
                                 FStar_TypeChecker_Env.top_level =
                                   (uu___409_8481.FStar_TypeChecker_Env.top_level);
                                 FStar_TypeChecker_Env.check_uvars =
                                   (uu___409_8481.FStar_TypeChecker_Env.check_uvars);
                                 FStar_TypeChecker_Env.use_eq =
                                   (uu___409_8481.FStar_TypeChecker_Env.use_eq);
                                 FStar_TypeChecker_Env.is_iface =
                                   (uu___409_8481.FStar_TypeChecker_Env.is_iface);
                                 FStar_TypeChecker_Env.admit =
                                   (uu___409_8481.FStar_TypeChecker_Env.admit);
                                 FStar_TypeChecker_Env.lax = true;
                                 FStar_TypeChecker_Env.lax_universes =
                                   (uu___409_8481.FStar_TypeChecker_Env.lax_universes);
                                 FStar_TypeChecker_Env.phase1 =
                                   (uu___409_8481.FStar_TypeChecker_Env.phase1);
                                 FStar_TypeChecker_Env.failhard =
                                   (uu___409_8481.FStar_TypeChecker_Env.failhard);
                                 FStar_TypeChecker_Env.nosynth =
                                   (uu___409_8481.FStar_TypeChecker_Env.nosynth);
                                 FStar_TypeChecker_Env.uvar_subtyping =
                                   (uu___409_8481.FStar_TypeChecker_Env.uvar_subtyping);
                                 FStar_TypeChecker_Env.tc_term =
                                   (uu___409_8481.FStar_TypeChecker_Env.tc_term);
                                 FStar_TypeChecker_Env.type_of =
                                   (uu___409_8481.FStar_TypeChecker_Env.type_of);
                                 FStar_TypeChecker_Env.universe_of =
                                   (uu___409_8481.FStar_TypeChecker_Env.universe_of);
                                 FStar_TypeChecker_Env.check_type_of =
                                   (uu___409_8481.FStar_TypeChecker_Env.check_type_of);
                                 FStar_TypeChecker_Env.use_bv_sorts =
                                   (uu___409_8481.FStar_TypeChecker_Env.use_bv_sorts);
                                 FStar_TypeChecker_Env.qtbl_name_and_index =
                                   (uu___409_8481.FStar_TypeChecker_Env.qtbl_name_and_index);
                                 FStar_TypeChecker_Env.normalized_eff_names =
                                   (uu___409_8481.FStar_TypeChecker_Env.normalized_eff_names);
                                 FStar_TypeChecker_Env.proof_ns =
                                   (uu___409_8481.FStar_TypeChecker_Env.proof_ns);
                                 FStar_TypeChecker_Env.synth_hook =
                                   (uu___409_8481.FStar_TypeChecker_Env.synth_hook);
                                 FStar_TypeChecker_Env.splice =
                                   (uu___409_8481.FStar_TypeChecker_Env.splice);
                                 FStar_TypeChecker_Env.is_native_tactic =
                                   (uu___409_8481.FStar_TypeChecker_Env.is_native_tactic);
                                 FStar_TypeChecker_Env.identifier_info =
                                   (uu___409_8481.FStar_TypeChecker_Env.identifier_info);
                                 FStar_TypeChecker_Env.tc_hooks =
                                   (uu___409_8481.FStar_TypeChecker_Env.tc_hooks);
                                 FStar_TypeChecker_Env.dsenv =
                                   (uu___409_8481.FStar_TypeChecker_Env.dsenv);
                                 FStar_TypeChecker_Env.dep_graph =
                                   (uu___409_8481.FStar_TypeChecker_Env.dep_graph);
                                 FStar_TypeChecker_Env.nbe =
                                   (uu___409_8481.FStar_TypeChecker_Env.nbe)
                               }) t1
                             in
                          match uu____8472 with
                          | (t2,lcomp,g) ->
                              let uu____8491 =
                                (let uu____8494 =
                                   FStar_Syntax_Util.is_pure_or_ghost_lcomp
                                     lcomp
                                    in
                                 Prims.op_Negation uu____8494) ||
                                  (let uu____8496 =
                                     FStar_TypeChecker_Env.is_trivial g  in
                                   Prims.op_Negation uu____8496)
                                 in
                              if uu____8491
                              then ret (t2, globalStop)
                              else
                                (let typ = lcomp.FStar_Syntax_Syntax.res_typ
                                    in
                                 let uu____8509 =
                                   new_uvar "pointwise_rec" env typ  in
                                 bind uu____8509
                                   (fun uu____8529  ->
                                      match uu____8529 with
                                      | (ut,uvar_ut) ->
                                          (log ps
                                             (fun uu____8546  ->
                                                let uu____8547 =
                                                  FStar_Syntax_Print.term_to_string
                                                    t2
                                                   in
                                                let uu____8548 =
                                                  FStar_Syntax_Print.term_to_string
                                                    ut
                                                   in
                                                FStar_Util.print2
                                                  "Pointwise_rec: making equality\n\t%s ==\n\t%s\n"
                                                  uu____8547 uu____8548);
                                           (let uu____8549 =
                                              let uu____8552 =
                                                let uu____8553 =
                                                  FStar_TypeChecker_TcTerm.universe_of
                                                    env typ
                                                   in
                                                FStar_Syntax_Util.mk_eq2
                                                  uu____8553 typ t2 ut
                                                 in
                                              add_irrelevant_goal
                                                "rewrite_rec equation" env
                                                uu____8552 opts
                                               in
                                            bind uu____8549
                                              (fun uu____8560  ->
                                                 let uu____8561 =
                                                   bind rewriter
                                                     (fun uu____8575  ->
                                                        let ut1 =
                                                          FStar_TypeChecker_Normalize.reduce_uvar_solutions
                                                            env ut
                                                           in
                                                        log ps
                                                          (fun uu____8581  ->
                                                             let uu____8582 =
                                                               FStar_Syntax_Print.term_to_string
                                                                 t2
                                                                in
                                                             let uu____8583 =
                                                               FStar_Syntax_Print.term_to_string
                                                                 ut1
                                                                in
                                                             FStar_Util.print2
                                                               "rewrite_rec: succeeded rewriting\n\t%s to\n\t%s\n"
                                                               uu____8582
                                                               uu____8583);
                                                        ret (ut1, ctrl1))
                                                    in
                                                 focus uu____8561)))))))
  
let (topdown_rewrite :
  (FStar_Syntax_Syntax.term ->
     (Prims.bool,FStar_BigInt.t) FStar_Pervasives_Native.tuple2 tac)
    -> unit tac -> unit tac)
  =
  fun ctrl  ->
    fun rewriter  ->
      let uu____8624 =
        bind get
          (fun ps  ->
             let uu____8634 =
               match ps.FStar_Tactics_Types.goals with
               | g::gs -> (g, gs)
               | [] -> failwith "no goals"  in
             match uu____8634 with
             | (g,gs) ->
                 let gt1 = FStar_Tactics_Types.goal_type g  in
                 (log ps
                    (fun uu____8671  ->
                       let uu____8672 = FStar_Syntax_Print.term_to_string gt1
                          in
                       FStar_Util.print1 "Topdown_rewrite starting with %s\n"
                         uu____8672);
                  bind dismiss_all
                    (fun uu____8675  ->
                       let uu____8676 =
                         let uu____8683 = FStar_Tactics_Types.goal_env g  in
                         ctrl_tac_fold
                           (rewrite_rec ps ctrl rewriter
                              g.FStar_Tactics_Types.opts) uu____8683
                           keepGoing gt1
                          in
                       bind uu____8676
                         (fun uu____8695  ->
                            match uu____8695 with
                            | (gt',uu____8703) ->
                                (log ps
                                   (fun uu____8707  ->
                                      let uu____8708 =
                                        FStar_Syntax_Print.term_to_string gt'
                                         in
                                      FStar_Util.print1
                                        "Topdown_rewrite seems to have succeded with %s\n"
                                        uu____8708);
                                 (let uu____8709 = push_goals gs  in
                                  bind uu____8709
                                    (fun uu____8714  ->
                                       let uu____8715 =
                                         let uu____8718 =
                                           FStar_Tactics_Types.goal_with_type
                                             g gt'
                                            in
                                         [uu____8718]  in
                                       add_goals uu____8715)))))))
         in
      FStar_All.pipe_left (wrap_err "topdown_rewrite") uu____8624
  
let (pointwise : FStar_Tactics_Types.direction -> unit tac -> unit tac) =
  fun d  ->
    fun tau  ->
      let uu____8741 =
        bind get
          (fun ps  ->
             let uu____8751 =
               match ps.FStar_Tactics_Types.goals with
               | g::gs -> (g, gs)
               | [] -> failwith "no goals"  in
             match uu____8751 with
             | (g,gs) ->
                 let gt1 = FStar_Tactics_Types.goal_type g  in
                 (log ps
                    (fun uu____8788  ->
                       let uu____8789 = FStar_Syntax_Print.term_to_string gt1
                          in
                       FStar_Util.print1 "Pointwise starting with %s\n"
                         uu____8789);
                  bind dismiss_all
                    (fun uu____8792  ->
                       let uu____8793 =
                         let uu____8796 = FStar_Tactics_Types.goal_env g  in
                         tac_fold_env d
                           (pointwise_rec ps tau g.FStar_Tactics_Types.opts)
                           uu____8796 gt1
                          in
                       bind uu____8793
                         (fun gt'  ->
                            log ps
                              (fun uu____8804  ->
                                 let uu____8805 =
                                   FStar_Syntax_Print.term_to_string gt'  in
                                 FStar_Util.print1
                                   "Pointwise seems to have succeded with %s\n"
                                   uu____8805);
                            (let uu____8806 = push_goals gs  in
                             bind uu____8806
                               (fun uu____8811  ->
                                  let uu____8812 =
                                    let uu____8815 =
                                      FStar_Tactics_Types.goal_with_type g
                                        gt'
                                       in
                                    [uu____8815]  in
                                  add_goals uu____8812))))))
         in
      FStar_All.pipe_left (wrap_err "pointwise") uu____8741
  
let (trefl : unit -> unit tac) =
  fun uu____8826  ->
    let uu____8829 =
      let uu____8832 = cur_goal ()  in
      bind uu____8832
        (fun g  ->
           let uu____8850 =
             let uu____8855 = FStar_Tactics_Types.goal_type g  in
             FStar_Syntax_Util.un_squash uu____8855  in
           match uu____8850 with
           | FStar_Pervasives_Native.Some t ->
               let uu____8863 = FStar_Syntax_Util.head_and_args' t  in
               (match uu____8863 with
                | (hd1,args) ->
                    let uu____8902 =
                      let uu____8915 =
                        let uu____8916 = FStar_Syntax_Util.un_uinst hd1  in
                        uu____8916.FStar_Syntax_Syntax.n  in
                      (uu____8915, args)  in
                    (match uu____8902 with
                     | (FStar_Syntax_Syntax.Tm_fvar
                        fv,uu____8930::(l,uu____8932)::(r,uu____8934)::[])
                         when
                         FStar_Syntax_Syntax.fv_eq_lid fv
                           FStar_Parser_Const.eq2_lid
                         ->
                         let uu____8981 =
                           let uu____8984 = FStar_Tactics_Types.goal_env g
                              in
                           do_unify uu____8984 l r  in
                         bind uu____8981
                           (fun b  ->
                              if b
                              then solve' g FStar_Syntax_Util.exp_unit
                              else
                                (let l1 =
                                   let uu____8991 =
                                     FStar_Tactics_Types.goal_env g  in
                                   FStar_TypeChecker_Normalize.normalize
                                     [FStar_TypeChecker_Env.UnfoldUntil
                                        FStar_Syntax_Syntax.delta_constant;
                                     FStar_TypeChecker_Env.Primops;
                                     FStar_TypeChecker_Env.UnfoldTac]
                                     uu____8991 l
                                    in
                                 let r1 =
                                   let uu____8993 =
                                     FStar_Tactics_Types.goal_env g  in
                                   FStar_TypeChecker_Normalize.normalize
                                     [FStar_TypeChecker_Env.UnfoldUntil
                                        FStar_Syntax_Syntax.delta_constant;
                                     FStar_TypeChecker_Env.Primops;
                                     FStar_TypeChecker_Env.UnfoldTac]
                                     uu____8993 r
                                    in
                                 let uu____8994 =
                                   let uu____8997 =
                                     FStar_Tactics_Types.goal_env g  in
                                   do_unify uu____8997 l1 r1  in
                                 bind uu____8994
                                   (fun b1  ->
                                      if b1
                                      then
                                        solve' g FStar_Syntax_Util.exp_unit
                                      else
                                        (let uu____9003 =
                                           let uu____9004 =
                                             FStar_Tactics_Types.goal_env g
                                              in
                                           tts uu____9004 l1  in
                                         let uu____9005 =
                                           let uu____9006 =
                                             FStar_Tactics_Types.goal_env g
                                              in
                                           tts uu____9006 r1  in
                                         fail2
                                           "not a trivial equality ((%s) vs (%s))"
                                           uu____9003 uu____9005))))
                     | (hd2,uu____9008) ->
                         let uu____9025 =
                           let uu____9026 = FStar_Tactics_Types.goal_env g
                              in
                           tts uu____9026 t  in
                         fail1 "trefl: not an equality (%s)" uu____9025))
           | FStar_Pervasives_Native.None  -> fail "not an irrelevant goal")
       in
    FStar_All.pipe_left (wrap_err "trefl") uu____8829
  
let (dup : unit -> unit tac) =
  fun uu____9039  ->
    let uu____9042 = cur_goal ()  in
    bind uu____9042
      (fun g  ->
         let uu____9048 =
           let uu____9055 = FStar_Tactics_Types.goal_env g  in
           let uu____9056 = FStar_Tactics_Types.goal_type g  in
           new_uvar "dup" uu____9055 uu____9056  in
         bind uu____9048
           (fun uu____9065  ->
              match uu____9065 with
              | (u,u_uvar) ->
                  let g' =
                    let uu___410_9075 = g  in
                    {
                      FStar_Tactics_Types.goal_main_env =
                        (uu___410_9075.FStar_Tactics_Types.goal_main_env);
                      FStar_Tactics_Types.goal_ctx_uvar = u_uvar;
                      FStar_Tactics_Types.opts =
                        (uu___410_9075.FStar_Tactics_Types.opts);
                      FStar_Tactics_Types.is_guard =
                        (uu___410_9075.FStar_Tactics_Types.is_guard)
                    }  in
                  bind __dismiss
                    (fun uu____9078  ->
                       let uu____9079 =
                         let uu____9082 = FStar_Tactics_Types.goal_env g  in
                         let uu____9083 =
                           let uu____9084 =
                             let uu____9085 = FStar_Tactics_Types.goal_env g
                                in
                             let uu____9086 = FStar_Tactics_Types.goal_type g
                                in
                             FStar_TypeChecker_TcTerm.universe_of uu____9085
                               uu____9086
                              in
                           let uu____9087 = FStar_Tactics_Types.goal_type g
                              in
                           let uu____9088 =
                             FStar_Tactics_Types.goal_witness g  in
                           FStar_Syntax_Util.mk_eq2 uu____9084 uu____9087 u
                             uu____9088
                            in
                         add_irrelevant_goal "dup equation" uu____9082
                           uu____9083 g.FStar_Tactics_Types.opts
                          in
                       bind uu____9079
                         (fun uu____9091  ->
                            let uu____9092 = add_goals [g']  in
                            bind uu____9092 (fun uu____9096  -> ret ())))))
  
let (flip : unit -> unit tac) =
  fun uu____9103  ->
    bind get
      (fun ps  ->
         match ps.FStar_Tactics_Types.goals with
         | g1::g2::gs ->
             set
               (let uu___411_9120 = ps  in
                {
                  FStar_Tactics_Types.main_context =
                    (uu___411_9120.FStar_Tactics_Types.main_context);
                  FStar_Tactics_Types.main_goal =
                    (uu___411_9120.FStar_Tactics_Types.main_goal);
                  FStar_Tactics_Types.all_implicits =
                    (uu___411_9120.FStar_Tactics_Types.all_implicits);
                  FStar_Tactics_Types.goals = (g2 :: g1 :: gs);
                  FStar_Tactics_Types.smt_goals =
                    (uu___411_9120.FStar_Tactics_Types.smt_goals);
                  FStar_Tactics_Types.depth =
                    (uu___411_9120.FStar_Tactics_Types.depth);
                  FStar_Tactics_Types.__dump =
                    (uu___411_9120.FStar_Tactics_Types.__dump);
                  FStar_Tactics_Types.psc =
                    (uu___411_9120.FStar_Tactics_Types.psc);
                  FStar_Tactics_Types.entry_range =
                    (uu___411_9120.FStar_Tactics_Types.entry_range);
                  FStar_Tactics_Types.guard_policy =
                    (uu___411_9120.FStar_Tactics_Types.guard_policy);
                  FStar_Tactics_Types.freshness =
                    (uu___411_9120.FStar_Tactics_Types.freshness);
                  FStar_Tactics_Types.tac_verb_dbg =
                    (uu___411_9120.FStar_Tactics_Types.tac_verb_dbg);
                  FStar_Tactics_Types.local_state =
                    (uu___411_9120.FStar_Tactics_Types.local_state)
                })
         | uu____9121 -> fail "flip: less than 2 goals")
  
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
              let uu____9246 = f x y  in
              if uu____9246 then aux (x :: acc) xs ys else (acc, xs, ys)
          | uu____9266 -> (acc, l11, l21)  in
        let uu____9281 = aux [] l1 l2  in
        match uu____9281 with | (pr,t1,t2) -> ((FStar_List.rev pr), t1, t2)
  
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
      let uu____9386 = get_phi g1  in
      match uu____9386 with
      | FStar_Pervasives_Native.None  -> fail "goal 1 is not irrelevant"
      | FStar_Pervasives_Native.Some phi1 ->
          let uu____9392 = get_phi g2  in
          (match uu____9392 with
           | FStar_Pervasives_Native.None  -> fail "goal 2 is not irrelevant"
           | FStar_Pervasives_Native.Some phi2 ->
               let gamma1 =
                 (g1.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_gamma
                  in
               let gamma2 =
                 (g2.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_gamma
                  in
               let uu____9404 =
                 longest_prefix FStar_Syntax_Syntax.eq_binding
                   (FStar_List.rev gamma1) (FStar_List.rev gamma2)
                  in
               (match uu____9404 with
                | (gamma,r1,r2) ->
                    let t1 =
                      let uu____9435 =
                        FStar_TypeChecker_Env.binders_of_bindings r1  in
                      close_forall_no_univs1 uu____9435 phi1  in
                    let t2 =
                      let uu____9445 =
                        FStar_TypeChecker_Env.binders_of_bindings r2  in
                      close_forall_no_univs1 uu____9445 phi2  in
                    let uu____9454 =
                      set_solution g1 FStar_Syntax_Util.exp_unit  in
                    bind uu____9454
                      (fun uu____9459  ->
                         let uu____9460 =
                           set_solution g2 FStar_Syntax_Util.exp_unit  in
                         bind uu____9460
                           (fun uu____9467  ->
                              let ng = FStar_Syntax_Util.mk_conj t1 t2  in
                              let nenv =
                                let uu___412_9472 =
                                  FStar_Tactics_Types.goal_env g1  in
                                let uu____9473 =
                                  FStar_Util.smap_create
                                    (Prims.parse_int "100")
                                   in
                                {
                                  FStar_TypeChecker_Env.solver =
                                    (uu___412_9472.FStar_TypeChecker_Env.solver);
                                  FStar_TypeChecker_Env.range =
                                    (uu___412_9472.FStar_TypeChecker_Env.range);
                                  FStar_TypeChecker_Env.curmodule =
                                    (uu___412_9472.FStar_TypeChecker_Env.curmodule);
                                  FStar_TypeChecker_Env.gamma =
                                    (FStar_List.rev gamma);
                                  FStar_TypeChecker_Env.gamma_sig =
                                    (uu___412_9472.FStar_TypeChecker_Env.gamma_sig);
                                  FStar_TypeChecker_Env.gamma_cache =
                                    uu____9473;
                                  FStar_TypeChecker_Env.modules =
                                    (uu___412_9472.FStar_TypeChecker_Env.modules);
                                  FStar_TypeChecker_Env.expected_typ =
                                    (uu___412_9472.FStar_TypeChecker_Env.expected_typ);
                                  FStar_TypeChecker_Env.sigtab =
                                    (uu___412_9472.FStar_TypeChecker_Env.sigtab);
                                  FStar_TypeChecker_Env.attrtab =
                                    (uu___412_9472.FStar_TypeChecker_Env.attrtab);
                                  FStar_TypeChecker_Env.is_pattern =
                                    (uu___412_9472.FStar_TypeChecker_Env.is_pattern);
                                  FStar_TypeChecker_Env.instantiate_imp =
                                    (uu___412_9472.FStar_TypeChecker_Env.instantiate_imp);
                                  FStar_TypeChecker_Env.effects =
                                    (uu___412_9472.FStar_TypeChecker_Env.effects);
                                  FStar_TypeChecker_Env.generalize =
                                    (uu___412_9472.FStar_TypeChecker_Env.generalize);
                                  FStar_TypeChecker_Env.letrecs =
                                    (uu___412_9472.FStar_TypeChecker_Env.letrecs);
                                  FStar_TypeChecker_Env.top_level =
                                    (uu___412_9472.FStar_TypeChecker_Env.top_level);
                                  FStar_TypeChecker_Env.check_uvars =
                                    (uu___412_9472.FStar_TypeChecker_Env.check_uvars);
                                  FStar_TypeChecker_Env.use_eq =
                                    (uu___412_9472.FStar_TypeChecker_Env.use_eq);
                                  FStar_TypeChecker_Env.is_iface =
                                    (uu___412_9472.FStar_TypeChecker_Env.is_iface);
                                  FStar_TypeChecker_Env.admit =
                                    (uu___412_9472.FStar_TypeChecker_Env.admit);
                                  FStar_TypeChecker_Env.lax =
                                    (uu___412_9472.FStar_TypeChecker_Env.lax);
                                  FStar_TypeChecker_Env.lax_universes =
                                    (uu___412_9472.FStar_TypeChecker_Env.lax_universes);
                                  FStar_TypeChecker_Env.phase1 =
                                    (uu___412_9472.FStar_TypeChecker_Env.phase1);
                                  FStar_TypeChecker_Env.failhard =
                                    (uu___412_9472.FStar_TypeChecker_Env.failhard);
                                  FStar_TypeChecker_Env.nosynth =
                                    (uu___412_9472.FStar_TypeChecker_Env.nosynth);
                                  FStar_TypeChecker_Env.uvar_subtyping =
                                    (uu___412_9472.FStar_TypeChecker_Env.uvar_subtyping);
                                  FStar_TypeChecker_Env.tc_term =
                                    (uu___412_9472.FStar_TypeChecker_Env.tc_term);
                                  FStar_TypeChecker_Env.type_of =
                                    (uu___412_9472.FStar_TypeChecker_Env.type_of);
                                  FStar_TypeChecker_Env.universe_of =
                                    (uu___412_9472.FStar_TypeChecker_Env.universe_of);
                                  FStar_TypeChecker_Env.check_type_of =
                                    (uu___412_9472.FStar_TypeChecker_Env.check_type_of);
                                  FStar_TypeChecker_Env.use_bv_sorts =
                                    (uu___412_9472.FStar_TypeChecker_Env.use_bv_sorts);
                                  FStar_TypeChecker_Env.qtbl_name_and_index =
                                    (uu___412_9472.FStar_TypeChecker_Env.qtbl_name_and_index);
                                  FStar_TypeChecker_Env.normalized_eff_names
                                    =
                                    (uu___412_9472.FStar_TypeChecker_Env.normalized_eff_names);
                                  FStar_TypeChecker_Env.proof_ns =
                                    (uu___412_9472.FStar_TypeChecker_Env.proof_ns);
                                  FStar_TypeChecker_Env.synth_hook =
                                    (uu___412_9472.FStar_TypeChecker_Env.synth_hook);
                                  FStar_TypeChecker_Env.splice =
                                    (uu___412_9472.FStar_TypeChecker_Env.splice);
                                  FStar_TypeChecker_Env.is_native_tactic =
                                    (uu___412_9472.FStar_TypeChecker_Env.is_native_tactic);
                                  FStar_TypeChecker_Env.identifier_info =
                                    (uu___412_9472.FStar_TypeChecker_Env.identifier_info);
                                  FStar_TypeChecker_Env.tc_hooks =
                                    (uu___412_9472.FStar_TypeChecker_Env.tc_hooks);
                                  FStar_TypeChecker_Env.dsenv =
                                    (uu___412_9472.FStar_TypeChecker_Env.dsenv);
                                  FStar_TypeChecker_Env.dep_graph =
                                    (uu___412_9472.FStar_TypeChecker_Env.dep_graph);
                                  FStar_TypeChecker_Env.nbe =
                                    (uu___412_9472.FStar_TypeChecker_Env.nbe)
                                }  in
                              let uu____9476 =
                                mk_irrelevant_goal "joined" nenv ng
                                  g1.FStar_Tactics_Types.opts
                                 in
                              bind uu____9476
                                (fun goal  ->
                                   mlog
                                     (fun uu____9485  ->
                                        let uu____9486 =
                                          goal_to_string_verbose g1  in
                                        let uu____9487 =
                                          goal_to_string_verbose g2  in
                                        let uu____9488 =
                                          goal_to_string_verbose goal  in
                                        FStar_Util.print3
                                          "join_goals of\n(%s)\nand\n(%s)\n= (%s)\n"
                                          uu____9486 uu____9487 uu____9488)
                                     (fun uu____9490  -> ret goal))))))
  
let (join : unit -> unit tac) =
  fun uu____9497  ->
    bind get
      (fun ps  ->
         match ps.FStar_Tactics_Types.goals with
         | g1::g2::gs ->
             let uu____9513 =
               set
                 (let uu___413_9518 = ps  in
                  {
                    FStar_Tactics_Types.main_context =
                      (uu___413_9518.FStar_Tactics_Types.main_context);
                    FStar_Tactics_Types.main_goal =
                      (uu___413_9518.FStar_Tactics_Types.main_goal);
                    FStar_Tactics_Types.all_implicits =
                      (uu___413_9518.FStar_Tactics_Types.all_implicits);
                    FStar_Tactics_Types.goals = gs;
                    FStar_Tactics_Types.smt_goals =
                      (uu___413_9518.FStar_Tactics_Types.smt_goals);
                    FStar_Tactics_Types.depth =
                      (uu___413_9518.FStar_Tactics_Types.depth);
                    FStar_Tactics_Types.__dump =
                      (uu___413_9518.FStar_Tactics_Types.__dump);
                    FStar_Tactics_Types.psc =
                      (uu___413_9518.FStar_Tactics_Types.psc);
                    FStar_Tactics_Types.entry_range =
                      (uu___413_9518.FStar_Tactics_Types.entry_range);
                    FStar_Tactics_Types.guard_policy =
                      (uu___413_9518.FStar_Tactics_Types.guard_policy);
                    FStar_Tactics_Types.freshness =
                      (uu___413_9518.FStar_Tactics_Types.freshness);
                    FStar_Tactics_Types.tac_verb_dbg =
                      (uu___413_9518.FStar_Tactics_Types.tac_verb_dbg);
                    FStar_Tactics_Types.local_state =
                      (uu___413_9518.FStar_Tactics_Types.local_state)
                  })
                in
             bind uu____9513
               (fun uu____9521  ->
                  let uu____9522 = join_goals g1 g2  in
                  bind uu____9522 (fun g12  -> add_goals [g12]))
         | uu____9527 -> fail "join: less than 2 goals")
  
let (later : unit -> unit tac) =
  fun uu____9536  ->
    bind get
      (fun ps  ->
         match ps.FStar_Tactics_Types.goals with
         | [] -> ret ()
         | g::gs ->
             set
               (let uu___414_9549 = ps  in
                {
                  FStar_Tactics_Types.main_context =
                    (uu___414_9549.FStar_Tactics_Types.main_context);
                  FStar_Tactics_Types.main_goal =
                    (uu___414_9549.FStar_Tactics_Types.main_goal);
                  FStar_Tactics_Types.all_implicits =
                    (uu___414_9549.FStar_Tactics_Types.all_implicits);
                  FStar_Tactics_Types.goals = (FStar_List.append gs [g]);
                  FStar_Tactics_Types.smt_goals =
                    (uu___414_9549.FStar_Tactics_Types.smt_goals);
                  FStar_Tactics_Types.depth =
                    (uu___414_9549.FStar_Tactics_Types.depth);
                  FStar_Tactics_Types.__dump =
                    (uu___414_9549.FStar_Tactics_Types.__dump);
                  FStar_Tactics_Types.psc =
                    (uu___414_9549.FStar_Tactics_Types.psc);
                  FStar_Tactics_Types.entry_range =
                    (uu___414_9549.FStar_Tactics_Types.entry_range);
                  FStar_Tactics_Types.guard_policy =
                    (uu___414_9549.FStar_Tactics_Types.guard_policy);
                  FStar_Tactics_Types.freshness =
                    (uu___414_9549.FStar_Tactics_Types.freshness);
                  FStar_Tactics_Types.tac_verb_dbg =
                    (uu___414_9549.FStar_Tactics_Types.tac_verb_dbg);
                  FStar_Tactics_Types.local_state =
                    (uu___414_9549.FStar_Tactics_Types.local_state)
                }))
  
let (qed : unit -> unit tac) =
  fun uu____9556  ->
    bind get
      (fun ps  ->
         match ps.FStar_Tactics_Types.goals with
         | [] -> ret ()
         | uu____9563 -> fail "Not done!")
  
let (cases :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 tac)
  =
  fun t  ->
    let uu____9583 =
      let uu____9590 = cur_goal ()  in
      bind uu____9590
        (fun g  ->
           let uu____9600 =
             let uu____9609 = FStar_Tactics_Types.goal_env g  in
             __tc uu____9609 t  in
           bind uu____9600
             (fun uu____9637  ->
                match uu____9637 with
                | (t1,typ,guard) ->
                    let uu____9653 = FStar_Syntax_Util.head_and_args typ  in
                    (match uu____9653 with
                     | (hd1,args) ->
                         let uu____9702 =
                           let uu____9717 =
                             let uu____9718 = FStar_Syntax_Util.un_uinst hd1
                                in
                             uu____9718.FStar_Syntax_Syntax.n  in
                           (uu____9717, args)  in
                         (match uu____9702 with
                          | (FStar_Syntax_Syntax.Tm_fvar
                             fv,(p,uu____9739)::(q,uu____9741)::[]) when
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
                                let uu____9795 =
                                  let uu____9796 =
                                    FStar_Tactics_Types.goal_env g  in
                                  FStar_TypeChecker_Env.push_bv uu____9796
                                    v_p
                                   in
                                FStar_Tactics_Types.goal_with_env g
                                  uu____9795
                                 in
                              let g2 =
                                let uu____9798 =
                                  let uu____9799 =
                                    FStar_Tactics_Types.goal_env g  in
                                  FStar_TypeChecker_Env.push_bv uu____9799
                                    v_q
                                   in
                                FStar_Tactics_Types.goal_with_env g
                                  uu____9798
                                 in
                              bind __dismiss
                                (fun uu____9806  ->
                                   let uu____9807 = add_goals [g1; g2]  in
                                   bind uu____9807
                                     (fun uu____9816  ->
                                        let uu____9817 =
                                          let uu____9822 =
                                            FStar_Syntax_Syntax.bv_to_name
                                              v_p
                                             in
                                          let uu____9823 =
                                            FStar_Syntax_Syntax.bv_to_name
                                              v_q
                                             in
                                          (uu____9822, uu____9823)  in
                                        ret uu____9817))
                          | uu____9828 ->
                              let uu____9843 =
                                let uu____9844 =
                                  FStar_Tactics_Types.goal_env g  in
                                tts uu____9844 typ  in
                              fail1 "Not a disjunction: %s" uu____9843))))
       in
    FStar_All.pipe_left (wrap_err "cases") uu____9583
  
let (set_options : Prims.string -> unit tac) =
  fun s  ->
    let uu____9874 =
      let uu____9877 = cur_goal ()  in
      bind uu____9877
        (fun g  ->
           FStar_Options.push ();
           (let uu____9890 = FStar_Util.smap_copy g.FStar_Tactics_Types.opts
               in
            FStar_Options.set uu____9890);
           (let res = FStar_Options.set_options FStar_Options.Set s  in
            let opts' = FStar_Options.peek ()  in
            FStar_Options.pop ();
            (match res with
             | FStar_Getopt.Success  ->
                 let g' =
                   let uu___415_9897 = g  in
                   {
                     FStar_Tactics_Types.goal_main_env =
                       (uu___415_9897.FStar_Tactics_Types.goal_main_env);
                     FStar_Tactics_Types.goal_ctx_uvar =
                       (uu___415_9897.FStar_Tactics_Types.goal_ctx_uvar);
                     FStar_Tactics_Types.opts = opts';
                     FStar_Tactics_Types.is_guard =
                       (uu___415_9897.FStar_Tactics_Types.is_guard)
                   }  in
                 replace_cur g'
             | FStar_Getopt.Error err ->
                 fail2 "Setting options `%s` failed: %s" s err
             | FStar_Getopt.Help  ->
                 fail1 "Setting options `%s` failed (got `Help`?)" s)))
       in
    FStar_All.pipe_left (wrap_err "set_options") uu____9874
  
let (top_env : unit -> env tac) =
  fun uu____9909  ->
    bind get
      (fun ps  -> FStar_All.pipe_left ret ps.FStar_Tactics_Types.main_context)
  
let (lax_on : unit -> Prims.bool tac) =
  fun uu____9922  ->
    let uu____9925 = cur_goal ()  in
    bind uu____9925
      (fun g  ->
         let uu____9931 =
           (FStar_Options.lax ()) ||
             (let uu____9933 = FStar_Tactics_Types.goal_env g  in
              uu____9933.FStar_TypeChecker_Env.lax)
            in
         ret uu____9931)
  
let (unquote :
  FStar_Reflection_Data.typ ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term tac)
  =
  fun ty  ->
    fun tm  ->
      let uu____9948 =
        mlog
          (fun uu____9953  ->
             let uu____9954 = FStar_Syntax_Print.term_to_string tm  in
             FStar_Util.print1 "unquote: tm = %s\n" uu____9954)
          (fun uu____9957  ->
             let uu____9958 = cur_goal ()  in
             bind uu____9958
               (fun goal  ->
                  let env =
                    let uu____9966 = FStar_Tactics_Types.goal_env goal  in
                    FStar_TypeChecker_Env.set_expected_typ uu____9966 ty  in
                  let uu____9967 = __tc env tm  in
                  bind uu____9967
                    (fun uu____9986  ->
                       match uu____9986 with
                       | (tm1,typ,guard) ->
                           mlog
                             (fun uu____10000  ->
                                let uu____10001 =
                                  FStar_Syntax_Print.term_to_string tm1  in
                                FStar_Util.print1 "unquote: tm' = %s\n"
                                  uu____10001)
                             (fun uu____10003  ->
                                mlog
                                  (fun uu____10006  ->
                                     let uu____10007 =
                                       FStar_Syntax_Print.term_to_string typ
                                        in
                                     FStar_Util.print1 "unquote: typ = %s\n"
                                       uu____10007)
                                  (fun uu____10010  ->
                                     let uu____10011 =
                                       proc_guard "unquote" env guard  in
                                     bind uu____10011
                                       (fun uu____10015  -> ret tm1))))))
         in
      FStar_All.pipe_left (wrap_err "unquote") uu____9948
  
let (uvar_env :
  env ->
    FStar_Reflection_Data.typ FStar_Pervasives_Native.option ->
      FStar_Syntax_Syntax.term tac)
  =
  fun env  ->
    fun ty  ->
      let uu____10038 =
        match ty with
        | FStar_Pervasives_Native.Some ty1 -> ret ty1
        | FStar_Pervasives_Native.None  ->
            let uu____10044 =
              let uu____10051 =
                let uu____10052 = FStar_Syntax_Util.type_u ()  in
                FStar_All.pipe_left FStar_Pervasives_Native.fst uu____10052
                 in
              new_uvar "uvar_env.2" env uu____10051  in
            bind uu____10044
              (fun uu____10068  ->
                 match uu____10068 with | (typ,uvar_typ) -> ret typ)
         in
      bind uu____10038
        (fun typ  ->
           let uu____10080 = new_uvar "uvar_env" env typ  in
           bind uu____10080
             (fun uu____10094  ->
                match uu____10094 with | (t,uvar_t) -> ret t))
  
let (unshelve : FStar_Syntax_Syntax.term -> unit tac) =
  fun t  ->
    let uu____10112 =
      bind get
        (fun ps  ->
           let env = ps.FStar_Tactics_Types.main_context  in
           let opts =
             match ps.FStar_Tactics_Types.goals with
             | g::uu____10131 -> g.FStar_Tactics_Types.opts
             | uu____10134 -> FStar_Options.peek ()  in
           let uu____10137 = FStar_Syntax_Util.head_and_args t  in
           match uu____10137 with
           | ({
                FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                  (ctx_uvar,uu____10157);
                FStar_Syntax_Syntax.pos = uu____10158;
                FStar_Syntax_Syntax.vars = uu____10159;_},uu____10160)
               ->
               let env1 =
                 let uu___416_10202 = env  in
                 {
                   FStar_TypeChecker_Env.solver =
                     (uu___416_10202.FStar_TypeChecker_Env.solver);
                   FStar_TypeChecker_Env.range =
                     (uu___416_10202.FStar_TypeChecker_Env.range);
                   FStar_TypeChecker_Env.curmodule =
                     (uu___416_10202.FStar_TypeChecker_Env.curmodule);
                   FStar_TypeChecker_Env.gamma =
                     (ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_gamma);
                   FStar_TypeChecker_Env.gamma_sig =
                     (uu___416_10202.FStar_TypeChecker_Env.gamma_sig);
                   FStar_TypeChecker_Env.gamma_cache =
                     (uu___416_10202.FStar_TypeChecker_Env.gamma_cache);
                   FStar_TypeChecker_Env.modules =
                     (uu___416_10202.FStar_TypeChecker_Env.modules);
                   FStar_TypeChecker_Env.expected_typ =
                     (uu___416_10202.FStar_TypeChecker_Env.expected_typ);
                   FStar_TypeChecker_Env.sigtab =
                     (uu___416_10202.FStar_TypeChecker_Env.sigtab);
                   FStar_TypeChecker_Env.attrtab =
                     (uu___416_10202.FStar_TypeChecker_Env.attrtab);
                   FStar_TypeChecker_Env.is_pattern =
                     (uu___416_10202.FStar_TypeChecker_Env.is_pattern);
                   FStar_TypeChecker_Env.instantiate_imp =
                     (uu___416_10202.FStar_TypeChecker_Env.instantiate_imp);
                   FStar_TypeChecker_Env.effects =
                     (uu___416_10202.FStar_TypeChecker_Env.effects);
                   FStar_TypeChecker_Env.generalize =
                     (uu___416_10202.FStar_TypeChecker_Env.generalize);
                   FStar_TypeChecker_Env.letrecs =
                     (uu___416_10202.FStar_TypeChecker_Env.letrecs);
                   FStar_TypeChecker_Env.top_level =
                     (uu___416_10202.FStar_TypeChecker_Env.top_level);
                   FStar_TypeChecker_Env.check_uvars =
                     (uu___416_10202.FStar_TypeChecker_Env.check_uvars);
                   FStar_TypeChecker_Env.use_eq =
                     (uu___416_10202.FStar_TypeChecker_Env.use_eq);
                   FStar_TypeChecker_Env.is_iface =
                     (uu___416_10202.FStar_TypeChecker_Env.is_iface);
                   FStar_TypeChecker_Env.admit =
                     (uu___416_10202.FStar_TypeChecker_Env.admit);
                   FStar_TypeChecker_Env.lax =
                     (uu___416_10202.FStar_TypeChecker_Env.lax);
                   FStar_TypeChecker_Env.lax_universes =
                     (uu___416_10202.FStar_TypeChecker_Env.lax_universes);
                   FStar_TypeChecker_Env.phase1 =
                     (uu___416_10202.FStar_TypeChecker_Env.phase1);
                   FStar_TypeChecker_Env.failhard =
                     (uu___416_10202.FStar_TypeChecker_Env.failhard);
                   FStar_TypeChecker_Env.nosynth =
                     (uu___416_10202.FStar_TypeChecker_Env.nosynth);
                   FStar_TypeChecker_Env.uvar_subtyping =
                     (uu___416_10202.FStar_TypeChecker_Env.uvar_subtyping);
                   FStar_TypeChecker_Env.tc_term =
                     (uu___416_10202.FStar_TypeChecker_Env.tc_term);
                   FStar_TypeChecker_Env.type_of =
                     (uu___416_10202.FStar_TypeChecker_Env.type_of);
                   FStar_TypeChecker_Env.universe_of =
                     (uu___416_10202.FStar_TypeChecker_Env.universe_of);
                   FStar_TypeChecker_Env.check_type_of =
                     (uu___416_10202.FStar_TypeChecker_Env.check_type_of);
                   FStar_TypeChecker_Env.use_bv_sorts =
                     (uu___416_10202.FStar_TypeChecker_Env.use_bv_sorts);
                   FStar_TypeChecker_Env.qtbl_name_and_index =
                     (uu___416_10202.FStar_TypeChecker_Env.qtbl_name_and_index);
                   FStar_TypeChecker_Env.normalized_eff_names =
                     (uu___416_10202.FStar_TypeChecker_Env.normalized_eff_names);
                   FStar_TypeChecker_Env.proof_ns =
                     (uu___416_10202.FStar_TypeChecker_Env.proof_ns);
                   FStar_TypeChecker_Env.synth_hook =
                     (uu___416_10202.FStar_TypeChecker_Env.synth_hook);
                   FStar_TypeChecker_Env.splice =
                     (uu___416_10202.FStar_TypeChecker_Env.splice);
                   FStar_TypeChecker_Env.is_native_tactic =
                     (uu___416_10202.FStar_TypeChecker_Env.is_native_tactic);
                   FStar_TypeChecker_Env.identifier_info =
                     (uu___416_10202.FStar_TypeChecker_Env.identifier_info);
                   FStar_TypeChecker_Env.tc_hooks =
                     (uu___416_10202.FStar_TypeChecker_Env.tc_hooks);
                   FStar_TypeChecker_Env.dsenv =
                     (uu___416_10202.FStar_TypeChecker_Env.dsenv);
                   FStar_TypeChecker_Env.dep_graph =
                     (uu___416_10202.FStar_TypeChecker_Env.dep_graph);
                   FStar_TypeChecker_Env.nbe =
                     (uu___416_10202.FStar_TypeChecker_Env.nbe)
                 }  in
               let g = FStar_Tactics_Types.mk_goal env1 ctx_uvar opts false
                  in
               let uu____10204 =
                 let uu____10207 = bnorm_goal g  in [uu____10207]  in
               add_goals uu____10204
           | uu____10208 -> fail "not a uvar")
       in
    FStar_All.pipe_left (wrap_err "unshelve") uu____10112
  
let (tac_and : Prims.bool tac -> Prims.bool tac -> Prims.bool tac) =
  fun t1  ->
    fun t2  ->
      let comp =
        bind t1
          (fun b  ->
             let uu____10257 = if b then t2 else ret false  in
             bind uu____10257 (fun b'  -> if b' then ret b' else fail ""))
         in
      let uu____10268 = trytac comp  in
      bind uu____10268
        (fun uu___351_10276  ->
           match uu___351_10276 with
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
        let uu____10302 =
          bind get
            (fun ps  ->
               let uu____10308 = __tc e t1  in
               bind uu____10308
                 (fun uu____10328  ->
                    match uu____10328 with
                    | (t11,ty1,g1) ->
                        let uu____10340 = __tc e t2  in
                        bind uu____10340
                          (fun uu____10360  ->
                             match uu____10360 with
                             | (t21,ty2,g2) ->
                                 let uu____10372 =
                                   proc_guard "unify_env g1" e g1  in
                                 bind uu____10372
                                   (fun uu____10377  ->
                                      let uu____10378 =
                                        proc_guard "unify_env g2" e g2  in
                                      bind uu____10378
                                        (fun uu____10384  ->
                                           let uu____10385 =
                                             do_unify e ty1 ty2  in
                                           let uu____10388 =
                                             do_unify e t11 t21  in
                                           tac_and uu____10385 uu____10388)))))
           in
        FStar_All.pipe_left (wrap_err "unify_env") uu____10302
  
let (launch_process :
  Prims.string -> Prims.string Prims.list -> Prims.string -> Prims.string tac)
  =
  fun prog  ->
    fun args  ->
      fun input  ->
        bind idtac
          (fun uu____10421  ->
             let uu____10422 = FStar_Options.unsafe_tactic_exec ()  in
             if uu____10422
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
        (fun uu____10443  ->
           let uu____10444 =
             FStar_Syntax_Syntax.gen_bv nm FStar_Pervasives_Native.None t  in
           ret uu____10444)
  
let (change : FStar_Reflection_Data.typ -> unit tac) =
  fun ty  ->
    let uu____10454 =
      mlog
        (fun uu____10459  ->
           let uu____10460 = FStar_Syntax_Print.term_to_string ty  in
           FStar_Util.print1 "change: ty = %s\n" uu____10460)
        (fun uu____10463  ->
           let uu____10464 = cur_goal ()  in
           bind uu____10464
             (fun g  ->
                let uu____10470 =
                  let uu____10479 = FStar_Tactics_Types.goal_env g  in
                  __tc uu____10479 ty  in
                bind uu____10470
                  (fun uu____10491  ->
                     match uu____10491 with
                     | (ty1,uu____10501,guard) ->
                         let uu____10503 =
                           let uu____10506 = FStar_Tactics_Types.goal_env g
                              in
                           proc_guard "change" uu____10506 guard  in
                         bind uu____10503
                           (fun uu____10509  ->
                              let uu____10510 =
                                let uu____10513 =
                                  FStar_Tactics_Types.goal_env g  in
                                let uu____10514 =
                                  FStar_Tactics_Types.goal_type g  in
                                do_unify uu____10513 uu____10514 ty1  in
                              bind uu____10510
                                (fun bb  ->
                                   if bb
                                   then
                                     let uu____10520 =
                                       FStar_Tactics_Types.goal_with_type g
                                         ty1
                                        in
                                     replace_cur uu____10520
                                   else
                                     (let steps =
                                        [FStar_TypeChecker_Env.AllowUnboundUniverses;
                                        FStar_TypeChecker_Env.UnfoldUntil
                                          FStar_Syntax_Syntax.delta_constant;
                                        FStar_TypeChecker_Env.Primops]  in
                                      let ng =
                                        let uu____10526 =
                                          FStar_Tactics_Types.goal_env g  in
                                        let uu____10527 =
                                          FStar_Tactics_Types.goal_type g  in
                                        normalize steps uu____10526
                                          uu____10527
                                         in
                                      let nty =
                                        let uu____10529 =
                                          FStar_Tactics_Types.goal_env g  in
                                        normalize steps uu____10529 ty1  in
                                      let uu____10530 =
                                        let uu____10533 =
                                          FStar_Tactics_Types.goal_env g  in
                                        do_unify uu____10533 ng nty  in
                                      bind uu____10530
                                        (fun b  ->
                                           if b
                                           then
                                             let uu____10539 =
                                               FStar_Tactics_Types.goal_with_type
                                                 g ty1
                                                in
                                             replace_cur uu____10539
                                           else fail "not convertible")))))))
       in
    FStar_All.pipe_left (wrap_err "change") uu____10454
  
let failwhen : 'a . Prims.bool -> Prims.string -> (unit -> 'a tac) -> 'a tac
  = fun b  -> fun msg  -> fun k  -> if b then fail msg else k () 
let (t_destruct :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.fv,FStar_BigInt.t) FStar_Pervasives_Native.tuple2
      Prims.list tac)
  =
  fun s_tm  ->
    let uu____10602 =
      let uu____10611 = cur_goal ()  in
      bind uu____10611
        (fun g  ->
           let uu____10623 =
             let uu____10632 = FStar_Tactics_Types.goal_env g  in
             __tc uu____10632 s_tm  in
           bind uu____10623
             (fun uu____10650  ->
                match uu____10650 with
                | (s_tm1,s_ty,guard) ->
                    let uu____10668 =
                      let uu____10671 = FStar_Tactics_Types.goal_env g  in
                      proc_guard "destruct" uu____10671 guard  in
                    bind uu____10668
                      (fun uu____10683  ->
                         let uu____10684 =
                           FStar_Syntax_Util.head_and_args' s_ty  in
                         match uu____10684 with
                         | (h,args) ->
                             let uu____10729 =
                               let uu____10736 =
                                 let uu____10737 =
                                   FStar_Syntax_Subst.compress h  in
                                 uu____10737.FStar_Syntax_Syntax.n  in
                               match uu____10736 with
                               | FStar_Syntax_Syntax.Tm_fvar fv ->
                                   ret (fv, [])
                               | FStar_Syntax_Syntax.Tm_uinst
                                   ({
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.Tm_fvar fv;
                                      FStar_Syntax_Syntax.pos = uu____10752;
                                      FStar_Syntax_Syntax.vars = uu____10753;_},us)
                                   -> ret (fv, us)
                               | uu____10763 -> fail "type is not an fv"  in
                             bind uu____10729
                               (fun uu____10783  ->
                                  match uu____10783 with
                                  | (fv,a_us) ->
                                      let t_lid =
                                        FStar_Syntax_Syntax.lid_of_fv fv  in
                                      let uu____10799 =
                                        let uu____10802 =
                                          FStar_Tactics_Types.goal_env g  in
                                        FStar_TypeChecker_Env.lookup_sigelt
                                          uu____10802 t_lid
                                         in
                                      (match uu____10799 with
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
                                                  (fun uu____10851  ->
                                                     let uu____10852 =
                                                       FStar_Syntax_Subst.open_term
                                                         t_ps t_ty
                                                        in
                                                     match uu____10852 with
                                                     | (t_ps1,t_ty1) ->
                                                         let uu____10867 =
                                                           mapM
                                                             (fun c_lid  ->
                                                                let uu____10895
                                                                  =
                                                                  let uu____10898
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    g  in
                                                                  FStar_TypeChecker_Env.lookup_sigelt
                                                                    uu____10898
                                                                    c_lid
                                                                   in
                                                                match uu____10895
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
                                                                    uu____10968
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
                                                                    let uu____10973
                                                                    =
                                                                    FStar_TypeChecker_Env.inst_tscheme
                                                                    (c_us,
                                                                    c_ty1)
                                                                     in
                                                                    match uu____10973
                                                                    with
                                                                    | 
                                                                    (c_us1,c_ty2)
                                                                    ->
                                                                    let uu____10996
                                                                    =
                                                                    FStar_Syntax_Util.arrow_formals_comp
                                                                    c_ty2  in
                                                                    (match uu____10996
                                                                    with
                                                                    | 
                                                                    (bs,comp)
                                                                    ->
                                                                    let uu____11039
                                                                    =
                                                                    FStar_List.splitAt
                                                                    nparam bs
                                                                     in
                                                                    (match uu____11039
                                                                    with
                                                                    | 
                                                                    (d_ps,bs1)
                                                                    ->
                                                                    let uu____11112
                                                                    =
                                                                    let uu____11113
                                                                    =
                                                                    FStar_Syntax_Util.is_total_comp
                                                                    comp  in
                                                                    Prims.op_Negation
                                                                    uu____11113
                                                                     in
                                                                    failwhen
                                                                    uu____11112
                                                                    "not total?"
                                                                    (fun
                                                                    uu____11130
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
                                                                    uu___352_11146
                                                                    =
                                                                    match uu___352_11146
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    (FStar_Syntax_Syntax.Implicit
                                                                    uu____11149)
                                                                    -> true
                                                                    | 
                                                                    uu____11150
                                                                    -> false
                                                                     in
                                                                    let uu____11153
                                                                    =
                                                                    FStar_List.splitAt
                                                                    nparam
                                                                    args  in
                                                                    match uu____11153
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
                                                                    uu____11286
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
                                                                    uu____11348
                                                                     ->
                                                                    match uu____11348
                                                                    with
                                                                    | 
                                                                    ((bv,uu____11368),
                                                                    (t,uu____11370))
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
                                                                    uu____11438
                                                                     ->
                                                                    match uu____11438
                                                                    with
                                                                    | 
                                                                    ((bv,uu____11464),
                                                                    (t,uu____11466))
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
                                                                    uu____11521
                                                                     ->
                                                                    match uu____11521
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
                                                                    let uu____11571
                                                                    =
                                                                    FStar_TypeChecker_TcTerm.tc_pat
                                                                    (let uu___417_11588
                                                                    = env  in
                                                                    {
                                                                    FStar_TypeChecker_Env.solver
                                                                    =
                                                                    (uu___417_11588.FStar_TypeChecker_Env.solver);
                                                                    FStar_TypeChecker_Env.range
                                                                    =
                                                                    (uu___417_11588.FStar_TypeChecker_Env.range);
                                                                    FStar_TypeChecker_Env.curmodule
                                                                    =
                                                                    (uu___417_11588.FStar_TypeChecker_Env.curmodule);
                                                                    FStar_TypeChecker_Env.gamma
                                                                    =
                                                                    (uu___417_11588.FStar_TypeChecker_Env.gamma);
                                                                    FStar_TypeChecker_Env.gamma_sig
                                                                    =
                                                                    (uu___417_11588.FStar_TypeChecker_Env.gamma_sig);
                                                                    FStar_TypeChecker_Env.gamma_cache
                                                                    =
                                                                    (uu___417_11588.FStar_TypeChecker_Env.gamma_cache);
                                                                    FStar_TypeChecker_Env.modules
                                                                    =
                                                                    (uu___417_11588.FStar_TypeChecker_Env.modules);
                                                                    FStar_TypeChecker_Env.expected_typ
                                                                    =
                                                                    (uu___417_11588.FStar_TypeChecker_Env.expected_typ);
                                                                    FStar_TypeChecker_Env.sigtab
                                                                    =
                                                                    (uu___417_11588.FStar_TypeChecker_Env.sigtab);
                                                                    FStar_TypeChecker_Env.attrtab
                                                                    =
                                                                    (uu___417_11588.FStar_TypeChecker_Env.attrtab);
                                                                    FStar_TypeChecker_Env.is_pattern
                                                                    =
                                                                    (uu___417_11588.FStar_TypeChecker_Env.is_pattern);
                                                                    FStar_TypeChecker_Env.instantiate_imp
                                                                    =
                                                                    (uu___417_11588.FStar_TypeChecker_Env.instantiate_imp);
                                                                    FStar_TypeChecker_Env.effects
                                                                    =
                                                                    (uu___417_11588.FStar_TypeChecker_Env.effects);
                                                                    FStar_TypeChecker_Env.generalize
                                                                    =
                                                                    (uu___417_11588.FStar_TypeChecker_Env.generalize);
                                                                    FStar_TypeChecker_Env.letrecs
                                                                    =
                                                                    (uu___417_11588.FStar_TypeChecker_Env.letrecs);
                                                                    FStar_TypeChecker_Env.top_level
                                                                    =
                                                                    (uu___417_11588.FStar_TypeChecker_Env.top_level);
                                                                    FStar_TypeChecker_Env.check_uvars
                                                                    =
                                                                    (uu___417_11588.FStar_TypeChecker_Env.check_uvars);
                                                                    FStar_TypeChecker_Env.use_eq
                                                                    =
                                                                    (uu___417_11588.FStar_TypeChecker_Env.use_eq);
                                                                    FStar_TypeChecker_Env.is_iface
                                                                    =
                                                                    (uu___417_11588.FStar_TypeChecker_Env.is_iface);
                                                                    FStar_TypeChecker_Env.admit
                                                                    =
                                                                    (uu___417_11588.FStar_TypeChecker_Env.admit);
                                                                    FStar_TypeChecker_Env.lax
                                                                    = true;
                                                                    FStar_TypeChecker_Env.lax_universes
                                                                    =
                                                                    (uu___417_11588.FStar_TypeChecker_Env.lax_universes);
                                                                    FStar_TypeChecker_Env.phase1
                                                                    =
                                                                    (uu___417_11588.FStar_TypeChecker_Env.phase1);
                                                                    FStar_TypeChecker_Env.failhard
                                                                    =
                                                                    (uu___417_11588.FStar_TypeChecker_Env.failhard);
                                                                    FStar_TypeChecker_Env.nosynth
                                                                    =
                                                                    (uu___417_11588.FStar_TypeChecker_Env.nosynth);
                                                                    FStar_TypeChecker_Env.uvar_subtyping
                                                                    =
                                                                    (uu___417_11588.FStar_TypeChecker_Env.uvar_subtyping);
                                                                    FStar_TypeChecker_Env.tc_term
                                                                    =
                                                                    (uu___417_11588.FStar_TypeChecker_Env.tc_term);
                                                                    FStar_TypeChecker_Env.type_of
                                                                    =
                                                                    (uu___417_11588.FStar_TypeChecker_Env.type_of);
                                                                    FStar_TypeChecker_Env.universe_of
                                                                    =
                                                                    (uu___417_11588.FStar_TypeChecker_Env.universe_of);
                                                                    FStar_TypeChecker_Env.check_type_of
                                                                    =
                                                                    (uu___417_11588.FStar_TypeChecker_Env.check_type_of);
                                                                    FStar_TypeChecker_Env.use_bv_sorts
                                                                    =
                                                                    (uu___417_11588.FStar_TypeChecker_Env.use_bv_sorts);
                                                                    FStar_TypeChecker_Env.qtbl_name_and_index
                                                                    =
                                                                    (uu___417_11588.FStar_TypeChecker_Env.qtbl_name_and_index);
                                                                    FStar_TypeChecker_Env.normalized_eff_names
                                                                    =
                                                                    (uu___417_11588.FStar_TypeChecker_Env.normalized_eff_names);
                                                                    FStar_TypeChecker_Env.proof_ns
                                                                    =
                                                                    (uu___417_11588.FStar_TypeChecker_Env.proof_ns);
                                                                    FStar_TypeChecker_Env.synth_hook
                                                                    =
                                                                    (uu___417_11588.FStar_TypeChecker_Env.synth_hook);
                                                                    FStar_TypeChecker_Env.splice
                                                                    =
                                                                    (uu___417_11588.FStar_TypeChecker_Env.splice);
                                                                    FStar_TypeChecker_Env.is_native_tactic
                                                                    =
                                                                    (uu___417_11588.FStar_TypeChecker_Env.is_native_tactic);
                                                                    FStar_TypeChecker_Env.identifier_info
                                                                    =
                                                                    (uu___417_11588.FStar_TypeChecker_Env.identifier_info);
                                                                    FStar_TypeChecker_Env.tc_hooks
                                                                    =
                                                                    (uu___417_11588.FStar_TypeChecker_Env.tc_hooks);
                                                                    FStar_TypeChecker_Env.dsenv
                                                                    =
                                                                    (uu___417_11588.FStar_TypeChecker_Env.dsenv);
                                                                    FStar_TypeChecker_Env.dep_graph
                                                                    =
                                                                    (uu___417_11588.FStar_TypeChecker_Env.dep_graph);
                                                                    FStar_TypeChecker_Env.nbe
                                                                    =
                                                                    (uu___417_11588.FStar_TypeChecker_Env.nbe)
                                                                    }) true
                                                                    s_ty pat
                                                                     in
                                                                    match uu____11571
                                                                    with
                                                                    | 
                                                                    (uu____11601,uu____11602,uu____11603,pat_t,uu____11605,uu____11606)
                                                                    ->
                                                                    let eq_b
                                                                    =
                                                                    let uu____11612
                                                                    =
                                                                    let uu____11613
                                                                    =
                                                                    FStar_Syntax_Util.mk_eq2
                                                                    equ s_ty
                                                                    s_tm1
                                                                    pat_t  in
                                                                    FStar_Syntax_Util.mk_squash
                                                                    equ
                                                                    uu____11613
                                                                     in
                                                                    FStar_Syntax_Syntax.gen_bv
                                                                    "breq"
                                                                    FStar_Pervasives_Native.None
                                                                    uu____11612
                                                                     in
                                                                    let cod1
                                                                    =
                                                                    let uu____11617
                                                                    =
                                                                    let uu____11626
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_binder
                                                                    eq_b  in
                                                                    [uu____11626]
                                                                     in
                                                                    let uu____11645
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Total
                                                                    cod  in
                                                                    FStar_Syntax_Util.arrow
                                                                    uu____11617
                                                                    uu____11645
                                                                     in
                                                                    let nty =
                                                                    let uu____11651
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Total
                                                                    cod1  in
                                                                    FStar_Syntax_Util.arrow
                                                                    bs2
                                                                    uu____11651
                                                                     in
                                                                    let uu____11654
                                                                    =
                                                                    new_uvar
                                                                    "destruct branch"
                                                                    env nty
                                                                     in
                                                                    bind
                                                                    uu____11654
                                                                    (fun
                                                                    uu____11683
                                                                     ->
                                                                    match uu____11683
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
                                                                    let uu____11709
                                                                    =
                                                                    let uu____11720
                                                                    =
                                                                    FStar_Syntax_Syntax.as_arg
                                                                    FStar_Syntax_Util.exp_unit
                                                                     in
                                                                    [uu____11720]
                                                                     in
                                                                    FStar_Syntax_Util.mk_app
                                                                    brt
                                                                    uu____11709
                                                                     in
                                                                    let br =
                                                                    FStar_Syntax_Subst.close_branch
                                                                    (pat,
                                                                    FStar_Pervasives_Native.None,
                                                                    brt1)  in
                                                                    let uu____11756
                                                                    =
                                                                    let uu____11767
                                                                    =
                                                                    let uu____11772
                                                                    =
                                                                    FStar_BigInt.of_int_fs
                                                                    (FStar_List.length
                                                                    bs2)  in
                                                                    (fv1,
                                                                    uu____11772)
                                                                     in
                                                                    (g', br,
                                                                    uu____11767)
                                                                     in
                                                                    ret
                                                                    uu____11756))))))
                                                                    | 
                                                                    uu____11793
                                                                    ->
                                                                    fail
                                                                    "impossible: not a ctor"))
                                                             c_lids
                                                            in
                                                         bind uu____10867
                                                           (fun goal_brs  ->
                                                              let uu____11842
                                                                =
                                                                FStar_List.unzip3
                                                                  goal_brs
                                                                 in
                                                              match uu____11842
                                                              with
                                                              | (goals1,brs,infos)
                                                                  ->
                                                                  let w =
                                                                    FStar_Syntax_Syntax.mk
                                                                    (FStar_Syntax_Syntax.Tm_match
                                                                    (s_tm1,
                                                                    brs))
                                                                    FStar_Pervasives_Native.None
                                                                    s_tm1.FStar_Syntax_Syntax.pos
                                                                     in
                                                                  let uu____11915
                                                                    =
                                                                    solve' g
                                                                    w  in
                                                                  bind
                                                                    uu____11915
                                                                    (
                                                                    fun
                                                                    uu____11926
                                                                     ->
                                                                    let uu____11927
                                                                    =
                                                                    add_goals
                                                                    goals1
                                                                     in
                                                                    bind
                                                                    uu____11927
                                                                    (fun
                                                                    uu____11937
                                                                     ->
                                                                    ret infos))))
                                            | uu____11944 ->
                                                fail "not an inductive type"))))))
       in
    FStar_All.pipe_left (wrap_err "destruct") uu____10602
  
let rec last : 'a . 'a Prims.list -> 'a =
  fun l  ->
    match l with
    | [] -> failwith "last: empty list"
    | x::[] -> x
    | uu____11989::xs -> last xs
  
let rec init : 'a . 'a Prims.list -> 'a Prims.list =
  fun l  ->
    match l with
    | [] -> failwith "init: empty list"
    | x::[] -> []
    | x::xs -> let uu____12017 = init xs  in x :: uu____12017
  
let rec (inspect :
  FStar_Syntax_Syntax.term -> FStar_Reflection_Data.term_view tac) =
  fun t  ->
    let uu____12029 =
      let t1 = FStar_Syntax_Util.unascribe t  in
      let t2 = FStar_Syntax_Util.un_uinst t1  in
      let t3 = FStar_Syntax_Util.unlazy_emb t2  in
      match t3.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_meta (t4,uu____12038) -> inspect t4
      | FStar_Syntax_Syntax.Tm_name bv ->
          FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_Var bv)
      | FStar_Syntax_Syntax.Tm_bvar bv ->
          FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_BVar bv)
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_FVar fv)
      | FStar_Syntax_Syntax.Tm_app (hd1,[]) ->
          failwith "empty arguments on Tm_app"
      | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
          let uu____12103 = last args  in
          (match uu____12103 with
           | (a,q) ->
               let q' = FStar_Reflection_Basic.inspect_aqual q  in
               let uu____12133 =
                 let uu____12134 =
                   let uu____12139 =
                     let uu____12140 =
                       let uu____12145 = init args  in
                       FStar_Syntax_Syntax.mk_Tm_app hd1 uu____12145  in
                     uu____12140 FStar_Pervasives_Native.None
                       t3.FStar_Syntax_Syntax.pos
                      in
                   (uu____12139, (a, q'))  in
                 FStar_Reflection_Data.Tv_App uu____12134  in
               FStar_All.pipe_left ret uu____12133)
      | FStar_Syntax_Syntax.Tm_abs ([],uu____12158,uu____12159) ->
          failwith "empty arguments on Tm_abs"
      | FStar_Syntax_Syntax.Tm_abs (bs,t4,k) ->
          let uu____12211 = FStar_Syntax_Subst.open_term bs t4  in
          (match uu____12211 with
           | (bs1,t5) ->
               (match bs1 with
                | [] -> failwith "impossible"
                | b::bs2 ->
                    let uu____12252 =
                      let uu____12253 =
                        let uu____12258 = FStar_Syntax_Util.abs bs2 t5 k  in
                        (b, uu____12258)  in
                      FStar_Reflection_Data.Tv_Abs uu____12253  in
                    FStar_All.pipe_left ret uu____12252))
      | FStar_Syntax_Syntax.Tm_type uu____12261 ->
          FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_Type ())
      | FStar_Syntax_Syntax.Tm_arrow ([],k) ->
          failwith "empty binders on arrow"
      | FStar_Syntax_Syntax.Tm_arrow uu____12285 ->
          let uu____12300 = FStar_Syntax_Util.arrow_one t3  in
          (match uu____12300 with
           | FStar_Pervasives_Native.Some (b,c) ->
               FStar_All.pipe_left ret
                 (FStar_Reflection_Data.Tv_Arrow (b, c))
           | FStar_Pervasives_Native.None  -> failwith "impossible")
      | FStar_Syntax_Syntax.Tm_refine (bv,t4) ->
          let b = FStar_Syntax_Syntax.mk_binder bv  in
          let uu____12330 = FStar_Syntax_Subst.open_term [b] t4  in
          (match uu____12330 with
           | (b',t5) ->
               let b1 =
                 match b' with
                 | b'1::[] -> b'1
                 | uu____12383 -> failwith "impossible"  in
               FStar_All.pipe_left ret
                 (FStar_Reflection_Data.Tv_Refine
                    ((FStar_Pervasives_Native.fst b1), t5)))
      | FStar_Syntax_Syntax.Tm_constant c ->
          let uu____12395 =
            let uu____12396 = FStar_Reflection_Basic.inspect_const c  in
            FStar_Reflection_Data.Tv_Const uu____12396  in
          FStar_All.pipe_left ret uu____12395
      | FStar_Syntax_Syntax.Tm_uvar (ctx_u,s) ->
          let uu____12417 =
            let uu____12418 =
              let uu____12423 =
                let uu____12424 =
                  FStar_Syntax_Unionfind.uvar_id
                    ctx_u.FStar_Syntax_Syntax.ctx_uvar_head
                   in
                FStar_BigInt.of_int_fs uu____12424  in
              (uu____12423, (ctx_u, s))  in
            FStar_Reflection_Data.Tv_Uvar uu____12418  in
          FStar_All.pipe_left ret uu____12417
      | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),t21) ->
          if lb.FStar_Syntax_Syntax.lbunivs <> []
          then FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown
          else
            (match lb.FStar_Syntax_Syntax.lbname with
             | FStar_Util.Inr uu____12458 ->
                 FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown
             | FStar_Util.Inl bv ->
                 let b = FStar_Syntax_Syntax.mk_binder bv  in
                 let uu____12463 = FStar_Syntax_Subst.open_term [b] t21  in
                 (match uu____12463 with
                  | (bs,t22) ->
                      let b1 =
                        match bs with
                        | b1::[] -> b1
                        | uu____12516 ->
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
             | FStar_Util.Inr uu____12550 ->
                 FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown
             | FStar_Util.Inl bv ->
                 let uu____12554 = FStar_Syntax_Subst.open_let_rec [lb] t21
                    in
                 (match uu____12554 with
                  | (lbs,t22) ->
                      (match lbs with
                       | lb1::[] ->
                           (match lb1.FStar_Syntax_Syntax.lbname with
                            | FStar_Util.Inr uu____12574 ->
                                ret FStar_Reflection_Data.Tv_Unknown
                            | FStar_Util.Inl bv1 ->
                                FStar_All.pipe_left ret
                                  (FStar_Reflection_Data.Tv_Let
                                     (true, bv1,
                                       (lb1.FStar_Syntax_Syntax.lbdef), t22)))
                       | uu____12578 ->
                           failwith
                             "impossible: open_term returned different amount of binders")))
      | FStar_Syntax_Syntax.Tm_match (t4,brs) ->
          let rec inspect_pat p =
            match p.FStar_Syntax_Syntax.v with
            | FStar_Syntax_Syntax.Pat_constant c ->
                let uu____12632 = FStar_Reflection_Basic.inspect_const c  in
                FStar_Reflection_Data.Pat_Constant uu____12632
            | FStar_Syntax_Syntax.Pat_cons (fv,ps) ->
                let uu____12651 =
                  let uu____12658 =
                    FStar_List.map
                      (fun uu____12670  ->
                         match uu____12670 with
                         | (p1,uu____12678) -> inspect_pat p1) ps
                     in
                  (fv, uu____12658)  in
                FStar_Reflection_Data.Pat_Cons uu____12651
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
              (fun uu___353_12772  ->
                 match uu___353_12772 with
                 | (pat,uu____12794,t5) ->
                     let uu____12812 = inspect_pat pat  in (uu____12812, t5))
              brs1
             in
          FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_Match (t4, brs2))
      | FStar_Syntax_Syntax.Tm_unknown  ->
          FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown
      | uu____12821 ->
          ((let uu____12823 =
              let uu____12828 =
                let uu____12829 = FStar_Syntax_Print.tag_of_term t3  in
                let uu____12830 = FStar_Syntax_Print.term_to_string t3  in
                FStar_Util.format2
                  "inspect: outside of expected syntax (%s, %s)\n"
                  uu____12829 uu____12830
                 in
              (FStar_Errors.Warning_CantInspect, uu____12828)  in
            FStar_Errors.log_issue t3.FStar_Syntax_Syntax.pos uu____12823);
           FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown)
       in
    wrap_err "inspect" uu____12029
  
let (pack : FStar_Reflection_Data.term_view -> FStar_Syntax_Syntax.term tac)
  =
  fun tv  ->
    match tv with
    | FStar_Reflection_Data.Tv_Var bv ->
        let uu____12843 = FStar_Syntax_Syntax.bv_to_name bv  in
        FStar_All.pipe_left ret uu____12843
    | FStar_Reflection_Data.Tv_BVar bv ->
        let uu____12847 = FStar_Syntax_Syntax.bv_to_tm bv  in
        FStar_All.pipe_left ret uu____12847
    | FStar_Reflection_Data.Tv_FVar fv ->
        let uu____12851 = FStar_Syntax_Syntax.fv_to_tm fv  in
        FStar_All.pipe_left ret uu____12851
    | FStar_Reflection_Data.Tv_App (l,(r,q)) ->
        let q' = FStar_Reflection_Basic.pack_aqual q  in
        let uu____12858 = FStar_Syntax_Util.mk_app l [(r, q')]  in
        FStar_All.pipe_left ret uu____12858
    | FStar_Reflection_Data.Tv_Abs (b,t) ->
        let uu____12883 =
          FStar_Syntax_Util.abs [b] t FStar_Pervasives_Native.None  in
        FStar_All.pipe_left ret uu____12883
    | FStar_Reflection_Data.Tv_Arrow (b,c) ->
        let uu____12900 = FStar_Syntax_Util.arrow [b] c  in
        FStar_All.pipe_left ret uu____12900
    | FStar_Reflection_Data.Tv_Type () ->
        FStar_All.pipe_left ret FStar_Syntax_Util.ktype
    | FStar_Reflection_Data.Tv_Refine (bv,t) ->
        let uu____12919 = FStar_Syntax_Util.refine bv t  in
        FStar_All.pipe_left ret uu____12919
    | FStar_Reflection_Data.Tv_Const c ->
        let uu____12923 =
          let uu____12924 =
            let uu____12931 =
              let uu____12932 = FStar_Reflection_Basic.pack_const c  in
              FStar_Syntax_Syntax.Tm_constant uu____12932  in
            FStar_Syntax_Syntax.mk uu____12931  in
          uu____12924 FStar_Pervasives_Native.None FStar_Range.dummyRange  in
        FStar_All.pipe_left ret uu____12923
    | FStar_Reflection_Data.Tv_Uvar (_u,ctx_u_s) ->
        let uu____12940 =
          FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_uvar ctx_u_s)
            FStar_Pervasives_Native.None FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____12940
    | FStar_Reflection_Data.Tv_Let (false ,bv,t1,t2) ->
        let lb =
          FStar_Syntax_Util.mk_letbinding (FStar_Util.Inl bv) []
            bv.FStar_Syntax_Syntax.sort FStar_Parser_Const.effect_Tot_lid t1
            [] FStar_Range.dummyRange
           in
        let uu____12949 =
          let uu____12950 =
            let uu____12957 =
              let uu____12958 =
                let uu____12971 =
                  let uu____12974 =
                    let uu____12975 = FStar_Syntax_Syntax.mk_binder bv  in
                    [uu____12975]  in
                  FStar_Syntax_Subst.close uu____12974 t2  in
                ((false, [lb]), uu____12971)  in
              FStar_Syntax_Syntax.Tm_let uu____12958  in
            FStar_Syntax_Syntax.mk uu____12957  in
          uu____12950 FStar_Pervasives_Native.None FStar_Range.dummyRange  in
        FStar_All.pipe_left ret uu____12949
    | FStar_Reflection_Data.Tv_Let (true ,bv,t1,t2) ->
        let lb =
          FStar_Syntax_Util.mk_letbinding (FStar_Util.Inl bv) []
            bv.FStar_Syntax_Syntax.sort FStar_Parser_Const.effect_Tot_lid t1
            [] FStar_Range.dummyRange
           in
        let uu____13015 = FStar_Syntax_Subst.close_let_rec [lb] t2  in
        (match uu____13015 with
         | (lbs,body) ->
             let uu____13030 =
               FStar_Syntax_Syntax.mk
                 (FStar_Syntax_Syntax.Tm_let ((true, lbs), body))
                 FStar_Pervasives_Native.None FStar_Range.dummyRange
                in
             FStar_All.pipe_left ret uu____13030)
    | FStar_Reflection_Data.Tv_Match (t,brs) ->
        let wrap v1 =
          {
            FStar_Syntax_Syntax.v = v1;
            FStar_Syntax_Syntax.p = FStar_Range.dummyRange
          }  in
        let rec pack_pat p =
          match p with
          | FStar_Reflection_Data.Pat_Constant c ->
              let uu____13064 =
                let uu____13065 = FStar_Reflection_Basic.pack_const c  in
                FStar_Syntax_Syntax.Pat_constant uu____13065  in
              FStar_All.pipe_left wrap uu____13064
          | FStar_Reflection_Data.Pat_Cons (fv,ps) ->
              let uu____13072 =
                let uu____13073 =
                  let uu____13086 =
                    FStar_List.map
                      (fun p1  ->
                         let uu____13102 = pack_pat p1  in
                         (uu____13102, false)) ps
                     in
                  (fv, uu____13086)  in
                FStar_Syntax_Syntax.Pat_cons uu____13073  in
              FStar_All.pipe_left wrap uu____13072
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
            (fun uu___354_13148  ->
               match uu___354_13148 with
               | (pat,t1) ->
                   let uu____13165 = pack_pat pat  in
                   (uu____13165, FStar_Pervasives_Native.None, t1)) brs
           in
        let brs2 = FStar_List.map FStar_Syntax_Subst.close_branch brs1  in
        let uu____13213 =
          FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_match (t, brs2))
            FStar_Pervasives_Native.None FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____13213
    | FStar_Reflection_Data.Tv_AscribedT (e,t,tacopt) ->
        let uu____13241 =
          FStar_Syntax_Syntax.mk
            (FStar_Syntax_Syntax.Tm_ascribed
               (e, ((FStar_Util.Inl t), tacopt),
                 FStar_Pervasives_Native.None)) FStar_Pervasives_Native.None
            FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____13241
    | FStar_Reflection_Data.Tv_AscribedC (e,c,tacopt) ->
        let uu____13287 =
          FStar_Syntax_Syntax.mk
            (FStar_Syntax_Syntax.Tm_ascribed
               (e, ((FStar_Util.Inr c), tacopt),
                 FStar_Pervasives_Native.None)) FStar_Pervasives_Native.None
            FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____13287
    | FStar_Reflection_Data.Tv_Unknown  ->
        let uu____13326 =
          FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown
            FStar_Pervasives_Native.None FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____13326
  
let (lget :
  FStar_Reflection_Data.typ -> Prims.string -> FStar_Syntax_Syntax.term tac)
  =
  fun ty  ->
    fun k  ->
      let uu____13343 =
        bind get
          (fun ps  ->
             let uu____13349 =
               FStar_Util.psmap_try_find ps.FStar_Tactics_Types.local_state k
                in
             match uu____13349 with
             | FStar_Pervasives_Native.None  -> fail "not found"
             | FStar_Pervasives_Native.Some t -> unquote ty t)
         in
      FStar_All.pipe_left (wrap_err "lget") uu____13343
  
let (lset :
  FStar_Reflection_Data.typ ->
    Prims.string -> FStar_Syntax_Syntax.term -> unit tac)
  =
  fun _ty  ->
    fun k  ->
      fun t  ->
        let uu____13378 =
          bind get
            (fun ps  ->
               let ps1 =
                 let uu___418_13385 = ps  in
                 let uu____13386 =
                   FStar_Util.psmap_add ps.FStar_Tactics_Types.local_state k
                     t
                    in
                 {
                   FStar_Tactics_Types.main_context =
                     (uu___418_13385.FStar_Tactics_Types.main_context);
                   FStar_Tactics_Types.main_goal =
                     (uu___418_13385.FStar_Tactics_Types.main_goal);
                   FStar_Tactics_Types.all_implicits =
                     (uu___418_13385.FStar_Tactics_Types.all_implicits);
                   FStar_Tactics_Types.goals =
                     (uu___418_13385.FStar_Tactics_Types.goals);
                   FStar_Tactics_Types.smt_goals =
                     (uu___418_13385.FStar_Tactics_Types.smt_goals);
                   FStar_Tactics_Types.depth =
                     (uu___418_13385.FStar_Tactics_Types.depth);
                   FStar_Tactics_Types.__dump =
                     (uu___418_13385.FStar_Tactics_Types.__dump);
                   FStar_Tactics_Types.psc =
                     (uu___418_13385.FStar_Tactics_Types.psc);
                   FStar_Tactics_Types.entry_range =
                     (uu___418_13385.FStar_Tactics_Types.entry_range);
                   FStar_Tactics_Types.guard_policy =
                     (uu___418_13385.FStar_Tactics_Types.guard_policy);
                   FStar_Tactics_Types.freshness =
                     (uu___418_13385.FStar_Tactics_Types.freshness);
                   FStar_Tactics_Types.tac_verb_dbg =
                     (uu___418_13385.FStar_Tactics_Types.tac_verb_dbg);
                   FStar_Tactics_Types.local_state = uu____13386
                 }  in
               set ps1)
           in
        FStar_All.pipe_left (wrap_err "lset") uu____13378
  
let (goal_of_goal_ty :
  env ->
    FStar_Reflection_Data.typ ->
      (FStar_Tactics_Types.goal,FStar_TypeChecker_Env.guard_t)
        FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun typ  ->
      let uu____13411 =
        FStar_TypeChecker_Util.new_implicit_var "proofstate_of_goal_ty"
          typ.FStar_Syntax_Syntax.pos env typ
         in
      match uu____13411 with
      | (u,ctx_uvars,g_u) ->
          let uu____13443 = FStar_List.hd ctx_uvars  in
          (match uu____13443 with
           | (ctx_uvar,uu____13457) ->
               let g =
                 let uu____13459 = FStar_Options.peek ()  in
                 FStar_Tactics_Types.mk_goal env ctx_uvar uu____13459 false
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
        let uu____13479 = goal_of_goal_ty env typ  in
        match uu____13479 with
        | (g,g_u) ->
            let ps =
              let uu____13491 =
                FStar_TypeChecker_Env.debug env
                  (FStar_Options.Other "TacVerbose")
                 in
              let uu____13492 = FStar_Util.psmap_empty ()  in
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
                FStar_Tactics_Types.tac_verb_dbg = uu____13491;
                FStar_Tactics_Types.local_state = uu____13492
              }  in
            let uu____13499 = FStar_Tactics_Types.goal_witness g  in
            (ps, uu____13499)
  