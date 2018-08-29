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
        (try (fun uu___359_158  -> match () with | () -> run t p) ()
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
         let maybe_label =
           match g.FStar_Tactics_Types.label with
           | "" -> ""
           | l -> Prims.strcat "Label: " (Prims.strcat l "\n")  in
         let uu____322 =
           FStar_Syntax_Print.binders_to_string ", "
             (g.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_binders
            in
         let uu____323 =
           let uu____324 = FStar_Tactics_Types.goal_env g  in
           tts uu____324
             (g.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_typ
            in
         FStar_Util.format4 "%s%s |- %s : %s" maybe_label uu____322 w
           uu____323)
  
let (tacprint : Prims.string -> unit) =
  fun s  -> FStar_Util.print1 "TAC>> %s\n" s 
let (tacprint1 : Prims.string -> Prims.string -> unit) =
  fun s  ->
    fun x  ->
      let uu____340 = FStar_Util.format1 s x  in
      FStar_Util.print1 "TAC>> %s\n" uu____340
  
let (tacprint2 : Prims.string -> Prims.string -> Prims.string -> unit) =
  fun s  ->
    fun x  ->
      fun y  ->
        let uu____356 = FStar_Util.format2 s x y  in
        FStar_Util.print1 "TAC>> %s\n" uu____356
  
let (tacprint3 :
  Prims.string -> Prims.string -> Prims.string -> Prims.string -> unit) =
  fun s  ->
    fun x  ->
      fun y  ->
        fun z  ->
          let uu____377 = FStar_Util.format3 s x y z  in
          FStar_Util.print1 "TAC>> %s\n" uu____377
  
let (comp_to_typ : FStar_Syntax_Syntax.comp -> FStar_Reflection_Data.typ) =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Total (t,uu____384) -> t
    | FStar_Syntax_Syntax.GTotal (t,uu____394) -> t
    | FStar_Syntax_Syntax.Comp ct -> ct.FStar_Syntax_Syntax.result_typ
  
let (get_phi :
  FStar_Tactics_Types.goal ->
    FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun g  ->
    let uu____413 =
      let uu____414 = FStar_Tactics_Types.goal_env g  in
      let uu____415 = FStar_Tactics_Types.goal_type g  in
      FStar_TypeChecker_Normalize.unfold_whnf uu____414 uu____415  in
    FStar_Syntax_Util.un_squash uu____413
  
let (is_irrelevant : FStar_Tactics_Types.goal -> Prims.bool) =
  fun g  -> let uu____421 = get_phi g  in FStar_Option.isSome uu____421 
let (print : Prims.string -> unit tac) = fun msg  -> tacprint msg; ret () 
let (debugging : unit -> Prims.bool tac) =
  fun uu____440  ->
    bind get
      (fun ps  ->
         let uu____446 =
           FStar_TypeChecker_Env.debug ps.FStar_Tactics_Types.main_context
             (FStar_Options.Other "Tac")
            in
         ret uu____446)
  
let (dump_goal :
  FStar_Tactics_Types.proofstate -> FStar_Tactics_Types.goal -> unit) =
  fun ps  ->
    fun goal  ->
      let uu____458 = goal_to_string ps goal  in tacprint uu____458
  
let (dump_cur : FStar_Tactics_Types.proofstate -> Prims.string -> unit) =
  fun ps  ->
    fun msg  ->
      match ps.FStar_Tactics_Types.goals with
      | [] -> tacprint1 "No more goals (%s)" msg
      | h::uu____470 ->
          (tacprint1 "Current goal (%s):" msg;
           (let uu____474 = FStar_List.hd ps.FStar_Tactics_Types.goals  in
            dump_goal ps uu____474))
  
let (ps_to_string :
  (Prims.string,FStar_Tactics_Types.proofstate)
    FStar_Pervasives_Native.tuple2 -> Prims.string)
  =
  fun uu____483  ->
    match uu____483 with
    | (msg,ps) ->
        let p_imp imp =
          FStar_Syntax_Print.uvar_to_string
            (imp.FStar_TypeChecker_Env.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_head
           in
        let uu____496 =
          let uu____499 =
            let uu____500 =
              FStar_Util.string_of_int ps.FStar_Tactics_Types.depth  in
            FStar_Util.format2 "State dump @ depth %s (%s):\n" uu____500 msg
             in
          let uu____501 =
            let uu____504 =
              if ps.FStar_Tactics_Types.entry_range <> FStar_Range.dummyRange
              then
                let uu____505 =
                  FStar_Range.string_of_def_range
                    ps.FStar_Tactics_Types.entry_range
                   in
                FStar_Util.format1 "Location: %s\n" uu____505
              else ""  in
            let uu____507 =
              let uu____510 =
                let uu____511 =
                  FStar_TypeChecker_Env.debug
                    ps.FStar_Tactics_Types.main_context
                    (FStar_Options.Other "Imp")
                   in
                if uu____511
                then
                  let uu____512 =
                    FStar_Common.string_of_list p_imp
                      ps.FStar_Tactics_Types.all_implicits
                     in
                  FStar_Util.format1 "Imps: %s\n" uu____512
                else ""  in
              let uu____514 =
                let uu____517 =
                  let uu____518 =
                    FStar_Util.string_of_int
                      (FStar_List.length ps.FStar_Tactics_Types.goals)
                     in
                  let uu____519 =
                    let uu____520 =
                      FStar_List.map (goal_to_string ps)
                        ps.FStar_Tactics_Types.goals
                       in
                    FStar_String.concat "\n" uu____520  in
                  FStar_Util.format2 "ACTIVE goals (%s):\n%s\n" uu____518
                    uu____519
                   in
                let uu____523 =
                  let uu____526 =
                    let uu____527 =
                      FStar_Util.string_of_int
                        (FStar_List.length ps.FStar_Tactics_Types.smt_goals)
                       in
                    let uu____528 =
                      let uu____529 =
                        FStar_List.map (goal_to_string ps)
                          ps.FStar_Tactics_Types.smt_goals
                         in
                      FStar_String.concat "\n" uu____529  in
                    FStar_Util.format2 "SMT goals (%s):\n%s\n" uu____527
                      uu____528
                     in
                  [uu____526]  in
                uu____517 :: uu____523  in
              uu____510 :: uu____514  in
            uu____504 :: uu____507  in
          uu____499 :: uu____501  in
        FStar_String.concat "" uu____496
  
let (goal_to_json : FStar_Tactics_Types.goal -> FStar_Util.json) =
  fun g  ->
    let g_binders =
      let uu____538 =
        let uu____539 = FStar_Tactics_Types.goal_env g  in
        FStar_TypeChecker_Env.all_binders uu____539  in
      let uu____540 =
        let uu____545 =
          let uu____546 = FStar_Tactics_Types.goal_env g  in
          FStar_TypeChecker_Env.dsenv uu____546  in
        FStar_Syntax_Print.binders_to_json uu____545  in
      FStar_All.pipe_right uu____538 uu____540  in
    let uu____547 =
      let uu____554 =
        let uu____561 =
          let uu____566 =
            let uu____567 =
              let uu____574 =
                let uu____579 =
                  let uu____580 =
                    let uu____581 = FStar_Tactics_Types.goal_env g  in
                    let uu____582 = FStar_Tactics_Types.goal_witness g  in
                    tts uu____581 uu____582  in
                  FStar_Util.JsonStr uu____580  in
                ("witness", uu____579)  in
              let uu____583 =
                let uu____590 =
                  let uu____595 =
                    let uu____596 =
                      let uu____597 = FStar_Tactics_Types.goal_env g  in
                      let uu____598 = FStar_Tactics_Types.goal_type g  in
                      tts uu____597 uu____598  in
                    FStar_Util.JsonStr uu____596  in
                  ("type", uu____595)  in
                [uu____590;
                ("label", (FStar_Util.JsonStr (g.FStar_Tactics_Types.label)))]
                 in
              uu____574 :: uu____583  in
            FStar_Util.JsonAssoc uu____567  in
          ("goal", uu____566)  in
        [uu____561]  in
      ("hyps", g_binders) :: uu____554  in
    FStar_Util.JsonAssoc uu____547
  
let (ps_to_json :
  (Prims.string,FStar_Tactics_Types.proofstate)
    FStar_Pervasives_Native.tuple2 -> FStar_Util.json)
  =
  fun uu____635  ->
    match uu____635 with
    | (msg,ps) ->
        let uu____642 =
          let uu____649 =
            let uu____656 =
              let uu____663 =
                let uu____670 =
                  let uu____675 =
                    let uu____676 =
                      FStar_List.map goal_to_json
                        ps.FStar_Tactics_Types.goals
                       in
                    FStar_Util.JsonList uu____676  in
                  ("goals", uu____675)  in
                let uu____679 =
                  let uu____686 =
                    let uu____691 =
                      let uu____692 =
                        FStar_List.map goal_to_json
                          ps.FStar_Tactics_Types.smt_goals
                         in
                      FStar_Util.JsonList uu____692  in
                    ("smt-goals", uu____691)  in
                  [uu____686]  in
                uu____670 :: uu____679  in
              ("depth", (FStar_Util.JsonInt (ps.FStar_Tactics_Types.depth)))
                :: uu____663
               in
            ("label", (FStar_Util.JsonStr msg)) :: uu____656  in
          let uu____715 =
            if ps.FStar_Tactics_Types.entry_range <> FStar_Range.dummyRange
            then
              let uu____728 =
                let uu____733 =
                  FStar_Range.json_of_def_range
                    ps.FStar_Tactics_Types.entry_range
                   in
                ("location", uu____733)  in
              [uu____728]
            else []  in
          FStar_List.append uu____649 uu____715  in
        FStar_Util.JsonAssoc uu____642
  
let (dump_proofstate :
  FStar_Tactics_Types.proofstate -> Prims.string -> unit) =
  fun ps  ->
    fun msg  ->
      FStar_Options.with_saved_options
        (fun uu____763  ->
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
         (let uu____786 = FStar_Tactics_Types.subst_proof_state subst1 ps  in
          dump_cur uu____786 msg);
         FStar_Tactics_Result.Success ((), ps))
  
let (print_proof_state : Prims.string -> unit tac) =
  fun msg  ->
    mk_tac
      (fun ps  ->
         let psc = ps.FStar_Tactics_Types.psc  in
         let subst1 = FStar_TypeChecker_Cfg.psc_subst psc  in
         (let uu____804 = FStar_Tactics_Types.subst_proof_state subst1 ps  in
          dump_proofstate uu____804 msg);
         FStar_Tactics_Result.Success ((), ps))
  
let mlog : 'a . (unit -> unit) -> (unit -> 'a tac) -> 'a tac =
  fun f  -> fun cont  -> bind get (fun ps  -> log ps f; cont ()) 
let fail : 'a . Prims.string -> 'a tac =
  fun msg  ->
    mk_tac
      (fun ps  ->
         (let uu____858 =
            FStar_TypeChecker_Env.debug ps.FStar_Tactics_Types.main_context
              (FStar_Options.Other "TacFail")
             in
          if uu____858
          then dump_proofstate ps (Prims.strcat "TACTIC FAILING: " msg)
          else ());
         FStar_Tactics_Result.Failed (msg, ps))
  
let fail1 : 'Auu____866 . Prims.string -> Prims.string -> 'Auu____866 tac =
  fun msg  ->
    fun x  -> let uu____879 = FStar_Util.format1 msg x  in fail uu____879
  
let fail2 :
  'Auu____888 .
    Prims.string -> Prims.string -> Prims.string -> 'Auu____888 tac
  =
  fun msg  ->
    fun x  ->
      fun y  -> let uu____906 = FStar_Util.format2 msg x y  in fail uu____906
  
let fail3 :
  'Auu____917 .
    Prims.string ->
      Prims.string -> Prims.string -> Prims.string -> 'Auu____917 tac
  =
  fun msg  ->
    fun x  ->
      fun y  ->
        fun z  ->
          let uu____940 = FStar_Util.format3 msg x y z  in fail uu____940
  
let fail4 :
  'Auu____953 .
    Prims.string ->
      Prims.string ->
        Prims.string -> Prims.string -> Prims.string -> 'Auu____953 tac
  =
  fun msg  ->
    fun x  ->
      fun y  ->
        fun z  ->
          fun w  ->
            let uu____981 = FStar_Util.format4 msg x y z w  in fail uu____981
  
let catch : 'a . 'a tac -> (Prims.string,'a) FStar_Util.either tac =
  fun t  ->
    mk_tac
      (fun ps  ->
         let tx = FStar_Syntax_Unionfind.new_transaction ()  in
         let uu____1014 = run t ps  in
         match uu____1014 with
         | FStar_Tactics_Result.Success (a,q) ->
             (FStar_Syntax_Unionfind.commit tx;
              FStar_Tactics_Result.Success ((FStar_Util.Inr a), q))
         | FStar_Tactics_Result.Failed (m,q) ->
             (FStar_Syntax_Unionfind.rollback tx;
              (let ps1 =
                 let uu___360_1038 = ps  in
                 {
                   FStar_Tactics_Types.main_context =
                     (uu___360_1038.FStar_Tactics_Types.main_context);
                   FStar_Tactics_Types.main_goal =
                     (uu___360_1038.FStar_Tactics_Types.main_goal);
                   FStar_Tactics_Types.all_implicits =
                     (uu___360_1038.FStar_Tactics_Types.all_implicits);
                   FStar_Tactics_Types.goals =
                     (uu___360_1038.FStar_Tactics_Types.goals);
                   FStar_Tactics_Types.smt_goals =
                     (uu___360_1038.FStar_Tactics_Types.smt_goals);
                   FStar_Tactics_Types.depth =
                     (uu___360_1038.FStar_Tactics_Types.depth);
                   FStar_Tactics_Types.__dump =
                     (uu___360_1038.FStar_Tactics_Types.__dump);
                   FStar_Tactics_Types.psc =
                     (uu___360_1038.FStar_Tactics_Types.psc);
                   FStar_Tactics_Types.entry_range =
                     (uu___360_1038.FStar_Tactics_Types.entry_range);
                   FStar_Tactics_Types.guard_policy =
                     (uu___360_1038.FStar_Tactics_Types.guard_policy);
                   FStar_Tactics_Types.freshness =
                     (q.FStar_Tactics_Types.freshness);
                   FStar_Tactics_Types.tac_verb_dbg =
                     (uu___360_1038.FStar_Tactics_Types.tac_verb_dbg);
                   FStar_Tactics_Types.local_state =
                     (uu___360_1038.FStar_Tactics_Types.local_state)
                 }  in
               FStar_Tactics_Result.Success ((FStar_Util.Inl m), ps1))))
  
let trytac : 'a . 'a tac -> 'a FStar_Pervasives_Native.option tac =
  fun t  ->
    let uu____1065 = catch t  in
    bind uu____1065
      (fun r  ->
         match r with
         | FStar_Util.Inr v1 -> ret (FStar_Pervasives_Native.Some v1)
         | FStar_Util.Inl uu____1092 -> ret FStar_Pervasives_Native.None)
  
let trytac_exn : 'a . 'a tac -> 'a FStar_Pervasives_Native.option tac =
  fun t  ->
    mk_tac
      (fun ps  ->
         try
           (fun uu___362_1123  ->
              match () with
              | () -> let uu____1128 = trytac t  in run uu____1128 ps) ()
         with
         | FStar_Errors.Err (uu____1144,msg) ->
             (log ps
                (fun uu____1148  ->
                   FStar_Util.print1 "trytac_exn error: (%s)" msg);
              FStar_Tactics_Result.Success (FStar_Pervasives_Native.None, ps))
         | FStar_Errors.Error (uu____1153,msg,uu____1155) ->
             (log ps
                (fun uu____1158  ->
                   FStar_Util.print1 "trytac_exn error: (%s)" msg);
              FStar_Tactics_Result.Success (FStar_Pervasives_Native.None, ps)))
  
let wrap_err : 'a . Prims.string -> 'a tac -> 'a tac =
  fun pref  ->
    fun t  ->
      mk_tac
        (fun ps  ->
           let uu____1191 = run t ps  in
           match uu____1191 with
           | FStar_Tactics_Result.Success (a,q) ->
               FStar_Tactics_Result.Success (a, q)
           | FStar_Tactics_Result.Failed (msg,q) ->
               FStar_Tactics_Result.Failed
                 ((Prims.strcat pref (Prims.strcat ": " msg)), q))
  
let (set : FStar_Tactics_Types.proofstate -> unit tac) =
  fun p  -> mk_tac (fun uu____1210  -> FStar_Tactics_Result.Success ((), p)) 
let (add_implicits : implicits -> unit tac) =
  fun i  ->
    bind get
      (fun p  ->
         set
           (let uu___363_1224 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___363_1224.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___363_1224.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (FStar_List.append i p.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___363_1224.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (uu___363_1224.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___363_1224.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___363_1224.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___363_1224.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___363_1224.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___363_1224.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___363_1224.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___363_1224.FStar_Tactics_Types.tac_verb_dbg);
              FStar_Tactics_Types.local_state =
                (uu___363_1224.FStar_Tactics_Types.local_state)
            }))
  
let (__do_unify :
  env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.bool tac)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        (let uu____1245 =
           FStar_TypeChecker_Env.debug env (FStar_Options.Other "1346")  in
         if uu____1245
         then
           let uu____1246 = FStar_Syntax_Print.term_to_string t1  in
           let uu____1247 = FStar_Syntax_Print.term_to_string t2  in
           FStar_Util.print2 "%%%%%%%%do_unify %s =? %s\n" uu____1246
             uu____1247
         else ());
        (try
           (fun uu___365_1254  ->
              match () with
              | () ->
                  let res = FStar_TypeChecker_Rel.teq_nosmt env t1 t2  in
                  ((let uu____1261 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "1346")
                       in
                    if uu____1261
                    then
                      let uu____1262 =
                        FStar_Common.string_of_option
                          (FStar_TypeChecker_Rel.guard_to_string env) res
                         in
                      let uu____1263 = FStar_Syntax_Print.term_to_string t1
                         in
                      let uu____1264 = FStar_Syntax_Print.term_to_string t2
                         in
                      FStar_Util.print3
                        "%%%%%%%%do_unify (RESULT %s) %s =? %s\n" uu____1262
                        uu____1263 uu____1264
                    else ());
                   (match res with
                    | FStar_Pervasives_Native.None  -> ret false
                    | FStar_Pervasives_Native.Some g ->
                        let uu____1269 =
                          add_implicits g.FStar_TypeChecker_Env.implicits  in
                        bind uu____1269 (fun uu____1273  -> ret true)))) ()
         with
         | FStar_Errors.Err (uu____1280,msg) ->
             mlog
               (fun uu____1283  ->
                  FStar_Util.print1 ">> do_unify error, (%s)\n" msg)
               (fun uu____1285  -> ret false)
         | FStar_Errors.Error (uu____1286,msg,r) ->
             mlog
               (fun uu____1291  ->
                  let uu____1292 = FStar_Range.string_of_range r  in
                  FStar_Util.print2 ">> do_unify error, (%s) at (%s)\n" msg
                    uu____1292) (fun uu____1294  -> ret false))
  
let (compress_implicits : unit tac) =
  bind get
    (fun ps  ->
       let imps = ps.FStar_Tactics_Types.all_implicits  in
       let g =
         let uu___366_1305 = FStar_TypeChecker_Env.trivial_guard  in
         {
           FStar_TypeChecker_Env.guard_f =
             (uu___366_1305.FStar_TypeChecker_Env.guard_f);
           FStar_TypeChecker_Env.deferred =
             (uu___366_1305.FStar_TypeChecker_Env.deferred);
           FStar_TypeChecker_Env.univ_ineqs =
             (uu___366_1305.FStar_TypeChecker_Env.univ_ineqs);
           FStar_TypeChecker_Env.implicits = imps
         }  in
       let g1 =
         FStar_TypeChecker_Rel.resolve_implicits_tac
           ps.FStar_Tactics_Types.main_context g
          in
       let ps' =
         let uu___367_1308 = ps  in
         {
           FStar_Tactics_Types.main_context =
             (uu___367_1308.FStar_Tactics_Types.main_context);
           FStar_Tactics_Types.main_goal =
             (uu___367_1308.FStar_Tactics_Types.main_goal);
           FStar_Tactics_Types.all_implicits =
             (g1.FStar_TypeChecker_Env.implicits);
           FStar_Tactics_Types.goals =
             (uu___367_1308.FStar_Tactics_Types.goals);
           FStar_Tactics_Types.smt_goals =
             (uu___367_1308.FStar_Tactics_Types.smt_goals);
           FStar_Tactics_Types.depth =
             (uu___367_1308.FStar_Tactics_Types.depth);
           FStar_Tactics_Types.__dump =
             (uu___367_1308.FStar_Tactics_Types.__dump);
           FStar_Tactics_Types.psc = (uu___367_1308.FStar_Tactics_Types.psc);
           FStar_Tactics_Types.entry_range =
             (uu___367_1308.FStar_Tactics_Types.entry_range);
           FStar_Tactics_Types.guard_policy =
             (uu___367_1308.FStar_Tactics_Types.guard_policy);
           FStar_Tactics_Types.freshness =
             (uu___367_1308.FStar_Tactics_Types.freshness);
           FStar_Tactics_Types.tac_verb_dbg =
             (uu___367_1308.FStar_Tactics_Types.tac_verb_dbg);
           FStar_Tactics_Types.local_state =
             (uu___367_1308.FStar_Tactics_Types.local_state)
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
          (fun uu____1331  ->
             (let uu____1333 =
                FStar_TypeChecker_Env.debug env (FStar_Options.Other "1346")
                 in
              if uu____1333
              then
                (FStar_Options.push ();
                 (let uu____1335 =
                    FStar_Options.set_options FStar_Options.Set
                      "--debug_level Rel --debug_level RelCheck"
                     in
                  ()))
              else ());
             (let uu____1337 = __do_unify env t1 t2  in
              bind uu____1337
                (fun r  ->
                   (let uu____1344 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "1346")
                       in
                    if uu____1344 then FStar_Options.pop () else ());
                   bind compress_implicits (fun uu____1347  -> ret r))))
  
let (remove_solved_goals : unit tac) =
  bind get
    (fun ps  ->
       let ps' =
         let uu___368_1354 = ps  in
         let uu____1355 =
           FStar_List.filter
             (fun g  ->
                let uu____1361 = check_goal_solved g  in
                FStar_Option.isNone uu____1361) ps.FStar_Tactics_Types.goals
            in
         {
           FStar_Tactics_Types.main_context =
             (uu___368_1354.FStar_Tactics_Types.main_context);
           FStar_Tactics_Types.main_goal =
             (uu___368_1354.FStar_Tactics_Types.main_goal);
           FStar_Tactics_Types.all_implicits =
             (uu___368_1354.FStar_Tactics_Types.all_implicits);
           FStar_Tactics_Types.goals = uu____1355;
           FStar_Tactics_Types.smt_goals =
             (uu___368_1354.FStar_Tactics_Types.smt_goals);
           FStar_Tactics_Types.depth =
             (uu___368_1354.FStar_Tactics_Types.depth);
           FStar_Tactics_Types.__dump =
             (uu___368_1354.FStar_Tactics_Types.__dump);
           FStar_Tactics_Types.psc = (uu___368_1354.FStar_Tactics_Types.psc);
           FStar_Tactics_Types.entry_range =
             (uu___368_1354.FStar_Tactics_Types.entry_range);
           FStar_Tactics_Types.guard_policy =
             (uu___368_1354.FStar_Tactics_Types.guard_policy);
           FStar_Tactics_Types.freshness =
             (uu___368_1354.FStar_Tactics_Types.freshness);
           FStar_Tactics_Types.tac_verb_dbg =
             (uu___368_1354.FStar_Tactics_Types.tac_verb_dbg);
           FStar_Tactics_Types.local_state =
             (uu___368_1354.FStar_Tactics_Types.local_state)
         }  in
       set ps')
  
let (set_solution :
  FStar_Tactics_Types.goal -> FStar_Syntax_Syntax.term -> unit tac) =
  fun goal  ->
    fun solution  ->
      let uu____1378 =
        FStar_Syntax_Unionfind.find
          (goal.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_head
         in
      match uu____1378 with
      | FStar_Pervasives_Native.Some uu____1383 ->
          let uu____1384 =
            let uu____1385 = goal_to_string_verbose goal  in
            FStar_Util.format1 "Goal %s is already solved" uu____1385  in
          fail uu____1384
      | FStar_Pervasives_Native.None  ->
          (FStar_Syntax_Unionfind.change
             (goal.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_head
             solution;
           ret ())
  
let (trysolve :
  FStar_Tactics_Types.goal -> FStar_Syntax_Syntax.term -> Prims.bool tac) =
  fun goal  ->
    fun solution  ->
      let uu____1401 = FStar_Tactics_Types.goal_env goal  in
      let uu____1402 = FStar_Tactics_Types.goal_witness goal  in
      do_unify uu____1401 solution uu____1402
  
let (__dismiss : unit tac) =
  bind get
    (fun p  ->
       let uu____1408 =
         let uu___369_1409 = p  in
         let uu____1410 = FStar_List.tl p.FStar_Tactics_Types.goals  in
         {
           FStar_Tactics_Types.main_context =
             (uu___369_1409.FStar_Tactics_Types.main_context);
           FStar_Tactics_Types.main_goal =
             (uu___369_1409.FStar_Tactics_Types.main_goal);
           FStar_Tactics_Types.all_implicits =
             (uu___369_1409.FStar_Tactics_Types.all_implicits);
           FStar_Tactics_Types.goals = uu____1410;
           FStar_Tactics_Types.smt_goals =
             (uu___369_1409.FStar_Tactics_Types.smt_goals);
           FStar_Tactics_Types.depth =
             (uu___369_1409.FStar_Tactics_Types.depth);
           FStar_Tactics_Types.__dump =
             (uu___369_1409.FStar_Tactics_Types.__dump);
           FStar_Tactics_Types.psc = (uu___369_1409.FStar_Tactics_Types.psc);
           FStar_Tactics_Types.entry_range =
             (uu___369_1409.FStar_Tactics_Types.entry_range);
           FStar_Tactics_Types.guard_policy =
             (uu___369_1409.FStar_Tactics_Types.guard_policy);
           FStar_Tactics_Types.freshness =
             (uu___369_1409.FStar_Tactics_Types.freshness);
           FStar_Tactics_Types.tac_verb_dbg =
             (uu___369_1409.FStar_Tactics_Types.tac_verb_dbg);
           FStar_Tactics_Types.local_state =
             (uu___369_1409.FStar_Tactics_Types.local_state)
         }  in
       set uu____1408)
  
let (solve :
  FStar_Tactics_Types.goal -> FStar_Syntax_Syntax.term -> unit tac) =
  fun goal  ->
    fun solution  ->
      let e = FStar_Tactics_Types.goal_env goal  in
      mlog
        (fun uu____1431  ->
           let uu____1432 =
             let uu____1433 = FStar_Tactics_Types.goal_witness goal  in
             FStar_Syntax_Print.term_to_string uu____1433  in
           let uu____1434 = FStar_Syntax_Print.term_to_string solution  in
           FStar_Util.print2 "solve %s := %s\n" uu____1432 uu____1434)
        (fun uu____1437  ->
           let uu____1438 = trysolve goal solution  in
           bind uu____1438
             (fun b  ->
                if b
                then bind __dismiss (fun uu____1446  -> remove_solved_goals)
                else
                  (let uu____1448 =
                     let uu____1449 =
                       let uu____1450 = FStar_Tactics_Types.goal_env goal  in
                       tts uu____1450 solution  in
                     let uu____1451 =
                       let uu____1452 = FStar_Tactics_Types.goal_env goal  in
                       let uu____1453 = FStar_Tactics_Types.goal_witness goal
                          in
                       tts uu____1452 uu____1453  in
                     let uu____1454 =
                       let uu____1455 = FStar_Tactics_Types.goal_env goal  in
                       let uu____1456 = FStar_Tactics_Types.goal_type goal
                          in
                       tts uu____1455 uu____1456  in
                     FStar_Util.format3 "%s does not solve %s : %s"
                       uu____1449 uu____1451 uu____1454
                      in
                   fail uu____1448)))
  
let (solve' :
  FStar_Tactics_Types.goal -> FStar_Syntax_Syntax.term -> unit tac) =
  fun goal  ->
    fun solution  ->
      let uu____1471 = set_solution goal solution  in
      bind uu____1471
        (fun uu____1475  ->
           bind __dismiss (fun uu____1477  -> remove_solved_goals))
  
let (set_goals : FStar_Tactics_Types.goal Prims.list -> unit tac) =
  fun gs  ->
    bind get
      (fun ps  ->
         set
           (let uu___370_1495 = ps  in
            {
              FStar_Tactics_Types.main_context =
                (uu___370_1495.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___370_1495.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___370_1495.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals = gs;
              FStar_Tactics_Types.smt_goals =
                (uu___370_1495.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___370_1495.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___370_1495.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___370_1495.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___370_1495.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___370_1495.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___370_1495.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___370_1495.FStar_Tactics_Types.tac_verb_dbg);
              FStar_Tactics_Types.local_state =
                (uu___370_1495.FStar_Tactics_Types.local_state)
            }))
  
let (set_smt_goals : FStar_Tactics_Types.goal Prims.list -> unit tac) =
  fun gs  ->
    bind get
      (fun ps  ->
         set
           (let uu___371_1513 = ps  in
            {
              FStar_Tactics_Types.main_context =
                (uu___371_1513.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___371_1513.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___371_1513.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___371_1513.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals = gs;
              FStar_Tactics_Types.depth =
                (uu___371_1513.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___371_1513.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___371_1513.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___371_1513.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___371_1513.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___371_1513.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___371_1513.FStar_Tactics_Types.tac_verb_dbg);
              FStar_Tactics_Types.local_state =
                (uu___371_1513.FStar_Tactics_Types.local_state)
            }))
  
let (dismiss_all : unit tac) = set_goals [] 
let (nwarn : Prims.int FStar_ST.ref) =
  FStar_Util.mk_ref (Prims.parse_int "0") 
let (check_valid_goal : FStar_Tactics_Types.goal -> unit) =
  fun g  ->
    let uu____1534 = FStar_Options.defensive ()  in
    if uu____1534
    then
      let b = true  in
      let env = FStar_Tactics_Types.goal_env g  in
      let b1 =
        b &&
          (let uu____1539 = FStar_Tactics_Types.goal_witness g  in
           FStar_TypeChecker_Env.closed env uu____1539)
         in
      let b2 =
        b1 &&
          (let uu____1542 = FStar_Tactics_Types.goal_type g  in
           FStar_TypeChecker_Env.closed env uu____1542)
         in
      let rec aux b3 e =
        let uu____1554 = FStar_TypeChecker_Env.pop_bv e  in
        match uu____1554 with
        | FStar_Pervasives_Native.None  -> b3
        | FStar_Pervasives_Native.Some (bv,e1) ->
            let b4 =
              b3 &&
                (FStar_TypeChecker_Env.closed e1 bv.FStar_Syntax_Syntax.sort)
               in
            aux b4 e1
         in
      let uu____1572 =
        (let uu____1575 = aux b2 env  in Prims.op_Negation uu____1575) &&
          (let uu____1577 = FStar_ST.op_Bang nwarn  in
           uu____1577 < (Prims.parse_int "5"))
         in
      (if uu____1572
       then
         ((let uu____1598 =
             let uu____1599 = FStar_Tactics_Types.goal_type g  in
             uu____1599.FStar_Syntax_Syntax.pos  in
           let uu____1602 =
             let uu____1607 =
               let uu____1608 = goal_to_string_verbose g  in
               FStar_Util.format1
                 "The following goal is ill-formed. Keeping calm and carrying on...\n<%s>\n\n"
                 uu____1608
                in
             (FStar_Errors.Warning_IllFormedGoal, uu____1607)  in
           FStar_Errors.log_issue uu____1598 uu____1602);
          (let uu____1609 =
             let uu____1610 = FStar_ST.op_Bang nwarn  in
             uu____1610 + (Prims.parse_int "1")  in
           FStar_ST.op_Colon_Equals nwarn uu____1609))
       else ())
    else ()
  
let (add_goals : FStar_Tactics_Types.goal Prims.list -> unit tac) =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___372_1670 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___372_1670.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___372_1670.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___372_1670.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (FStar_List.append gs p.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (uu___372_1670.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___372_1670.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___372_1670.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___372_1670.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___372_1670.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___372_1670.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___372_1670.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___372_1670.FStar_Tactics_Types.tac_verb_dbg);
              FStar_Tactics_Types.local_state =
                (uu___372_1670.FStar_Tactics_Types.local_state)
            }))
  
let (add_smt_goals : FStar_Tactics_Types.goal Prims.list -> unit tac) =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___373_1690 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___373_1690.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___373_1690.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___373_1690.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___373_1690.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (FStar_List.append gs p.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___373_1690.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___373_1690.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___373_1690.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___373_1690.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___373_1690.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___373_1690.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___373_1690.FStar_Tactics_Types.tac_verb_dbg);
              FStar_Tactics_Types.local_state =
                (uu___373_1690.FStar_Tactics_Types.local_state)
            }))
  
let (push_goals : FStar_Tactics_Types.goal Prims.list -> unit tac) =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___374_1710 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___374_1710.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___374_1710.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___374_1710.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (FStar_List.append p.FStar_Tactics_Types.goals gs);
              FStar_Tactics_Types.smt_goals =
                (uu___374_1710.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___374_1710.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___374_1710.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___374_1710.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___374_1710.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___374_1710.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___374_1710.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___374_1710.FStar_Tactics_Types.tac_verb_dbg);
              FStar_Tactics_Types.local_state =
                (uu___374_1710.FStar_Tactics_Types.local_state)
            }))
  
let (push_smt_goals : FStar_Tactics_Types.goal Prims.list -> unit tac) =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___375_1730 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___375_1730.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___375_1730.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___375_1730.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___375_1730.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (FStar_List.append p.FStar_Tactics_Types.smt_goals gs);
              FStar_Tactics_Types.depth =
                (uu___375_1730.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___375_1730.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___375_1730.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___375_1730.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___375_1730.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___375_1730.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___375_1730.FStar_Tactics_Types.tac_verb_dbg);
              FStar_Tactics_Types.local_state =
                (uu___375_1730.FStar_Tactics_Types.local_state)
            }))
  
let (replace_cur : FStar_Tactics_Types.goal -> unit tac) =
  fun g  -> bind __dismiss (fun uu____1741  -> add_goals [g]) 
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
        let uu____1769 =
          FStar_TypeChecker_Env.new_implicit_var_aux reason
            typ.FStar_Syntax_Syntax.pos env typ
            FStar_Syntax_Syntax.Allow_untyped
           in
        match uu____1769 with
        | (u,ctx_uvar,g_u) ->
            let uu____1803 =
              add_implicits g_u.FStar_TypeChecker_Env.implicits  in
            bind uu____1803
              (fun uu____1812  ->
                 let uu____1813 =
                   let uu____1818 =
                     let uu____1819 = FStar_List.hd ctx_uvar  in
                     FStar_Pervasives_Native.fst uu____1819  in
                   (u, uu____1818)  in
                 ret uu____1813)
  
let (is_true : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____1837 = FStar_Syntax_Util.un_squash t  in
    match uu____1837 with
    | FStar_Pervasives_Native.Some t' ->
        let uu____1847 =
          let uu____1848 = FStar_Syntax_Subst.compress t'  in
          uu____1848.FStar_Syntax_Syntax.n  in
        (match uu____1847 with
         | FStar_Syntax_Syntax.Tm_fvar fv ->
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.true_lid
         | uu____1852 -> false)
    | uu____1853 -> false
  
let (is_false : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____1863 = FStar_Syntax_Util.un_squash t  in
    match uu____1863 with
    | FStar_Pervasives_Native.Some t' ->
        let uu____1873 =
          let uu____1874 = FStar_Syntax_Subst.compress t'  in
          uu____1874.FStar_Syntax_Syntax.n  in
        (match uu____1873 with
         | FStar_Syntax_Syntax.Tm_fvar fv ->
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.false_lid
         | uu____1878 -> false)
    | uu____1879 -> false
  
let (cur_goal : unit -> FStar_Tactics_Types.goal tac) =
  fun uu____1890  ->
    bind get
      (fun p  ->
         match p.FStar_Tactics_Types.goals with
         | [] -> fail "No more goals (1)"
         | hd1::tl1 ->
             let uu____1901 =
               FStar_Syntax_Unionfind.find
                 (hd1.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_head
                in
             (match uu____1901 with
              | FStar_Pervasives_Native.None  -> ret hd1
              | FStar_Pervasives_Native.Some t ->
                  ((let uu____1908 = goal_to_string_verbose hd1  in
                    let uu____1909 = FStar_Syntax_Print.term_to_string t  in
                    FStar_Util.print2
                      "!!!!!!!!!!!! GOAL IS ALREADY SOLVED! %s\nsol is %s\n"
                      uu____1908 uu____1909);
                   ret hd1)))
  
let (tadmit_t : FStar_Syntax_Syntax.term -> unit tac) =
  fun t  ->
    let uu____1919 =
      bind get
        (fun ps  ->
           let uu____1925 = cur_goal ()  in
           bind uu____1925
             (fun g  ->
                (let uu____1932 =
                   let uu____1933 = FStar_Tactics_Types.goal_type g  in
                   uu____1933.FStar_Syntax_Syntax.pos  in
                 let uu____1936 =
                   let uu____1941 =
                     let uu____1942 = goal_to_string ps g  in
                     FStar_Util.format1 "Tactics admitted goal <%s>\n\n"
                       uu____1942
                      in
                   (FStar_Errors.Warning_TacAdmit, uu____1941)  in
                 FStar_Errors.log_issue uu____1932 uu____1936);
                solve' g t))
       in
    FStar_All.pipe_left (wrap_err "tadmit_t") uu____1919
  
let (fresh : unit -> FStar_BigInt.t tac) =
  fun uu____1953  ->
    bind get
      (fun ps  ->
         let n1 = ps.FStar_Tactics_Types.freshness  in
         let ps1 =
           let uu___376_1963 = ps  in
           {
             FStar_Tactics_Types.main_context =
               (uu___376_1963.FStar_Tactics_Types.main_context);
             FStar_Tactics_Types.main_goal =
               (uu___376_1963.FStar_Tactics_Types.main_goal);
             FStar_Tactics_Types.all_implicits =
               (uu___376_1963.FStar_Tactics_Types.all_implicits);
             FStar_Tactics_Types.goals =
               (uu___376_1963.FStar_Tactics_Types.goals);
             FStar_Tactics_Types.smt_goals =
               (uu___376_1963.FStar_Tactics_Types.smt_goals);
             FStar_Tactics_Types.depth =
               (uu___376_1963.FStar_Tactics_Types.depth);
             FStar_Tactics_Types.__dump =
               (uu___376_1963.FStar_Tactics_Types.__dump);
             FStar_Tactics_Types.psc =
               (uu___376_1963.FStar_Tactics_Types.psc);
             FStar_Tactics_Types.entry_range =
               (uu___376_1963.FStar_Tactics_Types.entry_range);
             FStar_Tactics_Types.guard_policy =
               (uu___376_1963.FStar_Tactics_Types.guard_policy);
             FStar_Tactics_Types.freshness = (n1 + (Prims.parse_int "1"));
             FStar_Tactics_Types.tac_verb_dbg =
               (uu___376_1963.FStar_Tactics_Types.tac_verb_dbg);
             FStar_Tactics_Types.local_state =
               (uu___376_1963.FStar_Tactics_Types.local_state)
           }  in
         let uu____1964 = set ps1  in
         bind uu____1964
           (fun uu____1969  ->
              let uu____1970 = FStar_BigInt.of_int_fs n1  in ret uu____1970))
  
let (mk_irrelevant_goal :
  Prims.string ->
    env ->
      FStar_Reflection_Data.typ ->
        FStar_Options.optionstate ->
          Prims.string -> FStar_Tactics_Types.goal tac)
  =
  fun reason  ->
    fun env  ->
      fun phi  ->
        fun opts  ->
          fun label1  ->
            let typ =
              let uu____2003 = env.FStar_TypeChecker_Env.universe_of env phi
                 in
              FStar_Syntax_Util.mk_squash uu____2003 phi  in
            let uu____2004 = new_uvar reason env typ  in
            bind uu____2004
              (fun uu____2019  ->
                 match uu____2019 with
                 | (uu____2026,ctx_uvar) ->
                     let goal =
                       FStar_Tactics_Types.mk_goal env ctx_uvar opts false
                         label1
                        in
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
             (fun uu____2071  ->
                let uu____2072 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.print1 "Tac> __tc(%s)\n" uu____2072)
             (fun uu____2075  ->
                let e1 =
                  let uu___377_2077 = e  in
                  {
                    FStar_TypeChecker_Env.solver =
                      (uu___377_2077.FStar_TypeChecker_Env.solver);
                    FStar_TypeChecker_Env.range =
                      (uu___377_2077.FStar_TypeChecker_Env.range);
                    FStar_TypeChecker_Env.curmodule =
                      (uu___377_2077.FStar_TypeChecker_Env.curmodule);
                    FStar_TypeChecker_Env.gamma =
                      (uu___377_2077.FStar_TypeChecker_Env.gamma);
                    FStar_TypeChecker_Env.gamma_sig =
                      (uu___377_2077.FStar_TypeChecker_Env.gamma_sig);
                    FStar_TypeChecker_Env.gamma_cache =
                      (uu___377_2077.FStar_TypeChecker_Env.gamma_cache);
                    FStar_TypeChecker_Env.modules =
                      (uu___377_2077.FStar_TypeChecker_Env.modules);
                    FStar_TypeChecker_Env.expected_typ =
                      (uu___377_2077.FStar_TypeChecker_Env.expected_typ);
                    FStar_TypeChecker_Env.sigtab =
                      (uu___377_2077.FStar_TypeChecker_Env.sigtab);
                    FStar_TypeChecker_Env.attrtab =
                      (uu___377_2077.FStar_TypeChecker_Env.attrtab);
                    FStar_TypeChecker_Env.is_pattern =
                      (uu___377_2077.FStar_TypeChecker_Env.is_pattern);
                    FStar_TypeChecker_Env.instantiate_imp =
                      (uu___377_2077.FStar_TypeChecker_Env.instantiate_imp);
                    FStar_TypeChecker_Env.effects =
                      (uu___377_2077.FStar_TypeChecker_Env.effects);
                    FStar_TypeChecker_Env.generalize =
                      (uu___377_2077.FStar_TypeChecker_Env.generalize);
                    FStar_TypeChecker_Env.letrecs =
                      (uu___377_2077.FStar_TypeChecker_Env.letrecs);
                    FStar_TypeChecker_Env.top_level =
                      (uu___377_2077.FStar_TypeChecker_Env.top_level);
                    FStar_TypeChecker_Env.check_uvars =
                      (uu___377_2077.FStar_TypeChecker_Env.check_uvars);
                    FStar_TypeChecker_Env.use_eq =
                      (uu___377_2077.FStar_TypeChecker_Env.use_eq);
                    FStar_TypeChecker_Env.is_iface =
                      (uu___377_2077.FStar_TypeChecker_Env.is_iface);
                    FStar_TypeChecker_Env.admit =
                      (uu___377_2077.FStar_TypeChecker_Env.admit);
                    FStar_TypeChecker_Env.lax =
                      (uu___377_2077.FStar_TypeChecker_Env.lax);
                    FStar_TypeChecker_Env.lax_universes =
                      (uu___377_2077.FStar_TypeChecker_Env.lax_universes);
                    FStar_TypeChecker_Env.phase1 =
                      (uu___377_2077.FStar_TypeChecker_Env.phase1);
                    FStar_TypeChecker_Env.failhard =
                      (uu___377_2077.FStar_TypeChecker_Env.failhard);
                    FStar_TypeChecker_Env.nosynth =
                      (uu___377_2077.FStar_TypeChecker_Env.nosynth);
                    FStar_TypeChecker_Env.uvar_subtyping = false;
                    FStar_TypeChecker_Env.tc_term =
                      (uu___377_2077.FStar_TypeChecker_Env.tc_term);
                    FStar_TypeChecker_Env.type_of =
                      (uu___377_2077.FStar_TypeChecker_Env.type_of);
                    FStar_TypeChecker_Env.universe_of =
                      (uu___377_2077.FStar_TypeChecker_Env.universe_of);
                    FStar_TypeChecker_Env.check_type_of =
                      (uu___377_2077.FStar_TypeChecker_Env.check_type_of);
                    FStar_TypeChecker_Env.use_bv_sorts =
                      (uu___377_2077.FStar_TypeChecker_Env.use_bv_sorts);
                    FStar_TypeChecker_Env.qtbl_name_and_index =
                      (uu___377_2077.FStar_TypeChecker_Env.qtbl_name_and_index);
                    FStar_TypeChecker_Env.normalized_eff_names =
                      (uu___377_2077.FStar_TypeChecker_Env.normalized_eff_names);
                    FStar_TypeChecker_Env.fv_delta_depths =
                      (uu___377_2077.FStar_TypeChecker_Env.fv_delta_depths);
                    FStar_TypeChecker_Env.proof_ns =
                      (uu___377_2077.FStar_TypeChecker_Env.proof_ns);
                    FStar_TypeChecker_Env.synth_hook =
                      (uu___377_2077.FStar_TypeChecker_Env.synth_hook);
                    FStar_TypeChecker_Env.splice =
                      (uu___377_2077.FStar_TypeChecker_Env.splice);
                    FStar_TypeChecker_Env.postprocess =
                      (uu___377_2077.FStar_TypeChecker_Env.postprocess);
                    FStar_TypeChecker_Env.is_native_tactic =
                      (uu___377_2077.FStar_TypeChecker_Env.is_native_tactic);
                    FStar_TypeChecker_Env.identifier_info =
                      (uu___377_2077.FStar_TypeChecker_Env.identifier_info);
                    FStar_TypeChecker_Env.tc_hooks =
                      (uu___377_2077.FStar_TypeChecker_Env.tc_hooks);
                    FStar_TypeChecker_Env.dsenv =
                      (uu___377_2077.FStar_TypeChecker_Env.dsenv);
                    FStar_TypeChecker_Env.nbe =
                      (uu___377_2077.FStar_TypeChecker_Env.nbe)
                  }  in
                try
                  (fun uu___379_2088  ->
                     match () with
                     | () ->
                         let uu____2097 =
                           FStar_TypeChecker_TcTerm.type_of_tot_term e1 t  in
                         ret uu____2097) ()
                with
                | FStar_Errors.Err (uu____2124,msg) ->
                    let uu____2126 = tts e1 t  in
                    let uu____2127 =
                      let uu____2128 = FStar_TypeChecker_Env.all_binders e1
                         in
                      FStar_All.pipe_right uu____2128
                        (FStar_Syntax_Print.binders_to_string ", ")
                       in
                    fail3 "Cannot type %s in context (%s). Error = (%s)"
                      uu____2126 uu____2127 msg
                | FStar_Errors.Error (uu____2135,msg,uu____2137) ->
                    let uu____2138 = tts e1 t  in
                    let uu____2139 =
                      let uu____2140 = FStar_TypeChecker_Env.all_binders e1
                         in
                      FStar_All.pipe_right uu____2140
                        (FStar_Syntax_Print.binders_to_string ", ")
                       in
                    fail3 "Cannot type %s in context (%s). Error = (%s)"
                      uu____2138 uu____2139 msg))
  
let (__tc_ghost :
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
             (fun uu____2189  ->
                let uu____2190 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.print1 "Tac> __tc_ghost(%s)\n" uu____2190)
             (fun uu____2193  ->
                let e1 =
                  let uu___380_2195 = e  in
                  {
                    FStar_TypeChecker_Env.solver =
                      (uu___380_2195.FStar_TypeChecker_Env.solver);
                    FStar_TypeChecker_Env.range =
                      (uu___380_2195.FStar_TypeChecker_Env.range);
                    FStar_TypeChecker_Env.curmodule =
                      (uu___380_2195.FStar_TypeChecker_Env.curmodule);
                    FStar_TypeChecker_Env.gamma =
                      (uu___380_2195.FStar_TypeChecker_Env.gamma);
                    FStar_TypeChecker_Env.gamma_sig =
                      (uu___380_2195.FStar_TypeChecker_Env.gamma_sig);
                    FStar_TypeChecker_Env.gamma_cache =
                      (uu___380_2195.FStar_TypeChecker_Env.gamma_cache);
                    FStar_TypeChecker_Env.modules =
                      (uu___380_2195.FStar_TypeChecker_Env.modules);
                    FStar_TypeChecker_Env.expected_typ =
                      (uu___380_2195.FStar_TypeChecker_Env.expected_typ);
                    FStar_TypeChecker_Env.sigtab =
                      (uu___380_2195.FStar_TypeChecker_Env.sigtab);
                    FStar_TypeChecker_Env.attrtab =
                      (uu___380_2195.FStar_TypeChecker_Env.attrtab);
                    FStar_TypeChecker_Env.is_pattern =
                      (uu___380_2195.FStar_TypeChecker_Env.is_pattern);
                    FStar_TypeChecker_Env.instantiate_imp =
                      (uu___380_2195.FStar_TypeChecker_Env.instantiate_imp);
                    FStar_TypeChecker_Env.effects =
                      (uu___380_2195.FStar_TypeChecker_Env.effects);
                    FStar_TypeChecker_Env.generalize =
                      (uu___380_2195.FStar_TypeChecker_Env.generalize);
                    FStar_TypeChecker_Env.letrecs =
                      (uu___380_2195.FStar_TypeChecker_Env.letrecs);
                    FStar_TypeChecker_Env.top_level =
                      (uu___380_2195.FStar_TypeChecker_Env.top_level);
                    FStar_TypeChecker_Env.check_uvars =
                      (uu___380_2195.FStar_TypeChecker_Env.check_uvars);
                    FStar_TypeChecker_Env.use_eq =
                      (uu___380_2195.FStar_TypeChecker_Env.use_eq);
                    FStar_TypeChecker_Env.is_iface =
                      (uu___380_2195.FStar_TypeChecker_Env.is_iface);
                    FStar_TypeChecker_Env.admit =
                      (uu___380_2195.FStar_TypeChecker_Env.admit);
                    FStar_TypeChecker_Env.lax =
                      (uu___380_2195.FStar_TypeChecker_Env.lax);
                    FStar_TypeChecker_Env.lax_universes =
                      (uu___380_2195.FStar_TypeChecker_Env.lax_universes);
                    FStar_TypeChecker_Env.phase1 =
                      (uu___380_2195.FStar_TypeChecker_Env.phase1);
                    FStar_TypeChecker_Env.failhard =
                      (uu___380_2195.FStar_TypeChecker_Env.failhard);
                    FStar_TypeChecker_Env.nosynth =
                      (uu___380_2195.FStar_TypeChecker_Env.nosynth);
                    FStar_TypeChecker_Env.uvar_subtyping = false;
                    FStar_TypeChecker_Env.tc_term =
                      (uu___380_2195.FStar_TypeChecker_Env.tc_term);
                    FStar_TypeChecker_Env.type_of =
                      (uu___380_2195.FStar_TypeChecker_Env.type_of);
                    FStar_TypeChecker_Env.universe_of =
                      (uu___380_2195.FStar_TypeChecker_Env.universe_of);
                    FStar_TypeChecker_Env.check_type_of =
                      (uu___380_2195.FStar_TypeChecker_Env.check_type_of);
                    FStar_TypeChecker_Env.use_bv_sorts =
                      (uu___380_2195.FStar_TypeChecker_Env.use_bv_sorts);
                    FStar_TypeChecker_Env.qtbl_name_and_index =
                      (uu___380_2195.FStar_TypeChecker_Env.qtbl_name_and_index);
                    FStar_TypeChecker_Env.normalized_eff_names =
                      (uu___380_2195.FStar_TypeChecker_Env.normalized_eff_names);
                    FStar_TypeChecker_Env.fv_delta_depths =
                      (uu___380_2195.FStar_TypeChecker_Env.fv_delta_depths);
                    FStar_TypeChecker_Env.proof_ns =
                      (uu___380_2195.FStar_TypeChecker_Env.proof_ns);
                    FStar_TypeChecker_Env.synth_hook =
                      (uu___380_2195.FStar_TypeChecker_Env.synth_hook);
                    FStar_TypeChecker_Env.splice =
                      (uu___380_2195.FStar_TypeChecker_Env.splice);
                    FStar_TypeChecker_Env.postprocess =
                      (uu___380_2195.FStar_TypeChecker_Env.postprocess);
                    FStar_TypeChecker_Env.is_native_tactic =
                      (uu___380_2195.FStar_TypeChecker_Env.is_native_tactic);
                    FStar_TypeChecker_Env.identifier_info =
                      (uu___380_2195.FStar_TypeChecker_Env.identifier_info);
                    FStar_TypeChecker_Env.tc_hooks =
                      (uu___380_2195.FStar_TypeChecker_Env.tc_hooks);
                    FStar_TypeChecker_Env.dsenv =
                      (uu___380_2195.FStar_TypeChecker_Env.dsenv);
                    FStar_TypeChecker_Env.nbe =
                      (uu___380_2195.FStar_TypeChecker_Env.nbe)
                  }  in
                try
                  (fun uu___382_2209  ->
                     match () with
                     | () ->
                         let uu____2218 =
                           FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term e1 t
                            in
                         (match uu____2218 with
                          | (t1,lc,g) ->
                              ret (t1, (lc.FStar_Syntax_Syntax.res_typ), g)))
                    ()
                with
                | FStar_Errors.Err (uu____2256,msg) ->
                    let uu____2258 = tts e1 t  in
                    let uu____2259 =
                      let uu____2260 = FStar_TypeChecker_Env.all_binders e1
                         in
                      FStar_All.pipe_right uu____2260
                        (FStar_Syntax_Print.binders_to_string ", ")
                       in
                    fail3 "Cannot type %s in context (%s). Error = (%s)"
                      uu____2258 uu____2259 msg
                | FStar_Errors.Error (uu____2267,msg,uu____2269) ->
                    let uu____2270 = tts e1 t  in
                    let uu____2271 =
                      let uu____2272 = FStar_TypeChecker_Env.all_binders e1
                         in
                      FStar_All.pipe_right uu____2272
                        (FStar_Syntax_Print.binders_to_string ", ")
                       in
                    fail3 "Cannot type %s in context (%s). Error = (%s)"
                      uu____2270 uu____2271 msg))
  
let (__tc_lax :
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
             (fun uu____2321  ->
                let uu____2322 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.print1 "Tac> __tc(%s)\n" uu____2322)
             (fun uu____2326  ->
                let e1 =
                  let uu___383_2328 = e  in
                  {
                    FStar_TypeChecker_Env.solver =
                      (uu___383_2328.FStar_TypeChecker_Env.solver);
                    FStar_TypeChecker_Env.range =
                      (uu___383_2328.FStar_TypeChecker_Env.range);
                    FStar_TypeChecker_Env.curmodule =
                      (uu___383_2328.FStar_TypeChecker_Env.curmodule);
                    FStar_TypeChecker_Env.gamma =
                      (uu___383_2328.FStar_TypeChecker_Env.gamma);
                    FStar_TypeChecker_Env.gamma_sig =
                      (uu___383_2328.FStar_TypeChecker_Env.gamma_sig);
                    FStar_TypeChecker_Env.gamma_cache =
                      (uu___383_2328.FStar_TypeChecker_Env.gamma_cache);
                    FStar_TypeChecker_Env.modules =
                      (uu___383_2328.FStar_TypeChecker_Env.modules);
                    FStar_TypeChecker_Env.expected_typ =
                      (uu___383_2328.FStar_TypeChecker_Env.expected_typ);
                    FStar_TypeChecker_Env.sigtab =
                      (uu___383_2328.FStar_TypeChecker_Env.sigtab);
                    FStar_TypeChecker_Env.attrtab =
                      (uu___383_2328.FStar_TypeChecker_Env.attrtab);
                    FStar_TypeChecker_Env.is_pattern =
                      (uu___383_2328.FStar_TypeChecker_Env.is_pattern);
                    FStar_TypeChecker_Env.instantiate_imp =
                      (uu___383_2328.FStar_TypeChecker_Env.instantiate_imp);
                    FStar_TypeChecker_Env.effects =
                      (uu___383_2328.FStar_TypeChecker_Env.effects);
                    FStar_TypeChecker_Env.generalize =
                      (uu___383_2328.FStar_TypeChecker_Env.generalize);
                    FStar_TypeChecker_Env.letrecs =
                      (uu___383_2328.FStar_TypeChecker_Env.letrecs);
                    FStar_TypeChecker_Env.top_level =
                      (uu___383_2328.FStar_TypeChecker_Env.top_level);
                    FStar_TypeChecker_Env.check_uvars =
                      (uu___383_2328.FStar_TypeChecker_Env.check_uvars);
                    FStar_TypeChecker_Env.use_eq =
                      (uu___383_2328.FStar_TypeChecker_Env.use_eq);
                    FStar_TypeChecker_Env.is_iface =
                      (uu___383_2328.FStar_TypeChecker_Env.is_iface);
                    FStar_TypeChecker_Env.admit =
                      (uu___383_2328.FStar_TypeChecker_Env.admit);
                    FStar_TypeChecker_Env.lax =
                      (uu___383_2328.FStar_TypeChecker_Env.lax);
                    FStar_TypeChecker_Env.lax_universes =
                      (uu___383_2328.FStar_TypeChecker_Env.lax_universes);
                    FStar_TypeChecker_Env.phase1 =
                      (uu___383_2328.FStar_TypeChecker_Env.phase1);
                    FStar_TypeChecker_Env.failhard =
                      (uu___383_2328.FStar_TypeChecker_Env.failhard);
                    FStar_TypeChecker_Env.nosynth =
                      (uu___383_2328.FStar_TypeChecker_Env.nosynth);
                    FStar_TypeChecker_Env.uvar_subtyping = false;
                    FStar_TypeChecker_Env.tc_term =
                      (uu___383_2328.FStar_TypeChecker_Env.tc_term);
                    FStar_TypeChecker_Env.type_of =
                      (uu___383_2328.FStar_TypeChecker_Env.type_of);
                    FStar_TypeChecker_Env.universe_of =
                      (uu___383_2328.FStar_TypeChecker_Env.universe_of);
                    FStar_TypeChecker_Env.check_type_of =
                      (uu___383_2328.FStar_TypeChecker_Env.check_type_of);
                    FStar_TypeChecker_Env.use_bv_sorts =
                      (uu___383_2328.FStar_TypeChecker_Env.use_bv_sorts);
                    FStar_TypeChecker_Env.qtbl_name_and_index =
                      (uu___383_2328.FStar_TypeChecker_Env.qtbl_name_and_index);
                    FStar_TypeChecker_Env.normalized_eff_names =
                      (uu___383_2328.FStar_TypeChecker_Env.normalized_eff_names);
                    FStar_TypeChecker_Env.fv_delta_depths =
                      (uu___383_2328.FStar_TypeChecker_Env.fv_delta_depths);
                    FStar_TypeChecker_Env.proof_ns =
                      (uu___383_2328.FStar_TypeChecker_Env.proof_ns);
                    FStar_TypeChecker_Env.synth_hook =
                      (uu___383_2328.FStar_TypeChecker_Env.synth_hook);
                    FStar_TypeChecker_Env.splice =
                      (uu___383_2328.FStar_TypeChecker_Env.splice);
                    FStar_TypeChecker_Env.postprocess =
                      (uu___383_2328.FStar_TypeChecker_Env.postprocess);
                    FStar_TypeChecker_Env.is_native_tactic =
                      (uu___383_2328.FStar_TypeChecker_Env.is_native_tactic);
                    FStar_TypeChecker_Env.identifier_info =
                      (uu___383_2328.FStar_TypeChecker_Env.identifier_info);
                    FStar_TypeChecker_Env.tc_hooks =
                      (uu___383_2328.FStar_TypeChecker_Env.tc_hooks);
                    FStar_TypeChecker_Env.dsenv =
                      (uu___383_2328.FStar_TypeChecker_Env.dsenv);
                    FStar_TypeChecker_Env.nbe =
                      (uu___383_2328.FStar_TypeChecker_Env.nbe)
                  }  in
                let e2 =
                  let uu___384_2330 = e1  in
                  {
                    FStar_TypeChecker_Env.solver =
                      (uu___384_2330.FStar_TypeChecker_Env.solver);
                    FStar_TypeChecker_Env.range =
                      (uu___384_2330.FStar_TypeChecker_Env.range);
                    FStar_TypeChecker_Env.curmodule =
                      (uu___384_2330.FStar_TypeChecker_Env.curmodule);
                    FStar_TypeChecker_Env.gamma =
                      (uu___384_2330.FStar_TypeChecker_Env.gamma);
                    FStar_TypeChecker_Env.gamma_sig =
                      (uu___384_2330.FStar_TypeChecker_Env.gamma_sig);
                    FStar_TypeChecker_Env.gamma_cache =
                      (uu___384_2330.FStar_TypeChecker_Env.gamma_cache);
                    FStar_TypeChecker_Env.modules =
                      (uu___384_2330.FStar_TypeChecker_Env.modules);
                    FStar_TypeChecker_Env.expected_typ =
                      (uu___384_2330.FStar_TypeChecker_Env.expected_typ);
                    FStar_TypeChecker_Env.sigtab =
                      (uu___384_2330.FStar_TypeChecker_Env.sigtab);
                    FStar_TypeChecker_Env.attrtab =
                      (uu___384_2330.FStar_TypeChecker_Env.attrtab);
                    FStar_TypeChecker_Env.is_pattern =
                      (uu___384_2330.FStar_TypeChecker_Env.is_pattern);
                    FStar_TypeChecker_Env.instantiate_imp =
                      (uu___384_2330.FStar_TypeChecker_Env.instantiate_imp);
                    FStar_TypeChecker_Env.effects =
                      (uu___384_2330.FStar_TypeChecker_Env.effects);
                    FStar_TypeChecker_Env.generalize =
                      (uu___384_2330.FStar_TypeChecker_Env.generalize);
                    FStar_TypeChecker_Env.letrecs =
                      (uu___384_2330.FStar_TypeChecker_Env.letrecs);
                    FStar_TypeChecker_Env.top_level =
                      (uu___384_2330.FStar_TypeChecker_Env.top_level);
                    FStar_TypeChecker_Env.check_uvars =
                      (uu___384_2330.FStar_TypeChecker_Env.check_uvars);
                    FStar_TypeChecker_Env.use_eq =
                      (uu___384_2330.FStar_TypeChecker_Env.use_eq);
                    FStar_TypeChecker_Env.is_iface =
                      (uu___384_2330.FStar_TypeChecker_Env.is_iface);
                    FStar_TypeChecker_Env.admit =
                      (uu___384_2330.FStar_TypeChecker_Env.admit);
                    FStar_TypeChecker_Env.lax = true;
                    FStar_TypeChecker_Env.lax_universes =
                      (uu___384_2330.FStar_TypeChecker_Env.lax_universes);
                    FStar_TypeChecker_Env.phase1 =
                      (uu___384_2330.FStar_TypeChecker_Env.phase1);
                    FStar_TypeChecker_Env.failhard =
                      (uu___384_2330.FStar_TypeChecker_Env.failhard);
                    FStar_TypeChecker_Env.nosynth =
                      (uu___384_2330.FStar_TypeChecker_Env.nosynth);
                    FStar_TypeChecker_Env.uvar_subtyping =
                      (uu___384_2330.FStar_TypeChecker_Env.uvar_subtyping);
                    FStar_TypeChecker_Env.tc_term =
                      (uu___384_2330.FStar_TypeChecker_Env.tc_term);
                    FStar_TypeChecker_Env.type_of =
                      (uu___384_2330.FStar_TypeChecker_Env.type_of);
                    FStar_TypeChecker_Env.universe_of =
                      (uu___384_2330.FStar_TypeChecker_Env.universe_of);
                    FStar_TypeChecker_Env.check_type_of =
                      (uu___384_2330.FStar_TypeChecker_Env.check_type_of);
                    FStar_TypeChecker_Env.use_bv_sorts =
                      (uu___384_2330.FStar_TypeChecker_Env.use_bv_sorts);
                    FStar_TypeChecker_Env.qtbl_name_and_index =
                      (uu___384_2330.FStar_TypeChecker_Env.qtbl_name_and_index);
                    FStar_TypeChecker_Env.normalized_eff_names =
                      (uu___384_2330.FStar_TypeChecker_Env.normalized_eff_names);
                    FStar_TypeChecker_Env.fv_delta_depths =
                      (uu___384_2330.FStar_TypeChecker_Env.fv_delta_depths);
                    FStar_TypeChecker_Env.proof_ns =
                      (uu___384_2330.FStar_TypeChecker_Env.proof_ns);
                    FStar_TypeChecker_Env.synth_hook =
                      (uu___384_2330.FStar_TypeChecker_Env.synth_hook);
                    FStar_TypeChecker_Env.splice =
                      (uu___384_2330.FStar_TypeChecker_Env.splice);
                    FStar_TypeChecker_Env.postprocess =
                      (uu___384_2330.FStar_TypeChecker_Env.postprocess);
                    FStar_TypeChecker_Env.is_native_tactic =
                      (uu___384_2330.FStar_TypeChecker_Env.is_native_tactic);
                    FStar_TypeChecker_Env.identifier_info =
                      (uu___384_2330.FStar_TypeChecker_Env.identifier_info);
                    FStar_TypeChecker_Env.tc_hooks =
                      (uu___384_2330.FStar_TypeChecker_Env.tc_hooks);
                    FStar_TypeChecker_Env.dsenv =
                      (uu___384_2330.FStar_TypeChecker_Env.dsenv);
                    FStar_TypeChecker_Env.nbe =
                      (uu___384_2330.FStar_TypeChecker_Env.nbe)
                  }  in
                try
                  (fun uu___386_2344  ->
                     match () with
                     | () ->
                         let uu____2353 =
                           FStar_TypeChecker_TcTerm.tc_term e2 t  in
                         (match uu____2353 with
                          | (t1,lc,g) ->
                              ret (t1, (lc.FStar_Syntax_Syntax.res_typ), g)))
                    ()
                with
                | FStar_Errors.Err (uu____2391,msg) ->
                    let uu____2393 = tts e2 t  in
                    let uu____2394 =
                      let uu____2395 = FStar_TypeChecker_Env.all_binders e2
                         in
                      FStar_All.pipe_right uu____2395
                        (FStar_Syntax_Print.binders_to_string ", ")
                       in
                    fail3 "Cannot type %s in context (%s). Error = (%s)"
                      uu____2393 uu____2394 msg
                | FStar_Errors.Error (uu____2402,msg,uu____2404) ->
                    let uu____2405 = tts e2 t  in
                    let uu____2406 =
                      let uu____2407 = FStar_TypeChecker_Env.all_binders e2
                         in
                      FStar_All.pipe_right uu____2407
                        (FStar_Syntax_Print.binders_to_string ", ")
                       in
                    fail3 "Cannot type %s in context (%s). Error = (%s)"
                      uu____2405 uu____2406 msg))
  
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
  fun uu____2434  ->
    bind get (fun ps  -> ret ps.FStar_Tactics_Types.guard_policy)
  
let (set_guard_policy : FStar_Tactics_Types.guard_policy -> unit tac) =
  fun pol  ->
    bind get
      (fun ps  ->
         set
           (let uu___387_2452 = ps  in
            {
              FStar_Tactics_Types.main_context =
                (uu___387_2452.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___387_2452.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___387_2452.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___387_2452.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (uu___387_2452.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___387_2452.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___387_2452.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___387_2452.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___387_2452.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy = pol;
              FStar_Tactics_Types.freshness =
                (uu___387_2452.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___387_2452.FStar_Tactics_Types.tac_verb_dbg);
              FStar_Tactics_Types.local_state =
                (uu___387_2452.FStar_Tactics_Types.local_state)
            }))
  
let with_policy : 'a . FStar_Tactics_Types.guard_policy -> 'a tac -> 'a tac =
  fun pol  ->
    fun t  ->
      let uu____2476 = get_guard_policy ()  in
      bind uu____2476
        (fun old_pol  ->
           let uu____2482 = set_guard_policy pol  in
           bind uu____2482
             (fun uu____2486  ->
                bind t
                  (fun r  ->
                     let uu____2490 = set_guard_policy old_pol  in
                     bind uu____2490 (fun uu____2494  -> ret r))))
  
let (getopts : FStar_Options.optionstate tac) =
  let uu____2497 = let uu____2502 = cur_goal ()  in trytac uu____2502  in
  bind uu____2497
    (fun uu___350_2509  ->
       match uu___350_2509 with
       | FStar_Pervasives_Native.Some g -> ret g.FStar_Tactics_Types.opts
       | FStar_Pervasives_Native.None  ->
           let uu____2515 = FStar_Options.peek ()  in ret uu____2515)
  
let (proc_guard :
  Prims.string -> env -> FStar_TypeChecker_Env.guard_t -> unit tac) =
  fun reason  ->
    fun e  ->
      fun g  ->
        mlog
          (fun uu____2537  ->
             let uu____2538 = FStar_TypeChecker_Rel.guard_to_string e g  in
             FStar_Util.print2 "Processing guard (%s:%s)\n" reason uu____2538)
          (fun uu____2541  ->
             let uu____2542 = add_implicits g.FStar_TypeChecker_Env.implicits
                in
             bind uu____2542
               (fun uu____2546  ->
                  bind getopts
                    (fun opts  ->
                       let uu____2550 =
                         let uu____2551 =
                           FStar_TypeChecker_Rel.simplify_guard e g  in
                         uu____2551.FStar_TypeChecker_Env.guard_f  in
                       match uu____2550 with
                       | FStar_TypeChecker_Common.Trivial  -> ret ()
                       | FStar_TypeChecker_Common.NonTrivial f ->
                           let uu____2555 = istrivial e f  in
                           if uu____2555
                           then ret ()
                           else
                             bind get
                               (fun ps  ->
                                  match ps.FStar_Tactics_Types.guard_policy
                                  with
                                  | FStar_Tactics_Types.Drop  ->
                                      ((let uu____2565 =
                                          let uu____2570 =
                                            let uu____2571 =
                                              FStar_TypeChecker_Rel.guard_to_string
                                                e g
                                               in
                                            FStar_Util.format1
                                              "Tactics admitted guard <%s>\n\n"
                                              uu____2571
                                             in
                                          (FStar_Errors.Warning_TacAdmit,
                                            uu____2570)
                                           in
                                        FStar_Errors.log_issue
                                          e.FStar_TypeChecker_Env.range
                                          uu____2565);
                                       ret ())
                                  | FStar_Tactics_Types.Goal  ->
                                      mlog
                                        (fun uu____2574  ->
                                           let uu____2575 =
                                             FStar_TypeChecker_Rel.guard_to_string
                                               e g
                                              in
                                           FStar_Util.print2
                                             "Making guard (%s:%s) into a goal\n"
                                             reason uu____2575)
                                        (fun uu____2578  ->
                                           let uu____2579 =
                                             mk_irrelevant_goal reason e f
                                               opts ""
                                              in
                                           bind uu____2579
                                             (fun goal  ->
                                                let goal1 =
                                                  let uu___388_2586 = goal
                                                     in
                                                  {
                                                    FStar_Tactics_Types.goal_main_env
                                                      =
                                                      (uu___388_2586.FStar_Tactics_Types.goal_main_env);
                                                    FStar_Tactics_Types.goal_ctx_uvar
                                                      =
                                                      (uu___388_2586.FStar_Tactics_Types.goal_ctx_uvar);
                                                    FStar_Tactics_Types.opts
                                                      =
                                                      (uu___388_2586.FStar_Tactics_Types.opts);
                                                    FStar_Tactics_Types.is_guard
                                                      = true;
                                                    FStar_Tactics_Types.label
                                                      =
                                                      (uu___388_2586.FStar_Tactics_Types.label)
                                                  }  in
                                                push_goals [goal1]))
                                  | FStar_Tactics_Types.SMT  ->
                                      mlog
                                        (fun uu____2589  ->
                                           let uu____2590 =
                                             FStar_TypeChecker_Rel.guard_to_string
                                               e g
                                              in
                                           FStar_Util.print2
                                             "Sending guard (%s:%s) to SMT goal\n"
                                             reason uu____2590)
                                        (fun uu____2593  ->
                                           let uu____2594 =
                                             mk_irrelevant_goal reason e f
                                               opts ""
                                              in
                                           bind uu____2594
                                             (fun goal  ->
                                                let goal1 =
                                                  let uu___389_2601 = goal
                                                     in
                                                  {
                                                    FStar_Tactics_Types.goal_main_env
                                                      =
                                                      (uu___389_2601.FStar_Tactics_Types.goal_main_env);
                                                    FStar_Tactics_Types.goal_ctx_uvar
                                                      =
                                                      (uu___389_2601.FStar_Tactics_Types.goal_ctx_uvar);
                                                    FStar_Tactics_Types.opts
                                                      =
                                                      (uu___389_2601.FStar_Tactics_Types.opts);
                                                    FStar_Tactics_Types.is_guard
                                                      = true;
                                                    FStar_Tactics_Types.label
                                                      =
                                                      (uu___389_2601.FStar_Tactics_Types.label)
                                                  }  in
                                                push_smt_goals [goal1]))
                                  | FStar_Tactics_Types.Force  ->
                                      mlog
                                        (fun uu____2604  ->
                                           let uu____2605 =
                                             FStar_TypeChecker_Rel.guard_to_string
                                               e g
                                              in
                                           FStar_Util.print2
                                             "Forcing guard (%s:%s)\n" reason
                                             uu____2605)
                                        (fun uu____2607  ->
                                           try
                                             (fun uu___391_2612  ->
                                                match () with
                                                | () ->
                                                    let uu____2615 =
                                                      let uu____2616 =
                                                        let uu____2617 =
                                                          FStar_TypeChecker_Rel.discharge_guard_no_smt
                                                            e g
                                                           in
                                                        FStar_All.pipe_left
                                                          FStar_TypeChecker_Env.is_trivial
                                                          uu____2617
                                                         in
                                                      Prims.op_Negation
                                                        uu____2616
                                                       in
                                                    if uu____2615
                                                    then
                                                      mlog
                                                        (fun uu____2622  ->
                                                           let uu____2623 =
                                                             FStar_TypeChecker_Rel.guard_to_string
                                                               e g
                                                              in
                                                           FStar_Util.print1
                                                             "guard = %s\n"
                                                             uu____2623)
                                                        (fun uu____2625  ->
                                                           fail1
                                                             "Forcing the guard failed (%s)"
                                                             reason)
                                                    else ret ()) ()
                                           with
                                           | uu___390_2628 ->
                                               mlog
                                                 (fun uu____2633  ->
                                                    let uu____2634 =
                                                      FStar_TypeChecker_Rel.guard_to_string
                                                        e g
                                                       in
                                                    FStar_Util.print1
                                                      "guard = %s\n"
                                                      uu____2634)
                                                 (fun uu____2636  ->
                                                    fail1
                                                      "Forcing the guard failed (%s)"
                                                      reason))))))
  
let (tc : FStar_Syntax_Syntax.term -> FStar_Reflection_Data.typ tac) =
  fun t  ->
    let uu____2646 =
      let uu____2649 = cur_goal ()  in
      bind uu____2649
        (fun goal  ->
           let uu____2655 =
             let uu____2664 = FStar_Tactics_Types.goal_env goal  in
             __tc_lax uu____2664 t  in
           bind uu____2655
             (fun uu____2675  ->
                match uu____2675 with
                | (uu____2684,typ,uu____2686) -> ret typ))
       in
    FStar_All.pipe_left (wrap_err "tc") uu____2646
  
let (add_irrelevant_goal :
  Prims.string ->
    env ->
      FStar_Reflection_Data.typ ->
        FStar_Options.optionstate -> Prims.string -> unit tac)
  =
  fun reason  ->
    fun env  ->
      fun phi  ->
        fun opts  ->
          fun label1  ->
            let uu____2720 = mk_irrelevant_goal reason env phi opts label1
               in
            bind uu____2720 (fun goal  -> add_goals [goal])
  
let (trivial : unit -> unit tac) =
  fun uu____2731  ->
    let uu____2734 = cur_goal ()  in
    bind uu____2734
      (fun goal  ->
         let uu____2740 =
           let uu____2741 = FStar_Tactics_Types.goal_env goal  in
           let uu____2742 = FStar_Tactics_Types.goal_type goal  in
           istrivial uu____2741 uu____2742  in
         if uu____2740
         then solve' goal FStar_Syntax_Util.exp_unit
         else
           (let uu____2746 =
              let uu____2747 = FStar_Tactics_Types.goal_env goal  in
              let uu____2748 = FStar_Tactics_Types.goal_type goal  in
              tts uu____2747 uu____2748  in
            fail1 "Not a trivial goal: %s" uu____2746))
  
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
             let uu____2797 =
               try
                 (fun uu___396_2820  ->
                    match () with
                    | () ->
                        let uu____2831 =
                          let uu____2840 = FStar_BigInt.to_int_fs n1  in
                          FStar_List.splitAt uu____2840
                            p.FStar_Tactics_Types.goals
                           in
                        ret uu____2831) ()
               with | uu___395_2850 -> fail "divide: not enough goals"  in
             bind uu____2797
               (fun uu____2886  ->
                  match uu____2886 with
                  | (lgs,rgs) ->
                      let lp =
                        let uu___392_2912 = p  in
                        {
                          FStar_Tactics_Types.main_context =
                            (uu___392_2912.FStar_Tactics_Types.main_context);
                          FStar_Tactics_Types.main_goal =
                            (uu___392_2912.FStar_Tactics_Types.main_goal);
                          FStar_Tactics_Types.all_implicits =
                            (uu___392_2912.FStar_Tactics_Types.all_implicits);
                          FStar_Tactics_Types.goals = lgs;
                          FStar_Tactics_Types.smt_goals = [];
                          FStar_Tactics_Types.depth =
                            (uu___392_2912.FStar_Tactics_Types.depth);
                          FStar_Tactics_Types.__dump =
                            (uu___392_2912.FStar_Tactics_Types.__dump);
                          FStar_Tactics_Types.psc =
                            (uu___392_2912.FStar_Tactics_Types.psc);
                          FStar_Tactics_Types.entry_range =
                            (uu___392_2912.FStar_Tactics_Types.entry_range);
                          FStar_Tactics_Types.guard_policy =
                            (uu___392_2912.FStar_Tactics_Types.guard_policy);
                          FStar_Tactics_Types.freshness =
                            (uu___392_2912.FStar_Tactics_Types.freshness);
                          FStar_Tactics_Types.tac_verb_dbg =
                            (uu___392_2912.FStar_Tactics_Types.tac_verb_dbg);
                          FStar_Tactics_Types.local_state =
                            (uu___392_2912.FStar_Tactics_Types.local_state)
                        }  in
                      let uu____2913 = set lp  in
                      bind uu____2913
                        (fun uu____2921  ->
                           bind l
                             (fun a  ->
                                bind get
                                  (fun lp'  ->
                                     let rp =
                                       let uu___393_2937 = lp'  in
                                       {
                                         FStar_Tactics_Types.main_context =
                                           (uu___393_2937.FStar_Tactics_Types.main_context);
                                         FStar_Tactics_Types.main_goal =
                                           (uu___393_2937.FStar_Tactics_Types.main_goal);
                                         FStar_Tactics_Types.all_implicits =
                                           (uu___393_2937.FStar_Tactics_Types.all_implicits);
                                         FStar_Tactics_Types.goals = rgs;
                                         FStar_Tactics_Types.smt_goals = [];
                                         FStar_Tactics_Types.depth =
                                           (uu___393_2937.FStar_Tactics_Types.depth);
                                         FStar_Tactics_Types.__dump =
                                           (uu___393_2937.FStar_Tactics_Types.__dump);
                                         FStar_Tactics_Types.psc =
                                           (uu___393_2937.FStar_Tactics_Types.psc);
                                         FStar_Tactics_Types.entry_range =
                                           (uu___393_2937.FStar_Tactics_Types.entry_range);
                                         FStar_Tactics_Types.guard_policy =
                                           (uu___393_2937.FStar_Tactics_Types.guard_policy);
                                         FStar_Tactics_Types.freshness =
                                           (uu___393_2937.FStar_Tactics_Types.freshness);
                                         FStar_Tactics_Types.tac_verb_dbg =
                                           (uu___393_2937.FStar_Tactics_Types.tac_verb_dbg);
                                         FStar_Tactics_Types.local_state =
                                           (uu___393_2937.FStar_Tactics_Types.local_state)
                                       }  in
                                     let uu____2938 = set rp  in
                                     bind uu____2938
                                       (fun uu____2946  ->
                                          bind r
                                            (fun b  ->
                                               bind get
                                                 (fun rp'  ->
                                                    let p' =
                                                      let uu___394_2962 = rp'
                                                         in
                                                      {
                                                        FStar_Tactics_Types.main_context
                                                          =
                                                          (uu___394_2962.FStar_Tactics_Types.main_context);
                                                        FStar_Tactics_Types.main_goal
                                                          =
                                                          (uu___394_2962.FStar_Tactics_Types.main_goal);
                                                        FStar_Tactics_Types.all_implicits
                                                          =
                                                          (uu___394_2962.FStar_Tactics_Types.all_implicits);
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
                                                          (uu___394_2962.FStar_Tactics_Types.depth);
                                                        FStar_Tactics_Types.__dump
                                                          =
                                                          (uu___394_2962.FStar_Tactics_Types.__dump);
                                                        FStar_Tactics_Types.psc
                                                          =
                                                          (uu___394_2962.FStar_Tactics_Types.psc);
                                                        FStar_Tactics_Types.entry_range
                                                          =
                                                          (uu___394_2962.FStar_Tactics_Types.entry_range);
                                                        FStar_Tactics_Types.guard_policy
                                                          =
                                                          (uu___394_2962.FStar_Tactics_Types.guard_policy);
                                                        FStar_Tactics_Types.freshness
                                                          =
                                                          (uu___394_2962.FStar_Tactics_Types.freshness);
                                                        FStar_Tactics_Types.tac_verb_dbg
                                                          =
                                                          (uu___394_2962.FStar_Tactics_Types.tac_verb_dbg);
                                                        FStar_Tactics_Types.local_state
                                                          =
                                                          (uu___394_2962.FStar_Tactics_Types.local_state)
                                                      }  in
                                                    let uu____2963 = set p'
                                                       in
                                                    bind uu____2963
                                                      (fun uu____2971  ->
                                                         bind
                                                           remove_solved_goals
                                                           (fun uu____2977 
                                                              -> ret (a, b)))))))))))
  
let focus : 'a . 'a tac -> 'a tac =
  fun f  ->
    let uu____2998 = divide FStar_BigInt.one f idtac  in
    bind uu____2998
      (fun uu____3011  -> match uu____3011 with | (a,()) -> ret a)
  
let rec map : 'a . 'a tac -> 'a Prims.list tac =
  fun tau  ->
    bind get
      (fun p  ->
         match p.FStar_Tactics_Types.goals with
         | [] -> ret []
         | uu____3048::uu____3049 ->
             let uu____3052 =
               let uu____3061 = map tau  in
               divide FStar_BigInt.one tau uu____3061  in
             bind uu____3052
               (fun uu____3079  ->
                  match uu____3079 with | (h,t) -> ret (h :: t)))
  
let (seq : unit tac -> unit tac -> unit tac) =
  fun t1  ->
    fun t2  ->
      let uu____3120 =
        bind t1
          (fun uu____3125  ->
             let uu____3126 = map t2  in
             bind uu____3126 (fun uu____3134  -> ret ()))
         in
      focus uu____3120
  
let (intro : unit -> FStar_Syntax_Syntax.binder tac) =
  fun uu____3143  ->
    let uu____3146 =
      let uu____3149 = cur_goal ()  in
      bind uu____3149
        (fun goal  ->
           let uu____3158 =
             let uu____3165 = FStar_Tactics_Types.goal_type goal  in
             FStar_Syntax_Util.arrow_one uu____3165  in
           match uu____3158 with
           | FStar_Pervasives_Native.Some (b,c) ->
               let uu____3174 =
                 let uu____3175 = FStar_Syntax_Util.is_total_comp c  in
                 Prims.op_Negation uu____3175  in
               if uu____3174
               then fail "Codomain is effectful"
               else
                 (let env' =
                    let uu____3180 = FStar_Tactics_Types.goal_env goal  in
                    FStar_TypeChecker_Env.push_binders uu____3180 [b]  in
                  let typ' = comp_to_typ c  in
                  let uu____3194 = new_uvar "intro" env' typ'  in
                  bind uu____3194
                    (fun uu____3210  ->
                       match uu____3210 with
                       | (body,ctx_uvar) ->
                           let sol =
                             FStar_Syntax_Util.abs [b] body
                               (FStar_Pervasives_Native.Some
                                  (FStar_Syntax_Util.residual_comp_of_comp c))
                              in
                           let uu____3234 = set_solution goal sol  in
                           bind uu____3234
                             (fun uu____3240  ->
                                let g =
                                  FStar_Tactics_Types.mk_goal env' ctx_uvar
                                    goal.FStar_Tactics_Types.opts
                                    goal.FStar_Tactics_Types.is_guard
                                    goal.FStar_Tactics_Types.label
                                   in
                                let uu____3242 =
                                  let uu____3245 = bnorm_goal g  in
                                  replace_cur uu____3245  in
                                bind uu____3242 (fun uu____3247  -> ret b))))
           | FStar_Pervasives_Native.None  ->
               let uu____3252 =
                 let uu____3253 = FStar_Tactics_Types.goal_env goal  in
                 let uu____3254 = FStar_Tactics_Types.goal_type goal  in
                 tts uu____3253 uu____3254  in
               fail1 "goal is not an arrow (%s)" uu____3252)
       in
    FStar_All.pipe_left (wrap_err "intro") uu____3146
  
let (intro_rec :
  unit ->
    (FStar_Syntax_Syntax.binder,FStar_Syntax_Syntax.binder)
      FStar_Pervasives_Native.tuple2 tac)
  =
  fun uu____3269  ->
    let uu____3276 = cur_goal ()  in
    bind uu____3276
      (fun goal  ->
         FStar_Util.print_string
           "WARNING (intro_rec): calling this is known to cause normalizer loops\n";
         FStar_Util.print_string
           "WARNING (intro_rec): proceed at your own risk...\n";
         (let uu____3293 =
            let uu____3300 = FStar_Tactics_Types.goal_type goal  in
            FStar_Syntax_Util.arrow_one uu____3300  in
          match uu____3293 with
          | FStar_Pervasives_Native.Some (b,c) ->
              let uu____3313 =
                let uu____3314 = FStar_Syntax_Util.is_total_comp c  in
                Prims.op_Negation uu____3314  in
              if uu____3313
              then fail "Codomain is effectful"
              else
                (let bv =
                   let uu____3327 = FStar_Tactics_Types.goal_type goal  in
                   FStar_Syntax_Syntax.gen_bv "__recf"
                     FStar_Pervasives_Native.None uu____3327
                    in
                 let bs =
                   let uu____3337 = FStar_Syntax_Syntax.mk_binder bv  in
                   [uu____3337; b]  in
                 let env' =
                   let uu____3363 = FStar_Tactics_Types.goal_env goal  in
                   FStar_TypeChecker_Env.push_binders uu____3363 bs  in
                 let uu____3364 =
                   let uu____3371 = comp_to_typ c  in
                   new_uvar "intro_rec" env' uu____3371  in
                 bind uu____3364
                   (fun uu____3390  ->
                      match uu____3390 with
                      | (u,ctx_uvar_u) ->
                          let lb =
                            let uu____3404 =
                              FStar_Tactics_Types.goal_type goal  in
                            let uu____3407 =
                              FStar_Syntax_Util.abs [b] u
                                FStar_Pervasives_Native.None
                               in
                            FStar_Syntax_Util.mk_letbinding
                              (FStar_Util.Inl bv) [] uu____3404
                              FStar_Parser_Const.effect_Tot_lid uu____3407 []
                              FStar_Range.dummyRange
                             in
                          let body = FStar_Syntax_Syntax.bv_to_name bv  in
                          let uu____3425 =
                            FStar_Syntax_Subst.close_let_rec [lb] body  in
                          (match uu____3425 with
                           | (lbs,body1) ->
                               let tm =
                                 let uu____3447 =
                                   let uu____3448 =
                                     FStar_Tactics_Types.goal_witness goal
                                      in
                                   uu____3448.FStar_Syntax_Syntax.pos  in
                                 FStar_Syntax_Syntax.mk
                                   (FStar_Syntax_Syntax.Tm_let
                                      ((true, lbs), body1))
                                   FStar_Pervasives_Native.None uu____3447
                                  in
                               let uu____3461 = set_solution goal tm  in
                               bind uu____3461
                                 (fun uu____3470  ->
                                    let uu____3471 =
                                      let uu____3474 =
                                        bnorm_goal
                                          (let uu___397_3477 = goal  in
                                           {
                                             FStar_Tactics_Types.goal_main_env
                                               =
                                               (uu___397_3477.FStar_Tactics_Types.goal_main_env);
                                             FStar_Tactics_Types.goal_ctx_uvar
                                               = ctx_uvar_u;
                                             FStar_Tactics_Types.opts =
                                               (uu___397_3477.FStar_Tactics_Types.opts);
                                             FStar_Tactics_Types.is_guard =
                                               (uu___397_3477.FStar_Tactics_Types.is_guard);
                                             FStar_Tactics_Types.label =
                                               (uu___397_3477.FStar_Tactics_Types.label)
                                           })
                                         in
                                      replace_cur uu____3474  in
                                    bind uu____3471
                                      (fun uu____3484  ->
                                         let uu____3485 =
                                           let uu____3490 =
                                             FStar_Syntax_Syntax.mk_binder bv
                                              in
                                           (uu____3490, b)  in
                                         ret uu____3485)))))
          | FStar_Pervasives_Native.None  ->
              let uu____3499 =
                let uu____3500 = FStar_Tactics_Types.goal_env goal  in
                let uu____3501 = FStar_Tactics_Types.goal_type goal  in
                tts uu____3500 uu____3501  in
              fail1 "intro_rec: goal is not an arrow (%s)" uu____3499))
  
let (norm : FStar_Syntax_Embeddings.norm_step Prims.list -> unit tac) =
  fun s  ->
    let uu____3519 = cur_goal ()  in
    bind uu____3519
      (fun goal  ->
         mlog
           (fun uu____3526  ->
              let uu____3527 =
                let uu____3528 = FStar_Tactics_Types.goal_witness goal  in
                FStar_Syntax_Print.term_to_string uu____3528  in
              FStar_Util.print1 "norm: witness = %s\n" uu____3527)
           (fun uu____3533  ->
              let steps =
                let uu____3537 = FStar_TypeChecker_Normalize.tr_norm_steps s
                   in
                FStar_List.append
                  [FStar_TypeChecker_Env.Reify;
                  FStar_TypeChecker_Env.UnfoldTac] uu____3537
                 in
              let t =
                let uu____3541 = FStar_Tactics_Types.goal_env goal  in
                let uu____3542 = FStar_Tactics_Types.goal_type goal  in
                normalize steps uu____3541 uu____3542  in
              let uu____3543 = FStar_Tactics_Types.goal_with_type goal t  in
              replace_cur uu____3543))
  
let (norm_term_env :
  env ->
    FStar_Syntax_Embeddings.norm_step Prims.list ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term tac)
  =
  fun e  ->
    fun s  ->
      fun t  ->
        let uu____3567 =
          bind get
            (fun ps  ->
               let opts =
                 match ps.FStar_Tactics_Types.goals with
                 | g::uu____3575 -> g.FStar_Tactics_Types.opts
                 | uu____3578 -> FStar_Options.peek ()  in
               mlog
                 (fun uu____3583  ->
                    let uu____3584 = FStar_Syntax_Print.term_to_string t  in
                    FStar_Util.print1 "norm_term_env: t = %s\n" uu____3584)
                 (fun uu____3587  ->
                    let uu____3588 = __tc_lax e t  in
                    bind uu____3588
                      (fun uu____3609  ->
                         match uu____3609 with
                         | (t1,uu____3619,uu____3620) ->
                             let steps =
                               let uu____3624 =
                                 FStar_TypeChecker_Normalize.tr_norm_steps s
                                  in
                               FStar_List.append
                                 [FStar_TypeChecker_Env.Reify;
                                 FStar_TypeChecker_Env.UnfoldTac] uu____3624
                                in
                             let t2 =
                               normalize steps
                                 ps.FStar_Tactics_Types.main_context t1
                                in
                             mlog
                               (fun uu____3630  ->
                                  let uu____3631 =
                                    FStar_Syntax_Print.term_to_string t2  in
                                  FStar_Util.print1
                                    "norm_term_env: t' = %s\n" uu____3631)
                               (fun uu____3633  -> ret t2))))
           in
        FStar_All.pipe_left (wrap_err "norm_term") uu____3567
  
let (refine_intro : unit -> unit tac) =
  fun uu____3644  ->
    let uu____3647 =
      let uu____3650 = cur_goal ()  in
      bind uu____3650
        (fun g  ->
           let uu____3657 =
             let uu____3668 = FStar_Tactics_Types.goal_env g  in
             let uu____3669 = FStar_Tactics_Types.goal_type g  in
             FStar_TypeChecker_Rel.base_and_refinement uu____3668 uu____3669
              in
           match uu____3657 with
           | (uu____3672,FStar_Pervasives_Native.None ) ->
               fail "not a refinement"
           | (t,FStar_Pervasives_Native.Some (bv,phi)) ->
               let g1 = FStar_Tactics_Types.goal_with_type g t  in
               let uu____3697 =
                 let uu____3702 =
                   let uu____3707 =
                     let uu____3708 = FStar_Syntax_Syntax.mk_binder bv  in
                     [uu____3708]  in
                   FStar_Syntax_Subst.open_term uu____3707 phi  in
                 match uu____3702 with
                 | (bvs,phi1) ->
                     let uu____3733 =
                       let uu____3734 = FStar_List.hd bvs  in
                       FStar_Pervasives_Native.fst uu____3734  in
                     (uu____3733, phi1)
                  in
               (match uu____3697 with
                | (bv1,phi1) ->
                    let uu____3753 =
                      let uu____3756 = FStar_Tactics_Types.goal_env g  in
                      let uu____3757 =
                        let uu____3758 =
                          let uu____3761 =
                            let uu____3762 =
                              let uu____3769 =
                                FStar_Tactics_Types.goal_witness g  in
                              (bv1, uu____3769)  in
                            FStar_Syntax_Syntax.NT uu____3762  in
                          [uu____3761]  in
                        FStar_Syntax_Subst.subst uu____3758 phi1  in
                      mk_irrelevant_goal "refine_intro refinement" uu____3756
                        uu____3757 g.FStar_Tactics_Types.opts
                        g.FStar_Tactics_Types.label
                       in
                    bind uu____3753
                      (fun g2  ->
                         bind __dismiss
                           (fun uu____3777  -> add_goals [g1; g2]))))
       in
    FStar_All.pipe_left (wrap_err "refine_intro") uu____3647
  
let (__exact_now : Prims.bool -> FStar_Syntax_Syntax.term -> unit tac) =
  fun set_expected_typ1  ->
    fun t  ->
      let uu____3796 = cur_goal ()  in
      bind uu____3796
        (fun goal  ->
           let env =
             if set_expected_typ1
             then
               let uu____3804 = FStar_Tactics_Types.goal_env goal  in
               let uu____3805 = FStar_Tactics_Types.goal_type goal  in
               FStar_TypeChecker_Env.set_expected_typ uu____3804 uu____3805
             else FStar_Tactics_Types.goal_env goal  in
           let uu____3807 = __tc env t  in
           bind uu____3807
             (fun uu____3826  ->
                match uu____3826 with
                | (t1,typ,guard) ->
                    mlog
                      (fun uu____3841  ->
                         let uu____3842 =
                           FStar_Syntax_Print.term_to_string typ  in
                         let uu____3843 =
                           let uu____3844 = FStar_Tactics_Types.goal_env goal
                              in
                           FStar_TypeChecker_Rel.guard_to_string uu____3844
                             guard
                            in
                         FStar_Util.print2
                           "__exact_now: got type %s\n__exact_now: and guard %s\n"
                           uu____3842 uu____3843)
                      (fun uu____3847  ->
                         let uu____3848 =
                           let uu____3851 = FStar_Tactics_Types.goal_env goal
                              in
                           proc_guard "__exact typing" uu____3851 guard  in
                         bind uu____3848
                           (fun uu____3853  ->
                              mlog
                                (fun uu____3857  ->
                                   let uu____3858 =
                                     FStar_Syntax_Print.term_to_string typ
                                      in
                                   let uu____3859 =
                                     let uu____3860 =
                                       FStar_Tactics_Types.goal_type goal  in
                                     FStar_Syntax_Print.term_to_string
                                       uu____3860
                                      in
                                   FStar_Util.print2
                                     "__exact_now: unifying %s and %s\n"
                                     uu____3858 uu____3859)
                                (fun uu____3863  ->
                                   let uu____3864 =
                                     let uu____3867 =
                                       FStar_Tactics_Types.goal_env goal  in
                                     let uu____3868 =
                                       FStar_Tactics_Types.goal_type goal  in
                                     do_unify uu____3867 typ uu____3868  in
                                   bind uu____3864
                                     (fun b  ->
                                        if b
                                        then solve goal t1
                                        else
                                          (let uu____3874 =
                                             let uu____3875 =
                                               FStar_Tactics_Types.goal_env
                                                 goal
                                                in
                                             tts uu____3875 t1  in
                                           let uu____3876 =
                                             let uu____3877 =
                                               FStar_Tactics_Types.goal_env
                                                 goal
                                                in
                                             tts uu____3877 typ  in
                                           let uu____3878 =
                                             let uu____3879 =
                                               FStar_Tactics_Types.goal_env
                                                 goal
                                                in
                                             let uu____3880 =
                                               FStar_Tactics_Types.goal_type
                                                 goal
                                                in
                                             tts uu____3879 uu____3880  in
                                           let uu____3881 =
                                             let uu____3882 =
                                               FStar_Tactics_Types.goal_env
                                                 goal
                                                in
                                             let uu____3883 =
                                               FStar_Tactics_Types.goal_witness
                                                 goal
                                                in
                                             tts uu____3882 uu____3883  in
                                           fail4
                                             "%s : %s does not exactly solve the goal %s (witness = %s)"
                                             uu____3874 uu____3876 uu____3878
                                             uu____3881)))))))
  
let (t_exact :
  Prims.bool -> Prims.bool -> FStar_Syntax_Syntax.term -> unit tac) =
  fun try_refine  ->
    fun set_expected_typ1  ->
      fun tm  ->
        let uu____3903 =
          mlog
            (fun uu____3908  ->
               let uu____3909 = FStar_Syntax_Print.term_to_string tm  in
               FStar_Util.print1 "t_exact: tm = %s\n" uu____3909)
            (fun uu____3912  ->
               let uu____3913 =
                 let uu____3920 = __exact_now set_expected_typ1 tm  in
                 catch uu____3920  in
               bind uu____3913
                 (fun uu___352_3929  ->
                    match uu___352_3929 with
                    | FStar_Util.Inr r -> ret ()
                    | FStar_Util.Inl e when Prims.op_Negation try_refine ->
                        fail e
                    | FStar_Util.Inl e ->
                        mlog
                          (fun uu____3940  ->
                             FStar_Util.print_string
                               "__exact_now failed, trying refine...\n")
                          (fun uu____3943  ->
                             let uu____3944 =
                               let uu____3951 =
                                 let uu____3954 =
                                   norm [FStar_Syntax_Embeddings.Delta]  in
                                 bind uu____3954
                                   (fun uu____3959  ->
                                      let uu____3960 = refine_intro ()  in
                                      bind uu____3960
                                        (fun uu____3964  ->
                                           __exact_now set_expected_typ1 tm))
                                  in
                               catch uu____3951  in
                             bind uu____3944
                               (fun uu___351_3971  ->
                                  match uu___351_3971 with
                                  | FStar_Util.Inr r ->
                                      mlog
                                        (fun uu____3980  ->
                                           FStar_Util.print_string
                                             "__exact_now: failed after refining too\n")
                                        (fun uu____3982  -> ret ())
                                  | FStar_Util.Inl uu____3983 ->
                                      mlog
                                        (fun uu____3985  ->
                                           FStar_Util.print_string
                                             "__exact_now: was not a refinement\n")
                                        (fun uu____3987  -> fail e)))))
           in
        FStar_All.pipe_left (wrap_err "exact") uu____3903
  
let rec mapM : 'a 'b . ('a -> 'b tac) -> 'a Prims.list -> 'b Prims.list tac =
  fun f  ->
    fun l  ->
      match l with
      | [] -> ret []
      | x::xs ->
          let uu____4037 = f x  in
          bind uu____4037
            (fun y  ->
               let uu____4045 = mapM f xs  in
               bind uu____4045 (fun ys  -> ret (y :: ys)))
  
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
          let uu____4116 = do_unify e ty1 ty2  in
          bind uu____4116
            (fun uu___353_4128  ->
               if uu___353_4128
               then ret acc
               else
                 (let uu____4147 = FStar_Syntax_Util.arrow_one ty1  in
                  match uu____4147 with
                  | FStar_Pervasives_Native.None  ->
                      let uu____4168 = FStar_Syntax_Print.term_to_string ty1
                         in
                      let uu____4169 = FStar_Syntax_Print.term_to_string ty2
                         in
                      fail2 "Could not instantiate, %s to %s" uu____4168
                        uu____4169
                  | FStar_Pervasives_Native.Some (b,c) ->
                      let uu____4184 =
                        let uu____4185 = FStar_Syntax_Util.is_total_comp c
                           in
                        Prims.op_Negation uu____4185  in
                      if uu____4184
                      then fail "Codomain is effectful"
                      else
                        (let uu____4205 =
                           new_uvar "apply arg" e
                             (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                            in
                         bind uu____4205
                           (fun uu____4231  ->
                              match uu____4231 with
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
      let uu____4317 =
        mlog
          (fun uu____4322  ->
             let uu____4323 = FStar_Syntax_Print.term_to_string tm  in
             FStar_Util.print1 "t_apply: tm = %s\n" uu____4323)
          (fun uu____4326  ->
             let uu____4327 = cur_goal ()  in
             bind uu____4327
               (fun goal  ->
                  let e = FStar_Tactics_Types.goal_env goal  in
                  let uu____4335 = __tc e tm  in
                  bind uu____4335
                    (fun uu____4356  ->
                       match uu____4356 with
                       | (tm1,typ,guard) ->
                           let typ1 = bnorm e typ  in
                           let uu____4369 =
                             let uu____4380 =
                               FStar_Tactics_Types.goal_type goal  in
                             try_match_by_application e typ1 uu____4380  in
                           bind uu____4369
                             (fun uvs  ->
                                let w =
                                  FStar_List.fold_right
                                    (fun uu____4423  ->
                                       fun w  ->
                                         match uu____4423 with
                                         | (uvt,q,uu____4441) ->
                                             FStar_Syntax_Util.mk_app w
                                               [(uvt, q)]) uvs tm1
                                   in
                                let uvset =
                                  let uu____4473 =
                                    FStar_Syntax_Free.new_uv_set ()  in
                                  FStar_List.fold_right
                                    (fun uu____4490  ->
                                       fun s  ->
                                         match uu____4490 with
                                         | (uu____4502,uu____4503,uv) ->
                                             let uu____4505 =
                                               FStar_Syntax_Free.uvars
                                                 uv.FStar_Syntax_Syntax.ctx_uvar_typ
                                                in
                                             FStar_Util.set_union s
                                               uu____4505) uvs uu____4473
                                   in
                                let free_in_some_goal uv =
                                  FStar_Util.set_mem uv uvset  in
                                let uu____4514 = solve' goal w  in
                                bind uu____4514
                                  (fun uu____4519  ->
                                     let uu____4520 =
                                       mapM
                                         (fun uu____4537  ->
                                            match uu____4537 with
                                            | (uvt,q,uv) ->
                                                let uu____4549 =
                                                  FStar_Syntax_Unionfind.find
                                                    uv.FStar_Syntax_Syntax.ctx_uvar_head
                                                   in
                                                (match uu____4549 with
                                                 | FStar_Pervasives_Native.Some
                                                     uu____4554 -> ret ()
                                                 | FStar_Pervasives_Native.None
                                                      ->
                                                     let uu____4555 =
                                                       uopt &&
                                                         (free_in_some_goal
                                                            uv)
                                                        in
                                                     if uu____4555
                                                     then ret ()
                                                     else
                                                       (let uu____4559 =
                                                          let uu____4562 =
                                                            bnorm_goal
                                                              (let uu___398_4565
                                                                 = goal  in
                                                               {
                                                                 FStar_Tactics_Types.goal_main_env
                                                                   =
                                                                   (uu___398_4565.FStar_Tactics_Types.goal_main_env);
                                                                 FStar_Tactics_Types.goal_ctx_uvar
                                                                   = uv;
                                                                 FStar_Tactics_Types.opts
                                                                   =
                                                                   (uu___398_4565.FStar_Tactics_Types.opts);
                                                                 FStar_Tactics_Types.is_guard
                                                                   = false;
                                                                 FStar_Tactics_Types.label
                                                                   =
                                                                   (uu___398_4565.FStar_Tactics_Types.label)
                                                               })
                                                             in
                                                          [uu____4562]  in
                                                        add_goals uu____4559)))
                                         uvs
                                        in
                                     bind uu____4520
                                       (fun uu____4569  ->
                                          proc_guard "apply guard" e guard))))))
         in
      FStar_All.pipe_left (wrap_err "apply") uu____4317
  
let (lemma_or_sq :
  FStar_Syntax_Syntax.comp ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun c  ->
    let ct = FStar_Syntax_Util.comp_to_comp_typ_nouniv c  in
    let uu____4594 =
      FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
        FStar_Parser_Const.effect_Lemma_lid
       in
    if uu____4594
    then
      let uu____4601 =
        match ct.FStar_Syntax_Syntax.effect_args with
        | pre::post::uu____4616 ->
            ((FStar_Pervasives_Native.fst pre),
              (FStar_Pervasives_Native.fst post))
        | uu____4669 -> failwith "apply_lemma: impossible: not a lemma"  in
      match uu____4601 with
      | (pre,post) ->
          let post1 =
            let uu____4701 =
              let uu____4712 =
                FStar_Syntax_Syntax.as_arg FStar_Syntax_Util.exp_unit  in
              [uu____4712]  in
            FStar_Syntax_Util.mk_app post uu____4701  in
          FStar_Pervasives_Native.Some (pre, post1)
    else
      (let uu____4742 =
         FStar_Syntax_Util.is_pure_effect ct.FStar_Syntax_Syntax.effect_name
          in
       if uu____4742
       then
         let uu____4749 =
           FStar_Syntax_Util.un_squash ct.FStar_Syntax_Syntax.result_typ  in
         FStar_Util.map_opt uu____4749
           (fun post  -> (FStar_Syntax_Util.t_true, post))
       else FStar_Pervasives_Native.None)
  
let (apply_lemma : FStar_Syntax_Syntax.term -> unit tac) =
  fun tm  ->
    let uu____4782 =
      let uu____4785 =
        bind get
          (fun ps  ->
             mlog
               (fun uu____4792  ->
                  let uu____4793 = FStar_Syntax_Print.term_to_string tm  in
                  FStar_Util.print1 "apply_lemma: tm = %s\n" uu____4793)
               (fun uu____4797  ->
                  let is_unit_t t =
                    let uu____4804 =
                      let uu____4805 = FStar_Syntax_Subst.compress t  in
                      uu____4805.FStar_Syntax_Syntax.n  in
                    match uu____4804 with
                    | FStar_Syntax_Syntax.Tm_fvar fv when
                        FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.unit_lid
                        -> true
                    | uu____4809 -> false  in
                  let uu____4810 = cur_goal ()  in
                  bind uu____4810
                    (fun goal  ->
                       let uu____4816 =
                         let uu____4825 = FStar_Tactics_Types.goal_env goal
                            in
                         __tc uu____4825 tm  in
                       bind uu____4816
                         (fun uu____4840  ->
                            match uu____4840 with
                            | (tm1,t,guard) ->
                                let uu____4852 =
                                  FStar_Syntax_Util.arrow_formals_comp t  in
                                (match uu____4852 with
                                 | (bs,comp) ->
                                     let uu____4885 = lemma_or_sq comp  in
                                     (match uu____4885 with
                                      | FStar_Pervasives_Native.None  ->
                                          fail
                                            "not a lemma or squashed function"
                                      | FStar_Pervasives_Native.Some
                                          (pre,post) ->
                                          let uu____4904 =
                                            FStar_List.fold_left
                                              (fun uu____4952  ->
                                                 fun uu____4953  ->
                                                   match (uu____4952,
                                                           uu____4953)
                                                   with
                                                   | ((uvs,guard1,subst1),
                                                      (b,aq)) ->
                                                       let b_t =
                                                         FStar_Syntax_Subst.subst
                                                           subst1
                                                           b.FStar_Syntax_Syntax.sort
                                                          in
                                                       let uu____5066 =
                                                         is_unit_t b_t  in
                                                       if uu____5066
                                                       then
                                                         (((FStar_Syntax_Util.exp_unit,
                                                             aq) :: uvs),
                                                           guard1,
                                                           ((FStar_Syntax_Syntax.NT
                                                               (b,
                                                                 FStar_Syntax_Util.exp_unit))
                                                           :: subst1))
                                                       else
                                                         (let uu____5104 =
                                                            let uu____5117 =
                                                              let uu____5118
                                                                =
                                                                FStar_Tactics_Types.goal_type
                                                                  goal
                                                                 in
                                                              uu____5118.FStar_Syntax_Syntax.pos
                                                               in
                                                            let uu____5121 =
                                                              FStar_Tactics_Types.goal_env
                                                                goal
                                                               in
                                                            FStar_TypeChecker_Util.new_implicit_var
                                                              "apply_lemma"
                                                              uu____5117
                                                              uu____5121 b_t
                                                             in
                                                          match uu____5104
                                                          with
                                                          | (u,uu____5139,g_u)
                                                              ->
                                                              let uu____5153
                                                                =
                                                                FStar_TypeChecker_Env.conj_guard
                                                                  guard1 g_u
                                                                 in
                                                              (((u, aq) ::
                                                                uvs),
                                                                uu____5153,
                                                                ((FStar_Syntax_Syntax.NT
                                                                    (b, u))
                                                                :: subst1))))
                                              ([], guard, []) bs
                                             in
                                          (match uu____4904 with
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
                                               let uu____5232 =
                                                 let uu____5235 =
                                                   FStar_Tactics_Types.goal_env
                                                     goal
                                                    in
                                                 let uu____5236 =
                                                   FStar_Syntax_Util.mk_squash
                                                     FStar_Syntax_Syntax.U_zero
                                                     post1
                                                    in
                                                 let uu____5237 =
                                                   FStar_Tactics_Types.goal_type
                                                     goal
                                                    in
                                                 do_unify uu____5235
                                                   uu____5236 uu____5237
                                                  in
                                               bind uu____5232
                                                 (fun b  ->
                                                    if Prims.op_Negation b
                                                    then
                                                      let uu____5245 =
                                                        let uu____5246 =
                                                          FStar_Tactics_Types.goal_env
                                                            goal
                                                           in
                                                        tts uu____5246 tm1
                                                         in
                                                      let uu____5247 =
                                                        let uu____5248 =
                                                          FStar_Tactics_Types.goal_env
                                                            goal
                                                           in
                                                        let uu____5249 =
                                                          FStar_Syntax_Util.mk_squash
                                                            FStar_Syntax_Syntax.U_zero
                                                            post1
                                                           in
                                                        tts uu____5248
                                                          uu____5249
                                                         in
                                                      let uu____5250 =
                                                        let uu____5251 =
                                                          FStar_Tactics_Types.goal_env
                                                            goal
                                                           in
                                                        let uu____5252 =
                                                          FStar_Tactics_Types.goal_type
                                                            goal
                                                           in
                                                        tts uu____5251
                                                          uu____5252
                                                         in
                                                      fail3
                                                        "Cannot instantiate lemma %s (with postcondition: %s) to match goal (%s)"
                                                        uu____5245 uu____5247
                                                        uu____5250
                                                    else
                                                      (let uu____5254 =
                                                         add_implicits
                                                           implicits.FStar_TypeChecker_Env.implicits
                                                          in
                                                       bind uu____5254
                                                         (fun uu____5259  ->
                                                            let uu____5260 =
                                                              solve' goal
                                                                FStar_Syntax_Util.exp_unit
                                                               in
                                                            bind uu____5260
                                                              (fun uu____5268
                                                                  ->
                                                                 let is_free_uvar
                                                                   uv t1 =
                                                                   let free_uvars
                                                                    =
                                                                    let uu____5293
                                                                    =
                                                                    let uu____5296
                                                                    =
                                                                    FStar_Syntax_Free.uvars
                                                                    t1  in
                                                                    FStar_Util.set_elements
                                                                    uu____5296
                                                                     in
                                                                    FStar_List.map
                                                                    (fun x 
                                                                    ->
                                                                    x.FStar_Syntax_Syntax.ctx_uvar_head)
                                                                    uu____5293
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
                                                                    let uu____5331
                                                                    =
                                                                    FStar_Tactics_Types.goal_type
                                                                    g'  in
                                                                    is_free_uvar
                                                                    uv
                                                                    uu____5331)
                                                                    goals
                                                                    in
                                                                 let checkone
                                                                   t1 goals =
                                                                   let uu____5347
                                                                    =
                                                                    FStar_Syntax_Util.head_and_args
                                                                    t1  in
                                                                   match uu____5347
                                                                   with
                                                                   | 
                                                                   (hd1,uu____5365)
                                                                    ->
                                                                    (match 
                                                                    hd1.FStar_Syntax_Syntax.n
                                                                    with
                                                                    | 
                                                                    FStar_Syntax_Syntax.Tm_uvar
                                                                    (uv,uu____5391)
                                                                    ->
                                                                    appears
                                                                    uv.FStar_Syntax_Syntax.ctx_uvar_head
                                                                    goals
                                                                    | 
                                                                    uu____5408
                                                                    -> false)
                                                                    in
                                                                 let uu____5409
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
                                                                    let uu____5439
                                                                    =
                                                                    FStar_Syntax_Util.head_and_args
                                                                    term  in
                                                                    match uu____5439
                                                                    with
                                                                    | 
                                                                    (hd1,uu____5461)
                                                                    ->
                                                                    let uu____5486
                                                                    =
                                                                    let uu____5487
                                                                    =
                                                                    FStar_Syntax_Subst.compress
                                                                    hd1  in
                                                                    uu____5487.FStar_Syntax_Syntax.n
                                                                     in
                                                                    (match uu____5486
                                                                    with
                                                                    | 
                                                                    FStar_Syntax_Syntax.Tm_uvar
                                                                    (ctx_uvar1,uu____5495)
                                                                    ->
                                                                    let goal1
                                                                    =
                                                                    bnorm_goal
                                                                    (let uu___399_5515
                                                                    = goal
                                                                     in
                                                                    {
                                                                    FStar_Tactics_Types.goal_main_env
                                                                    =
                                                                    (uu___399_5515.FStar_Tactics_Types.goal_main_env);
                                                                    FStar_Tactics_Types.goal_ctx_uvar
                                                                    =
                                                                    ctx_uvar1;
                                                                    FStar_Tactics_Types.opts
                                                                    =
                                                                    (uu___399_5515.FStar_Tactics_Types.opts);
                                                                    FStar_Tactics_Types.is_guard
                                                                    =
                                                                    (uu___399_5515.FStar_Tactics_Types.is_guard);
                                                                    FStar_Tactics_Types.label
                                                                    =
                                                                    (uu___399_5515.FStar_Tactics_Types.label)
                                                                    })  in
                                                                    ret
                                                                    [goal1]
                                                                    | 
                                                                    uu____5518
                                                                    ->
                                                                    mlog
                                                                    (fun
                                                                    uu____5524
                                                                     ->
                                                                    let uu____5525
                                                                    =
                                                                    FStar_Syntax_Print.uvar_to_string
                                                                    ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_head
                                                                     in
                                                                    let uu____5526
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    term  in
                                                                    FStar_Util.print2
                                                                    "apply_lemma: arg %s unified to (%s)\n"
                                                                    uu____5525
                                                                    uu____5526)
                                                                    (fun
                                                                    uu____5531
                                                                     ->
                                                                    let env =
                                                                    let uu___400_5533
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    goal  in
                                                                    {
                                                                    FStar_TypeChecker_Env.solver
                                                                    =
                                                                    (uu___400_5533.FStar_TypeChecker_Env.solver);
                                                                    FStar_TypeChecker_Env.range
                                                                    =
                                                                    (uu___400_5533.FStar_TypeChecker_Env.range);
                                                                    FStar_TypeChecker_Env.curmodule
                                                                    =
                                                                    (uu___400_5533.FStar_TypeChecker_Env.curmodule);
                                                                    FStar_TypeChecker_Env.gamma
                                                                    =
                                                                    (ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_gamma);
                                                                    FStar_TypeChecker_Env.gamma_sig
                                                                    =
                                                                    (uu___400_5533.FStar_TypeChecker_Env.gamma_sig);
                                                                    FStar_TypeChecker_Env.gamma_cache
                                                                    =
                                                                    (uu___400_5533.FStar_TypeChecker_Env.gamma_cache);
                                                                    FStar_TypeChecker_Env.modules
                                                                    =
                                                                    (uu___400_5533.FStar_TypeChecker_Env.modules);
                                                                    FStar_TypeChecker_Env.expected_typ
                                                                    =
                                                                    (uu___400_5533.FStar_TypeChecker_Env.expected_typ);
                                                                    FStar_TypeChecker_Env.sigtab
                                                                    =
                                                                    (uu___400_5533.FStar_TypeChecker_Env.sigtab);
                                                                    FStar_TypeChecker_Env.attrtab
                                                                    =
                                                                    (uu___400_5533.FStar_TypeChecker_Env.attrtab);
                                                                    FStar_TypeChecker_Env.is_pattern
                                                                    =
                                                                    (uu___400_5533.FStar_TypeChecker_Env.is_pattern);
                                                                    FStar_TypeChecker_Env.instantiate_imp
                                                                    =
                                                                    (uu___400_5533.FStar_TypeChecker_Env.instantiate_imp);
                                                                    FStar_TypeChecker_Env.effects
                                                                    =
                                                                    (uu___400_5533.FStar_TypeChecker_Env.effects);
                                                                    FStar_TypeChecker_Env.generalize
                                                                    =
                                                                    (uu___400_5533.FStar_TypeChecker_Env.generalize);
                                                                    FStar_TypeChecker_Env.letrecs
                                                                    =
                                                                    (uu___400_5533.FStar_TypeChecker_Env.letrecs);
                                                                    FStar_TypeChecker_Env.top_level
                                                                    =
                                                                    (uu___400_5533.FStar_TypeChecker_Env.top_level);
                                                                    FStar_TypeChecker_Env.check_uvars
                                                                    =
                                                                    (uu___400_5533.FStar_TypeChecker_Env.check_uvars);
                                                                    FStar_TypeChecker_Env.use_eq
                                                                    =
                                                                    (uu___400_5533.FStar_TypeChecker_Env.use_eq);
                                                                    FStar_TypeChecker_Env.is_iface
                                                                    =
                                                                    (uu___400_5533.FStar_TypeChecker_Env.is_iface);
                                                                    FStar_TypeChecker_Env.admit
                                                                    =
                                                                    (uu___400_5533.FStar_TypeChecker_Env.admit);
                                                                    FStar_TypeChecker_Env.lax
                                                                    =
                                                                    (uu___400_5533.FStar_TypeChecker_Env.lax);
                                                                    FStar_TypeChecker_Env.lax_universes
                                                                    =
                                                                    (uu___400_5533.FStar_TypeChecker_Env.lax_universes);
                                                                    FStar_TypeChecker_Env.phase1
                                                                    =
                                                                    (uu___400_5533.FStar_TypeChecker_Env.phase1);
                                                                    FStar_TypeChecker_Env.failhard
                                                                    =
                                                                    (uu___400_5533.FStar_TypeChecker_Env.failhard);
                                                                    FStar_TypeChecker_Env.nosynth
                                                                    =
                                                                    (uu___400_5533.FStar_TypeChecker_Env.nosynth);
                                                                    FStar_TypeChecker_Env.uvar_subtyping
                                                                    =
                                                                    (uu___400_5533.FStar_TypeChecker_Env.uvar_subtyping);
                                                                    FStar_TypeChecker_Env.tc_term
                                                                    =
                                                                    (uu___400_5533.FStar_TypeChecker_Env.tc_term);
                                                                    FStar_TypeChecker_Env.type_of
                                                                    =
                                                                    (uu___400_5533.FStar_TypeChecker_Env.type_of);
                                                                    FStar_TypeChecker_Env.universe_of
                                                                    =
                                                                    (uu___400_5533.FStar_TypeChecker_Env.universe_of);
                                                                    FStar_TypeChecker_Env.check_type_of
                                                                    =
                                                                    (uu___400_5533.FStar_TypeChecker_Env.check_type_of);
                                                                    FStar_TypeChecker_Env.use_bv_sorts
                                                                    =
                                                                    (uu___400_5533.FStar_TypeChecker_Env.use_bv_sorts);
                                                                    FStar_TypeChecker_Env.qtbl_name_and_index
                                                                    =
                                                                    (uu___400_5533.FStar_TypeChecker_Env.qtbl_name_and_index);
                                                                    FStar_TypeChecker_Env.normalized_eff_names
                                                                    =
                                                                    (uu___400_5533.FStar_TypeChecker_Env.normalized_eff_names);
                                                                    FStar_TypeChecker_Env.fv_delta_depths
                                                                    =
                                                                    (uu___400_5533.FStar_TypeChecker_Env.fv_delta_depths);
                                                                    FStar_TypeChecker_Env.proof_ns
                                                                    =
                                                                    (uu___400_5533.FStar_TypeChecker_Env.proof_ns);
                                                                    FStar_TypeChecker_Env.synth_hook
                                                                    =
                                                                    (uu___400_5533.FStar_TypeChecker_Env.synth_hook);
                                                                    FStar_TypeChecker_Env.splice
                                                                    =
                                                                    (uu___400_5533.FStar_TypeChecker_Env.splice);
                                                                    FStar_TypeChecker_Env.postprocess
                                                                    =
                                                                    (uu___400_5533.FStar_TypeChecker_Env.postprocess);
                                                                    FStar_TypeChecker_Env.is_native_tactic
                                                                    =
                                                                    (uu___400_5533.FStar_TypeChecker_Env.is_native_tactic);
                                                                    FStar_TypeChecker_Env.identifier_info
                                                                    =
                                                                    (uu___400_5533.FStar_TypeChecker_Env.identifier_info);
                                                                    FStar_TypeChecker_Env.tc_hooks
                                                                    =
                                                                    (uu___400_5533.FStar_TypeChecker_Env.tc_hooks);
                                                                    FStar_TypeChecker_Env.dsenv
                                                                    =
                                                                    (uu___400_5533.FStar_TypeChecker_Env.dsenv);
                                                                    FStar_TypeChecker_Env.nbe
                                                                    =
                                                                    (uu___400_5533.FStar_TypeChecker_Env.nbe)
                                                                    }  in
                                                                    let g_typ
                                                                    =
                                                                    FStar_TypeChecker_TcTerm.check_type_of_well_typed_term'
                                                                    true env
                                                                    term
                                                                    ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_typ
                                                                     in
                                                                    let uu____5535
                                                                    =
                                                                    let uu____5538
                                                                    =
                                                                    if
                                                                    ps.FStar_Tactics_Types.tac_verb_dbg
                                                                    then
                                                                    let uu____5539
                                                                    =
                                                                    FStar_Syntax_Print.ctx_uvar_to_string
                                                                    ctx_uvar
                                                                     in
                                                                    let uu____5540
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    term  in
                                                                    FStar_Util.format2
                                                                    "apply_lemma solved arg %s to %s\n"
                                                                    uu____5539
                                                                    uu____5540
                                                                    else
                                                                    "apply_lemma solved arg"
                                                                     in
                                                                    let uu____5542
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    goal  in
                                                                    proc_guard
                                                                    uu____5538
                                                                    uu____5542
                                                                    g_typ  in
                                                                    bind
                                                                    uu____5535
                                                                    (fun
                                                                    uu____5546
                                                                     ->
                                                                    ret [])))))
                                                                    in
                                                                 bind
                                                                   uu____5409
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
                                                                    let uu____5608
                                                                    = f x xs1
                                                                     in
                                                                    if
                                                                    uu____5608
                                                                    then
                                                                    let uu____5611
                                                                    =
                                                                    filter' f
                                                                    xs1  in x
                                                                    ::
                                                                    uu____5611
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
                                                                    let uu____5625
                                                                    =
                                                                    let uu____5626
                                                                    =
                                                                    FStar_Tactics_Types.goal_witness
                                                                    g  in
                                                                    checkone
                                                                    uu____5626
                                                                    goals  in
                                                                    Prims.op_Negation
                                                                    uu____5625)
                                                                    sub_goals1
                                                                     in
                                                                    let uu____5627
                                                                    =
                                                                    let uu____5630
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    goal  in
                                                                    proc_guard
                                                                    "apply_lemma guard"
                                                                    uu____5630
                                                                    guard  in
                                                                    bind
                                                                    uu____5627
                                                                    (fun
                                                                    uu____5633
                                                                     ->
                                                                    let uu____5634
                                                                    =
                                                                    let uu____5637
                                                                    =
                                                                    let uu____5638
                                                                    =
                                                                    let uu____5639
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    goal  in
                                                                    let uu____5640
                                                                    =
                                                                    FStar_Syntax_Util.mk_squash
                                                                    FStar_Syntax_Syntax.U_zero
                                                                    pre1  in
                                                                    istrivial
                                                                    uu____5639
                                                                    uu____5640
                                                                     in
                                                                    Prims.op_Negation
                                                                    uu____5638
                                                                     in
                                                                    if
                                                                    uu____5637
                                                                    then
                                                                    let uu____5643
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    goal  in
                                                                    add_irrelevant_goal
                                                                    "apply_lemma precondition"
                                                                    uu____5643
                                                                    pre1
                                                                    goal.FStar_Tactics_Types.opts
                                                                    goal.FStar_Tactics_Types.label
                                                                    else
                                                                    ret ()
                                                                     in
                                                                    bind
                                                                    uu____5634
                                                                    (fun
                                                                    uu____5646
                                                                     ->
                                                                    add_goals
                                                                    sub_goals2))))))))))))))
         in
      focus uu____4785  in
    FStar_All.pipe_left (wrap_err "apply_lemma") uu____4782
  
let (destruct_eq' :
  FStar_Reflection_Data.typ ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun typ  ->
    let uu____5668 = FStar_Syntax_Util.destruct_typ_as_formula typ  in
    match uu____5668 with
    | FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn
        (l,uu____5678::(e1,uu____5680)::(e2,uu____5682)::[])) when
        FStar_Ident.lid_equals l FStar_Parser_Const.eq2_lid ->
        FStar_Pervasives_Native.Some (e1, e2)
    | uu____5743 -> FStar_Pervasives_Native.None
  
let (destruct_eq :
  FStar_Reflection_Data.typ ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun typ  ->
    let uu____5767 = destruct_eq' typ  in
    match uu____5767 with
    | FStar_Pervasives_Native.Some t -> FStar_Pervasives_Native.Some t
    | FStar_Pervasives_Native.None  ->
        let uu____5797 = FStar_Syntax_Util.un_squash typ  in
        (match uu____5797 with
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
        let uu____5859 = FStar_TypeChecker_Env.pop_bv e1  in
        match uu____5859 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (bv',e') ->
            if FStar_Syntax_Syntax.bv_eq bvar bv'
            then FStar_Pervasives_Native.Some (e', [])
            else
              (let uu____5907 = aux e'  in
               FStar_Util.map_opt uu____5907
                 (fun uu____5931  ->
                    match uu____5931 with | (e'',bvs) -> (e'', (bv' :: bvs))))
         in
      let uu____5952 = aux e  in
      FStar_Util.map_opt uu____5952
        (fun uu____5976  ->
           match uu____5976 with | (e',bvs) -> (e', (FStar_List.rev bvs)))
  
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
          let uu____6043 =
            let uu____6052 = FStar_Tactics_Types.goal_env g  in
            split_env b1 uu____6052  in
          FStar_Util.map_opt uu____6043
            (fun uu____6067  ->
               match uu____6067 with
               | (e0,bvs) ->
                   let s1 bv =
                     let uu___401_6086 = bv  in
                     let uu____6087 =
                       FStar_Syntax_Subst.subst s bv.FStar_Syntax_Syntax.sort
                        in
                     {
                       FStar_Syntax_Syntax.ppname =
                         (uu___401_6086.FStar_Syntax_Syntax.ppname);
                       FStar_Syntax_Syntax.index =
                         (uu___401_6086.FStar_Syntax_Syntax.index);
                       FStar_Syntax_Syntax.sort = uu____6087
                     }  in
                   let bvs1 = FStar_List.map s1 bvs  in
                   let new_env = push_bvs e0 (b2 :: bvs1)  in
                   let new_goal =
                     let uu___402_6095 = g.FStar_Tactics_Types.goal_ctx_uvar
                        in
                     let uu____6096 =
                       FStar_TypeChecker_Env.all_binders new_env  in
                     let uu____6105 =
                       let uu____6108 = FStar_Tactics_Types.goal_type g  in
                       FStar_Syntax_Subst.subst s uu____6108  in
                     {
                       FStar_Syntax_Syntax.ctx_uvar_head =
                         (uu___402_6095.FStar_Syntax_Syntax.ctx_uvar_head);
                       FStar_Syntax_Syntax.ctx_uvar_gamma =
                         (new_env.FStar_TypeChecker_Env.gamma);
                       FStar_Syntax_Syntax.ctx_uvar_binders = uu____6096;
                       FStar_Syntax_Syntax.ctx_uvar_typ = uu____6105;
                       FStar_Syntax_Syntax.ctx_uvar_reason =
                         (uu___402_6095.FStar_Syntax_Syntax.ctx_uvar_reason);
                       FStar_Syntax_Syntax.ctx_uvar_should_check =
                         (uu___402_6095.FStar_Syntax_Syntax.ctx_uvar_should_check);
                       FStar_Syntax_Syntax.ctx_uvar_range =
                         (uu___402_6095.FStar_Syntax_Syntax.ctx_uvar_range)
                     }  in
                   let uu___403_6109 = g  in
                   {
                     FStar_Tactics_Types.goal_main_env =
                       (uu___403_6109.FStar_Tactics_Types.goal_main_env);
                     FStar_Tactics_Types.goal_ctx_uvar = new_goal;
                     FStar_Tactics_Types.opts =
                       (uu___403_6109.FStar_Tactics_Types.opts);
                     FStar_Tactics_Types.is_guard =
                       (uu___403_6109.FStar_Tactics_Types.is_guard);
                     FStar_Tactics_Types.label =
                       (uu___403_6109.FStar_Tactics_Types.label)
                   })
  
let (rewrite : FStar_Syntax_Syntax.binder -> unit tac) =
  fun h  ->
    let uu____6119 =
      let uu____6122 = cur_goal ()  in
      bind uu____6122
        (fun goal  ->
           let uu____6130 = h  in
           match uu____6130 with
           | (bv,uu____6134) ->
               mlog
                 (fun uu____6142  ->
                    let uu____6143 = FStar_Syntax_Print.bv_to_string bv  in
                    let uu____6144 =
                      FStar_Syntax_Print.term_to_string
                        bv.FStar_Syntax_Syntax.sort
                       in
                    FStar_Util.print2 "+++Rewrite %s : %s\n" uu____6143
                      uu____6144)
                 (fun uu____6147  ->
                    let uu____6148 =
                      let uu____6157 = FStar_Tactics_Types.goal_env goal  in
                      split_env bv uu____6157  in
                    match uu____6148 with
                    | FStar_Pervasives_Native.None  ->
                        fail "binder not found in environment"
                    | FStar_Pervasives_Native.Some (e0,bvs) ->
                        let uu____6178 =
                          destruct_eq bv.FStar_Syntax_Syntax.sort  in
                        (match uu____6178 with
                         | FStar_Pervasives_Native.Some (x,e) ->
                             let uu____6193 =
                               let uu____6194 = FStar_Syntax_Subst.compress x
                                  in
                               uu____6194.FStar_Syntax_Syntax.n  in
                             (match uu____6193 with
                              | FStar_Syntax_Syntax.Tm_name x1 ->
                                  let s = [FStar_Syntax_Syntax.NT (x1, e)]
                                     in
                                  let s1 bv1 =
                                    let uu___404_6211 = bv1  in
                                    let uu____6212 =
                                      FStar_Syntax_Subst.subst s
                                        bv1.FStar_Syntax_Syntax.sort
                                       in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___404_6211.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___404_6211.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = uu____6212
                                    }  in
                                  let bvs1 = FStar_List.map s1 bvs  in
                                  let new_env = push_bvs e0 (bv :: bvs1)  in
                                  let new_goal =
                                    let uu___405_6220 =
                                      goal.FStar_Tactics_Types.goal_ctx_uvar
                                       in
                                    let uu____6221 =
                                      FStar_TypeChecker_Env.all_binders
                                        new_env
                                       in
                                    let uu____6230 =
                                      let uu____6233 =
                                        FStar_Tactics_Types.goal_type goal
                                         in
                                      FStar_Syntax_Subst.subst s uu____6233
                                       in
                                    {
                                      FStar_Syntax_Syntax.ctx_uvar_head =
                                        (uu___405_6220.FStar_Syntax_Syntax.ctx_uvar_head);
                                      FStar_Syntax_Syntax.ctx_uvar_gamma =
                                        (new_env.FStar_TypeChecker_Env.gamma);
                                      FStar_Syntax_Syntax.ctx_uvar_binders =
                                        uu____6221;
                                      FStar_Syntax_Syntax.ctx_uvar_typ =
                                        uu____6230;
                                      FStar_Syntax_Syntax.ctx_uvar_reason =
                                        (uu___405_6220.FStar_Syntax_Syntax.ctx_uvar_reason);
                                      FStar_Syntax_Syntax.ctx_uvar_should_check
                                        =
                                        (uu___405_6220.FStar_Syntax_Syntax.ctx_uvar_should_check);
                                      FStar_Syntax_Syntax.ctx_uvar_range =
                                        (uu___405_6220.FStar_Syntax_Syntax.ctx_uvar_range)
                                    }  in
                                  replace_cur
                                    (let uu___406_6236 = goal  in
                                     {
                                       FStar_Tactics_Types.goal_main_env =
                                         (uu___406_6236.FStar_Tactics_Types.goal_main_env);
                                       FStar_Tactics_Types.goal_ctx_uvar =
                                         new_goal;
                                       FStar_Tactics_Types.opts =
                                         (uu___406_6236.FStar_Tactics_Types.opts);
                                       FStar_Tactics_Types.is_guard =
                                         (uu___406_6236.FStar_Tactics_Types.is_guard);
                                       FStar_Tactics_Types.label =
                                         (uu___406_6236.FStar_Tactics_Types.label)
                                     })
                              | uu____6237 ->
                                  fail
                                    "Not an equality hypothesis with a variable on the LHS")
                         | uu____6238 -> fail "Not an equality hypothesis")))
       in
    FStar_All.pipe_left (wrap_err "rewrite") uu____6119
  
let (rename_to : FStar_Syntax_Syntax.binder -> Prims.string -> unit tac) =
  fun b  ->
    fun s  ->
      let uu____6263 =
        let uu____6266 = cur_goal ()  in
        bind uu____6266
          (fun goal  ->
             let uu____6277 = b  in
             match uu____6277 with
             | (bv,uu____6281) ->
                 let bv' =
                   let uu____6287 =
                     let uu___407_6288 = bv  in
                     let uu____6289 =
                       FStar_Ident.mk_ident
                         (s,
                           ((bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange))
                        in
                     {
                       FStar_Syntax_Syntax.ppname = uu____6289;
                       FStar_Syntax_Syntax.index =
                         (uu___407_6288.FStar_Syntax_Syntax.index);
                       FStar_Syntax_Syntax.sort =
                         (uu___407_6288.FStar_Syntax_Syntax.sort)
                     }  in
                   FStar_Syntax_Syntax.freshen_bv uu____6287  in
                 let s1 =
                   let uu____6293 =
                     let uu____6294 =
                       let uu____6301 = FStar_Syntax_Syntax.bv_to_name bv'
                          in
                       (bv, uu____6301)  in
                     FStar_Syntax_Syntax.NT uu____6294  in
                   [uu____6293]  in
                 let uu____6306 = subst_goal bv bv' s1 goal  in
                 (match uu____6306 with
                  | FStar_Pervasives_Native.None  ->
                      fail "binder not found in environment"
                  | FStar_Pervasives_Native.Some goal1 -> replace_cur goal1))
         in
      FStar_All.pipe_left (wrap_err "rename_to") uu____6263
  
let (binder_retype : FStar_Syntax_Syntax.binder -> unit tac) =
  fun b  ->
    let uu____6325 =
      let uu____6328 = cur_goal ()  in
      bind uu____6328
        (fun goal  ->
           let uu____6337 = b  in
           match uu____6337 with
           | (bv,uu____6341) ->
               let uu____6346 =
                 let uu____6355 = FStar_Tactics_Types.goal_env goal  in
                 split_env bv uu____6355  in
               (match uu____6346 with
                | FStar_Pervasives_Native.None  ->
                    fail "binder is not present in environment"
                | FStar_Pervasives_Native.Some (e0,bvs) ->
                    let uu____6376 = FStar_Syntax_Util.type_u ()  in
                    (match uu____6376 with
                     | (ty,u) ->
                         let uu____6385 = new_uvar "binder_retype" e0 ty  in
                         bind uu____6385
                           (fun uu____6403  ->
                              match uu____6403 with
                              | (t',u_t') ->
                                  let bv'' =
                                    let uu___408_6413 = bv  in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___408_6413.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___408_6413.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = t'
                                    }  in
                                  let s =
                                    let uu____6417 =
                                      let uu____6418 =
                                        let uu____6425 =
                                          FStar_Syntax_Syntax.bv_to_name bv''
                                           in
                                        (bv, uu____6425)  in
                                      FStar_Syntax_Syntax.NT uu____6418  in
                                    [uu____6417]  in
                                  let bvs1 =
                                    FStar_List.map
                                      (fun b1  ->
                                         let uu___409_6437 = b1  in
                                         let uu____6438 =
                                           FStar_Syntax_Subst.subst s
                                             b1.FStar_Syntax_Syntax.sort
                                            in
                                         {
                                           FStar_Syntax_Syntax.ppname =
                                             (uu___409_6437.FStar_Syntax_Syntax.ppname);
                                           FStar_Syntax_Syntax.index =
                                             (uu___409_6437.FStar_Syntax_Syntax.index);
                                           FStar_Syntax_Syntax.sort =
                                             uu____6438
                                         }) bvs
                                     in
                                  let env' = push_bvs e0 (bv'' :: bvs1)  in
                                  bind __dismiss
                                    (fun uu____6445  ->
                                       let new_goal =
                                         let uu____6447 =
                                           FStar_Tactics_Types.goal_with_env
                                             goal env'
                                            in
                                         let uu____6448 =
                                           let uu____6449 =
                                             FStar_Tactics_Types.goal_type
                                               goal
                                              in
                                           FStar_Syntax_Subst.subst s
                                             uu____6449
                                            in
                                         FStar_Tactics_Types.goal_with_type
                                           uu____6447 uu____6448
                                          in
                                       let uu____6450 = add_goals [new_goal]
                                          in
                                       bind uu____6450
                                         (fun uu____6455  ->
                                            let uu____6456 =
                                              FStar_Syntax_Util.mk_eq2
                                                (FStar_Syntax_Syntax.U_succ u)
                                                ty
                                                bv.FStar_Syntax_Syntax.sort
                                                t'
                                               in
                                            add_irrelevant_goal
                                              "binder_retype equation" e0
                                              uu____6456
                                              goal.FStar_Tactics_Types.opts
                                              goal.FStar_Tactics_Types.label))))))
       in
    FStar_All.pipe_left (wrap_err "binder_retype") uu____6325
  
let (norm_binder_type :
  FStar_Syntax_Embeddings.norm_step Prims.list ->
    FStar_Syntax_Syntax.binder -> unit tac)
  =
  fun s  ->
    fun b  ->
      let uu____6479 =
        let uu____6482 = cur_goal ()  in
        bind uu____6482
          (fun goal  ->
             let uu____6491 = b  in
             match uu____6491 with
             | (bv,uu____6495) ->
                 let uu____6500 =
                   let uu____6509 = FStar_Tactics_Types.goal_env goal  in
                   split_env bv uu____6509  in
                 (match uu____6500 with
                  | FStar_Pervasives_Native.None  ->
                      fail "binder is not present in environment"
                  | FStar_Pervasives_Native.Some (e0,bvs) ->
                      let steps =
                        let uu____6533 =
                          FStar_TypeChecker_Normalize.tr_norm_steps s  in
                        FStar_List.append
                          [FStar_TypeChecker_Env.Reify;
                          FStar_TypeChecker_Env.UnfoldTac] uu____6533
                         in
                      let sort' =
                        normalize steps e0 bv.FStar_Syntax_Syntax.sort  in
                      let bv' =
                        let uu___410_6538 = bv  in
                        {
                          FStar_Syntax_Syntax.ppname =
                            (uu___410_6538.FStar_Syntax_Syntax.ppname);
                          FStar_Syntax_Syntax.index =
                            (uu___410_6538.FStar_Syntax_Syntax.index);
                          FStar_Syntax_Syntax.sort = sort'
                        }  in
                      let env' = push_bvs e0 (bv' :: bvs)  in
                      let uu____6540 =
                        FStar_Tactics_Types.goal_with_env goal env'  in
                      replace_cur uu____6540))
         in
      FStar_All.pipe_left (wrap_err "norm_binder_type") uu____6479
  
let (revert : unit -> unit tac) =
  fun uu____6551  ->
    let uu____6554 = cur_goal ()  in
    bind uu____6554
      (fun goal  ->
         let uu____6560 =
           let uu____6567 = FStar_Tactics_Types.goal_env goal  in
           FStar_TypeChecker_Env.pop_bv uu____6567  in
         match uu____6560 with
         | FStar_Pervasives_Native.None  ->
             fail "Cannot revert; empty context"
         | FStar_Pervasives_Native.Some (x,env') ->
             let typ' =
               let uu____6583 =
                 let uu____6586 = FStar_Tactics_Types.goal_type goal  in
                 FStar_Syntax_Syntax.mk_Total uu____6586  in
               FStar_Syntax_Util.arrow [(x, FStar_Pervasives_Native.None)]
                 uu____6583
                in
             let uu____6601 = new_uvar "revert" env' typ'  in
             bind uu____6601
               (fun uu____6616  ->
                  match uu____6616 with
                  | (r,u_r) ->
                      let uu____6625 =
                        let uu____6628 =
                          let uu____6629 =
                            let uu____6630 =
                              FStar_Tactics_Types.goal_type goal  in
                            uu____6630.FStar_Syntax_Syntax.pos  in
                          let uu____6633 =
                            let uu____6638 =
                              let uu____6639 =
                                let uu____6648 =
                                  FStar_Syntax_Syntax.bv_to_name x  in
                                FStar_Syntax_Syntax.as_arg uu____6648  in
                              [uu____6639]  in
                            FStar_Syntax_Syntax.mk_Tm_app r uu____6638  in
                          uu____6633 FStar_Pervasives_Native.None uu____6629
                           in
                        set_solution goal uu____6628  in
                      bind uu____6625
                        (fun uu____6669  ->
                           let g =
                             FStar_Tactics_Types.mk_goal env' u_r
                               goal.FStar_Tactics_Types.opts
                               goal.FStar_Tactics_Types.is_guard
                               goal.FStar_Tactics_Types.label
                              in
                           replace_cur g)))
  
let (free_in :
  FStar_Syntax_Syntax.bv -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun bv  ->
    fun t  ->
      let uu____6681 = FStar_Syntax_Free.names t  in
      FStar_Util.set_mem bv uu____6681
  
let rec (clear : FStar_Syntax_Syntax.binder -> unit tac) =
  fun b  ->
    let bv = FStar_Pervasives_Native.fst b  in
    let uu____6696 = cur_goal ()  in
    bind uu____6696
      (fun goal  ->
         mlog
           (fun uu____6704  ->
              let uu____6705 = FStar_Syntax_Print.binder_to_string b  in
              let uu____6706 =
                let uu____6707 =
                  let uu____6708 =
                    let uu____6717 = FStar_Tactics_Types.goal_env goal  in
                    FStar_TypeChecker_Env.all_binders uu____6717  in
                  FStar_All.pipe_right uu____6708 FStar_List.length  in
                FStar_All.pipe_right uu____6707 FStar_Util.string_of_int  in
              FStar_Util.print2 "Clear of (%s), env has %s binders\n"
                uu____6705 uu____6706)
           (fun uu____6734  ->
              let uu____6735 =
                let uu____6744 = FStar_Tactics_Types.goal_env goal  in
                split_env bv uu____6744  in
              match uu____6735 with
              | FStar_Pervasives_Native.None  ->
                  fail "Cannot clear; binder not in environment"
              | FStar_Pervasives_Native.Some (e',bvs) ->
                  let rec check1 bvs1 =
                    match bvs1 with
                    | [] -> ret ()
                    | bv'::bvs2 ->
                        let uu____6783 =
                          free_in bv bv'.FStar_Syntax_Syntax.sort  in
                        if uu____6783
                        then
                          let uu____6786 =
                            let uu____6787 =
                              FStar_Syntax_Print.bv_to_string bv'  in
                            FStar_Util.format1
                              "Cannot clear; binder present in the type of %s"
                              uu____6787
                             in
                          fail uu____6786
                        else check1 bvs2
                     in
                  let uu____6789 =
                    let uu____6790 = FStar_Tactics_Types.goal_type goal  in
                    free_in bv uu____6790  in
                  if uu____6789
                  then fail "Cannot clear; binder present in goal"
                  else
                    (let uu____6794 = check1 bvs  in
                     bind uu____6794
                       (fun uu____6800  ->
                          let env' = push_bvs e' bvs  in
                          let uu____6802 =
                            let uu____6809 =
                              FStar_Tactics_Types.goal_type goal  in
                            new_uvar "clear.witness" env' uu____6809  in
                          bind uu____6802
                            (fun uu____6818  ->
                               match uu____6818 with
                               | (ut,uvar_ut) ->
                                   let uu____6827 = set_solution goal ut  in
                                   bind uu____6827
                                     (fun uu____6832  ->
                                        let uu____6833 =
                                          FStar_Tactics_Types.mk_goal env'
                                            uvar_ut
                                            goal.FStar_Tactics_Types.opts
                                            goal.FStar_Tactics_Types.is_guard
                                            goal.FStar_Tactics_Types.label
                                           in
                                        replace_cur uu____6833))))))
  
let (clear_top : unit -> unit tac) =
  fun uu____6840  ->
    let uu____6843 = cur_goal ()  in
    bind uu____6843
      (fun goal  ->
         let uu____6849 =
           let uu____6856 = FStar_Tactics_Types.goal_env goal  in
           FStar_TypeChecker_Env.pop_bv uu____6856  in
         match uu____6849 with
         | FStar_Pervasives_Native.None  ->
             fail "Cannot clear; empty context"
         | FStar_Pervasives_Native.Some (x,uu____6864) ->
             let uu____6869 = FStar_Syntax_Syntax.mk_binder x  in
             clear uu____6869)
  
let (prune : Prims.string -> unit tac) =
  fun s  ->
    let uu____6879 = cur_goal ()  in
    bind uu____6879
      (fun g  ->
         let ctx = FStar_Tactics_Types.goal_env g  in
         let ctx' =
           let uu____6889 = FStar_Ident.path_of_text s  in
           FStar_TypeChecker_Env.rem_proof_ns ctx uu____6889  in
         let g' = FStar_Tactics_Types.goal_with_env g ctx'  in
         bind __dismiss (fun uu____6892  -> add_goals [g']))
  
let (addns : Prims.string -> unit tac) =
  fun s  ->
    let uu____6902 = cur_goal ()  in
    bind uu____6902
      (fun g  ->
         let ctx = FStar_Tactics_Types.goal_env g  in
         let ctx' =
           let uu____6912 = FStar_Ident.path_of_text s  in
           FStar_TypeChecker_Env.add_proof_ns ctx uu____6912  in
         let g' = FStar_Tactics_Types.goal_with_env g ctx'  in
         bind __dismiss (fun uu____6915  -> add_goals [g']))
  
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
            let uu____6955 = FStar_Syntax_Subst.compress t  in
            uu____6955.FStar_Syntax_Syntax.n  in
          let uu____6958 =
            if d = FStar_Tactics_Types.TopDown
            then
              f env
                (let uu___414_6964 = t  in
                 {
                   FStar_Syntax_Syntax.n = tn;
                   FStar_Syntax_Syntax.pos =
                     (uu___414_6964.FStar_Syntax_Syntax.pos);
                   FStar_Syntax_Syntax.vars =
                     (uu___414_6964.FStar_Syntax_Syntax.vars)
                 })
            else ret t  in
          bind uu____6958
            (fun t1  ->
               let ff = tac_fold_env d f env  in
               let tn1 =
                 let uu____6980 =
                   let uu____6981 = FStar_Syntax_Subst.compress t1  in
                   uu____6981.FStar_Syntax_Syntax.n  in
                 match uu____6980 with
                 | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
                     let uu____7012 = ff hd1  in
                     bind uu____7012
                       (fun hd2  ->
                          let fa uu____7038 =
                            match uu____7038 with
                            | (a,q) ->
                                let uu____7059 = ff a  in
                                bind uu____7059 (fun a1  -> ret (a1, q))
                             in
                          let uu____7078 = mapM fa args  in
                          bind uu____7078
                            (fun args1  ->
                               ret (FStar_Syntax_Syntax.Tm_app (hd2, args1))))
                 | FStar_Syntax_Syntax.Tm_abs (bs,t2,k) ->
                     let uu____7160 = FStar_Syntax_Subst.open_term bs t2  in
                     (match uu____7160 with
                      | (bs1,t') ->
                          let uu____7169 =
                            let uu____7172 =
                              FStar_TypeChecker_Env.push_binders env bs1  in
                            tac_fold_env d f uu____7172 t'  in
                          bind uu____7169
                            (fun t''  ->
                               let uu____7176 =
                                 let uu____7177 =
                                   let uu____7196 =
                                     FStar_Syntax_Subst.close_binders bs1  in
                                   let uu____7205 =
                                     FStar_Syntax_Subst.close bs1 t''  in
                                   (uu____7196, uu____7205, k)  in
                                 FStar_Syntax_Syntax.Tm_abs uu____7177  in
                               ret uu____7176))
                 | FStar_Syntax_Syntax.Tm_arrow (bs,k) -> ret tn
                 | FStar_Syntax_Syntax.Tm_match (hd1,brs) ->
                     let uu____7280 = ff hd1  in
                     bind uu____7280
                       (fun hd2  ->
                          let ffb br =
                            let uu____7295 =
                              FStar_Syntax_Subst.open_branch br  in
                            match uu____7295 with
                            | (pat,w,e) ->
                                let bvs = FStar_Syntax_Syntax.pat_bvs pat  in
                                let ff1 =
                                  let uu____7327 =
                                    FStar_TypeChecker_Env.push_bvs env bvs
                                     in
                                  tac_fold_env d f uu____7327  in
                                let uu____7328 = ff1 e  in
                                bind uu____7328
                                  (fun e1  ->
                                     let br1 =
                                       FStar_Syntax_Subst.close_branch
                                         (pat, w, e1)
                                        in
                                     ret br1)
                             in
                          let uu____7343 = mapM ffb brs  in
                          bind uu____7343
                            (fun brs1  ->
                               ret (FStar_Syntax_Syntax.Tm_match (hd2, brs1))))
                 | FStar_Syntax_Syntax.Tm_let
                     ((false
                       ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inl bv;
                          FStar_Syntax_Syntax.lbunivs = uu____7387;
                          FStar_Syntax_Syntax.lbtyp = uu____7388;
                          FStar_Syntax_Syntax.lbeff = uu____7389;
                          FStar_Syntax_Syntax.lbdef = def;
                          FStar_Syntax_Syntax.lbattrs = uu____7391;
                          FStar_Syntax_Syntax.lbpos = uu____7392;_}::[]),e)
                     ->
                     let lb =
                       let uu____7417 =
                         let uu____7418 = FStar_Syntax_Subst.compress t1  in
                         uu____7418.FStar_Syntax_Syntax.n  in
                       match uu____7417 with
                       | FStar_Syntax_Syntax.Tm_let
                           ((false ,lb::[]),uu____7422) -> lb
                       | uu____7435 -> failwith "impossible"  in
                     let fflb lb1 =
                       let uu____7444 = ff lb1.FStar_Syntax_Syntax.lbdef  in
                       bind uu____7444
                         (fun def1  ->
                            ret
                              (let uu___411_7450 = lb1  in
                               {
                                 FStar_Syntax_Syntax.lbname =
                                   (uu___411_7450.FStar_Syntax_Syntax.lbname);
                                 FStar_Syntax_Syntax.lbunivs =
                                   (uu___411_7450.FStar_Syntax_Syntax.lbunivs);
                                 FStar_Syntax_Syntax.lbtyp =
                                   (uu___411_7450.FStar_Syntax_Syntax.lbtyp);
                                 FStar_Syntax_Syntax.lbeff =
                                   (uu___411_7450.FStar_Syntax_Syntax.lbeff);
                                 FStar_Syntax_Syntax.lbdef = def1;
                                 FStar_Syntax_Syntax.lbattrs =
                                   (uu___411_7450.FStar_Syntax_Syntax.lbattrs);
                                 FStar_Syntax_Syntax.lbpos =
                                   (uu___411_7450.FStar_Syntax_Syntax.lbpos)
                               }))
                        in
                     let uu____7451 = fflb lb  in
                     bind uu____7451
                       (fun lb1  ->
                          let uu____7461 =
                            let uu____7466 =
                              let uu____7467 =
                                FStar_Syntax_Syntax.mk_binder bv  in
                              [uu____7467]  in
                            FStar_Syntax_Subst.open_term uu____7466 e  in
                          match uu____7461 with
                          | (bs,e1) ->
                              let ff1 =
                                let uu____7497 =
                                  FStar_TypeChecker_Env.push_binders env bs
                                   in
                                tac_fold_env d f uu____7497  in
                              let uu____7498 = ff1 e1  in
                              bind uu____7498
                                (fun e2  ->
                                   let e3 = FStar_Syntax_Subst.close bs e2
                                      in
                                   ret
                                     (FStar_Syntax_Syntax.Tm_let
                                        ((false, [lb1]), e3))))
                 | FStar_Syntax_Syntax.Tm_let ((true ,lbs),e) ->
                     let fflb lb =
                       let uu____7539 = ff lb.FStar_Syntax_Syntax.lbdef  in
                       bind uu____7539
                         (fun def  ->
                            ret
                              (let uu___412_7545 = lb  in
                               {
                                 FStar_Syntax_Syntax.lbname =
                                   (uu___412_7545.FStar_Syntax_Syntax.lbname);
                                 FStar_Syntax_Syntax.lbunivs =
                                   (uu___412_7545.FStar_Syntax_Syntax.lbunivs);
                                 FStar_Syntax_Syntax.lbtyp =
                                   (uu___412_7545.FStar_Syntax_Syntax.lbtyp);
                                 FStar_Syntax_Syntax.lbeff =
                                   (uu___412_7545.FStar_Syntax_Syntax.lbeff);
                                 FStar_Syntax_Syntax.lbdef = def;
                                 FStar_Syntax_Syntax.lbattrs =
                                   (uu___412_7545.FStar_Syntax_Syntax.lbattrs);
                                 FStar_Syntax_Syntax.lbpos =
                                   (uu___412_7545.FStar_Syntax_Syntax.lbpos)
                               }))
                        in
                     let uu____7546 = FStar_Syntax_Subst.open_let_rec lbs e
                        in
                     (match uu____7546 with
                      | (lbs1,e1) ->
                          let uu____7561 = mapM fflb lbs1  in
                          bind uu____7561
                            (fun lbs2  ->
                               let uu____7573 = ff e1  in
                               bind uu____7573
                                 (fun e2  ->
                                    let uu____7581 =
                                      FStar_Syntax_Subst.close_let_rec lbs2
                                        e2
                                       in
                                    match uu____7581 with
                                    | (lbs3,e3) ->
                                        ret
                                          (FStar_Syntax_Syntax.Tm_let
                                             ((true, lbs3), e3)))))
                 | FStar_Syntax_Syntax.Tm_ascribed (t2,asc,eff) ->
                     let uu____7649 = ff t2  in
                     bind uu____7649
                       (fun t3  ->
                          ret
                            (FStar_Syntax_Syntax.Tm_ascribed (t3, asc, eff)))
                 | FStar_Syntax_Syntax.Tm_meta (t2,m) ->
                     let uu____7680 = ff t2  in
                     bind uu____7680
                       (fun t3  -> ret (FStar_Syntax_Syntax.Tm_meta (t3, m)))
                 | uu____7687 -> ret tn  in
               bind tn1
                 (fun tn2  ->
                    let t' =
                      let uu___413_7694 = t1  in
                      {
                        FStar_Syntax_Syntax.n = tn2;
                        FStar_Syntax_Syntax.pos =
                          (uu___413_7694.FStar_Syntax_Syntax.pos);
                        FStar_Syntax_Syntax.vars =
                          (uu___413_7694.FStar_Syntax_Syntax.vars)
                      }  in
                    if d = FStar_Tactics_Types.BottomUp
                    then f env t'
                    else ret t'))
  
let (pointwise_rec :
  FStar_Tactics_Types.proofstate ->
    unit tac ->
      FStar_Options.optionstate ->
        Prims.string ->
          FStar_TypeChecker_Env.env ->
            FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term tac)
  =
  fun ps  ->
    fun tau  ->
      fun opts  ->
        fun label1  ->
          fun env  ->
            fun t  ->
              let uu____7736 =
                FStar_TypeChecker_TcTerm.tc_term
                  (let uu___415_7745 = env  in
                   {
                     FStar_TypeChecker_Env.solver =
                       (uu___415_7745.FStar_TypeChecker_Env.solver);
                     FStar_TypeChecker_Env.range =
                       (uu___415_7745.FStar_TypeChecker_Env.range);
                     FStar_TypeChecker_Env.curmodule =
                       (uu___415_7745.FStar_TypeChecker_Env.curmodule);
                     FStar_TypeChecker_Env.gamma =
                       (uu___415_7745.FStar_TypeChecker_Env.gamma);
                     FStar_TypeChecker_Env.gamma_sig =
                       (uu___415_7745.FStar_TypeChecker_Env.gamma_sig);
                     FStar_TypeChecker_Env.gamma_cache =
                       (uu___415_7745.FStar_TypeChecker_Env.gamma_cache);
                     FStar_TypeChecker_Env.modules =
                       (uu___415_7745.FStar_TypeChecker_Env.modules);
                     FStar_TypeChecker_Env.expected_typ =
                       (uu___415_7745.FStar_TypeChecker_Env.expected_typ);
                     FStar_TypeChecker_Env.sigtab =
                       (uu___415_7745.FStar_TypeChecker_Env.sigtab);
                     FStar_TypeChecker_Env.attrtab =
                       (uu___415_7745.FStar_TypeChecker_Env.attrtab);
                     FStar_TypeChecker_Env.is_pattern =
                       (uu___415_7745.FStar_TypeChecker_Env.is_pattern);
                     FStar_TypeChecker_Env.instantiate_imp =
                       (uu___415_7745.FStar_TypeChecker_Env.instantiate_imp);
                     FStar_TypeChecker_Env.effects =
                       (uu___415_7745.FStar_TypeChecker_Env.effects);
                     FStar_TypeChecker_Env.generalize =
                       (uu___415_7745.FStar_TypeChecker_Env.generalize);
                     FStar_TypeChecker_Env.letrecs =
                       (uu___415_7745.FStar_TypeChecker_Env.letrecs);
                     FStar_TypeChecker_Env.top_level =
                       (uu___415_7745.FStar_TypeChecker_Env.top_level);
                     FStar_TypeChecker_Env.check_uvars =
                       (uu___415_7745.FStar_TypeChecker_Env.check_uvars);
                     FStar_TypeChecker_Env.use_eq =
                       (uu___415_7745.FStar_TypeChecker_Env.use_eq);
                     FStar_TypeChecker_Env.is_iface =
                       (uu___415_7745.FStar_TypeChecker_Env.is_iface);
                     FStar_TypeChecker_Env.admit =
                       (uu___415_7745.FStar_TypeChecker_Env.admit);
                     FStar_TypeChecker_Env.lax = true;
                     FStar_TypeChecker_Env.lax_universes =
                       (uu___415_7745.FStar_TypeChecker_Env.lax_universes);
                     FStar_TypeChecker_Env.phase1 =
                       (uu___415_7745.FStar_TypeChecker_Env.phase1);
                     FStar_TypeChecker_Env.failhard =
                       (uu___415_7745.FStar_TypeChecker_Env.failhard);
                     FStar_TypeChecker_Env.nosynth =
                       (uu___415_7745.FStar_TypeChecker_Env.nosynth);
                     FStar_TypeChecker_Env.uvar_subtyping =
                       (uu___415_7745.FStar_TypeChecker_Env.uvar_subtyping);
                     FStar_TypeChecker_Env.tc_term =
                       (uu___415_7745.FStar_TypeChecker_Env.tc_term);
                     FStar_TypeChecker_Env.type_of =
                       (uu___415_7745.FStar_TypeChecker_Env.type_of);
                     FStar_TypeChecker_Env.universe_of =
                       (uu___415_7745.FStar_TypeChecker_Env.universe_of);
                     FStar_TypeChecker_Env.check_type_of =
                       (uu___415_7745.FStar_TypeChecker_Env.check_type_of);
                     FStar_TypeChecker_Env.use_bv_sorts =
                       (uu___415_7745.FStar_TypeChecker_Env.use_bv_sorts);
                     FStar_TypeChecker_Env.qtbl_name_and_index =
                       (uu___415_7745.FStar_TypeChecker_Env.qtbl_name_and_index);
                     FStar_TypeChecker_Env.normalized_eff_names =
                       (uu___415_7745.FStar_TypeChecker_Env.normalized_eff_names);
                     FStar_TypeChecker_Env.fv_delta_depths =
                       (uu___415_7745.FStar_TypeChecker_Env.fv_delta_depths);
                     FStar_TypeChecker_Env.proof_ns =
                       (uu___415_7745.FStar_TypeChecker_Env.proof_ns);
                     FStar_TypeChecker_Env.synth_hook =
                       (uu___415_7745.FStar_TypeChecker_Env.synth_hook);
                     FStar_TypeChecker_Env.splice =
                       (uu___415_7745.FStar_TypeChecker_Env.splice);
                     FStar_TypeChecker_Env.postprocess =
                       (uu___415_7745.FStar_TypeChecker_Env.postprocess);
                     FStar_TypeChecker_Env.is_native_tactic =
                       (uu___415_7745.FStar_TypeChecker_Env.is_native_tactic);
                     FStar_TypeChecker_Env.identifier_info =
                       (uu___415_7745.FStar_TypeChecker_Env.identifier_info);
                     FStar_TypeChecker_Env.tc_hooks =
                       (uu___415_7745.FStar_TypeChecker_Env.tc_hooks);
                     FStar_TypeChecker_Env.dsenv =
                       (uu___415_7745.FStar_TypeChecker_Env.dsenv);
                     FStar_TypeChecker_Env.nbe =
                       (uu___415_7745.FStar_TypeChecker_Env.nbe)
                   }) t
                 in
              match uu____7736 with
              | (t1,lcomp,g) ->
                  let uu____7751 =
                    (let uu____7754 =
                       FStar_Syntax_Util.is_pure_or_ghost_lcomp lcomp  in
                     Prims.op_Negation uu____7754) ||
                      (let uu____7756 = FStar_TypeChecker_Env.is_trivial g
                          in
                       Prims.op_Negation uu____7756)
                     in
                  if uu____7751
                  then ret t1
                  else
                    (let rewrite_eq =
                       let typ = lcomp.FStar_Syntax_Syntax.res_typ  in
                       let uu____7764 = new_uvar "pointwise_rec" env typ  in
                       bind uu____7764
                         (fun uu____7780  ->
                            match uu____7780 with
                            | (ut,uvar_ut) ->
                                (log ps
                                   (fun uu____7793  ->
                                      let uu____7794 =
                                        FStar_Syntax_Print.term_to_string t1
                                         in
                                      let uu____7795 =
                                        FStar_Syntax_Print.term_to_string ut
                                         in
                                      FStar_Util.print2
                                        "Pointwise_rec: making equality\n\t%s ==\n\t%s\n"
                                        uu____7794 uu____7795);
                                 (let uu____7796 =
                                    let uu____7799 =
                                      let uu____7800 =
                                        FStar_TypeChecker_TcTerm.universe_of
                                          env typ
                                         in
                                      FStar_Syntax_Util.mk_eq2 uu____7800 typ
                                        t1 ut
                                       in
                                    add_irrelevant_goal
                                      "pointwise_rec equation" env uu____7799
                                      opts label1
                                     in
                                  bind uu____7796
                                    (fun uu____7803  ->
                                       let uu____7804 =
                                         bind tau
                                           (fun uu____7810  ->
                                              let ut1 =
                                                FStar_TypeChecker_Normalize.reduce_uvar_solutions
                                                  env ut
                                                 in
                                              log ps
                                                (fun uu____7816  ->
                                                   let uu____7817 =
                                                     FStar_Syntax_Print.term_to_string
                                                       t1
                                                      in
                                                   let uu____7818 =
                                                     FStar_Syntax_Print.term_to_string
                                                       ut1
                                                      in
                                                   FStar_Util.print2
                                                     "Pointwise_rec: succeeded rewriting\n\t%s to\n\t%s\n"
                                                     uu____7817 uu____7818);
                                              ret ut1)
                                          in
                                       focus uu____7804))))
                        in
                     let uu____7819 = catch rewrite_eq  in
                     bind uu____7819
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
          let uu____8017 = FStar_Syntax_Subst.compress t  in
          maybe_continue ctrl uu____8017
            (fun t1  ->
               let uu____8025 =
                 f env
                   (let uu___418_8034 = t1  in
                    {
                      FStar_Syntax_Syntax.n = (t1.FStar_Syntax_Syntax.n);
                      FStar_Syntax_Syntax.pos =
                        (uu___418_8034.FStar_Syntax_Syntax.pos);
                      FStar_Syntax_Syntax.vars =
                        (uu___418_8034.FStar_Syntax_Syntax.vars)
                    })
                  in
               bind uu____8025
                 (fun uu____8050  ->
                    match uu____8050 with
                    | (t2,ctrl1) ->
                        maybe_continue ctrl1 t2
                          (fun t3  ->
                             let uu____8073 =
                               let uu____8074 =
                                 FStar_Syntax_Subst.compress t3  in
                               uu____8074.FStar_Syntax_Syntax.n  in
                             match uu____8073 with
                             | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
                                 let uu____8111 =
                                   ctrl_tac_fold f env ctrl1 hd1  in
                                 bind uu____8111
                                   (fun uu____8136  ->
                                      match uu____8136 with
                                      | (hd2,ctrl2) ->
                                          let ctrl3 = keep_going ctrl2  in
                                          let uu____8152 =
                                            ctrl_tac_fold_args f env ctrl3
                                              args
                                             in
                                          bind uu____8152
                                            (fun uu____8179  ->
                                               match uu____8179 with
                                               | (args1,ctrl4) ->
                                                   ret
                                                     ((let uu___416_8209 = t3
                                                          in
                                                       {
                                                         FStar_Syntax_Syntax.n
                                                           =
                                                           (FStar_Syntax_Syntax.Tm_app
                                                              (hd2, args1));
                                                         FStar_Syntax_Syntax.pos
                                                           =
                                                           (uu___416_8209.FStar_Syntax_Syntax.pos);
                                                         FStar_Syntax_Syntax.vars
                                                           =
                                                           (uu___416_8209.FStar_Syntax_Syntax.vars)
                                                       }), ctrl4)))
                             | FStar_Syntax_Syntax.Tm_abs (bs,t4,k) ->
                                 let uu____8251 =
                                   FStar_Syntax_Subst.open_term bs t4  in
                                 (match uu____8251 with
                                  | (bs1,t') ->
                                      let uu____8266 =
                                        let uu____8273 =
                                          FStar_TypeChecker_Env.push_binders
                                            env bs1
                                           in
                                        ctrl_tac_fold f uu____8273 ctrl1 t'
                                         in
                                      bind uu____8266
                                        (fun uu____8291  ->
                                           match uu____8291 with
                                           | (t'',ctrl2) ->
                                               let uu____8306 =
                                                 let uu____8313 =
                                                   let uu___417_8316 = t4  in
                                                   let uu____8319 =
                                                     let uu____8320 =
                                                       let uu____8339 =
                                                         FStar_Syntax_Subst.close_binders
                                                           bs1
                                                          in
                                                       let uu____8348 =
                                                         FStar_Syntax_Subst.close
                                                           bs1 t''
                                                          in
                                                       (uu____8339,
                                                         uu____8348, k)
                                                        in
                                                     FStar_Syntax_Syntax.Tm_abs
                                                       uu____8320
                                                      in
                                                   {
                                                     FStar_Syntax_Syntax.n =
                                                       uu____8319;
                                                     FStar_Syntax_Syntax.pos
                                                       =
                                                       (uu___417_8316.FStar_Syntax_Syntax.pos);
                                                     FStar_Syntax_Syntax.vars
                                                       =
                                                       (uu___417_8316.FStar_Syntax_Syntax.vars)
                                                   }  in
                                                 (uu____8313, ctrl2)  in
                                               ret uu____8306))
                             | FStar_Syntax_Syntax.Tm_arrow (bs,k) ->
                                 ret (t3, ctrl1)
                             | uu____8401 -> ret (t3, ctrl1))))

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
              let uu____8448 = ctrl_tac_fold f env ctrl t  in
              bind uu____8448
                (fun uu____8472  ->
                   match uu____8472 with
                   | (t1,ctrl1) ->
                       let uu____8487 = ctrl_tac_fold_args f env ctrl1 ts1
                          in
                       bind uu____8487
                         (fun uu____8514  ->
                            match uu____8514 with
                            | (ts2,ctrl2) -> ret (((t1, q) :: ts2), ctrl2)))

let (rewrite_rec :
  FStar_Tactics_Types.proofstate ->
    (FStar_Syntax_Syntax.term -> rewrite_result ctrl_tac) ->
      unit tac ->
        FStar_Options.optionstate ->
          Prims.string ->
            FStar_TypeChecker_Env.env ->
              FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term ctrl_tac)
  =
  fun ps  ->
    fun ctrl  ->
      fun rewriter  ->
        fun opts  ->
          fun label1  ->
            fun env  ->
              fun t  ->
                let t1 = FStar_Syntax_Subst.compress t  in
                let uu____8603 =
                  let uu____8610 =
                    add_irrelevant_goal "dummy" env FStar_Syntax_Util.t_true
                      opts label1
                     in
                  bind uu____8610
                    (fun uu____8619  ->
                       let uu____8620 = ctrl t1  in
                       bind uu____8620
                         (fun res  ->
                            let uu____8643 = trivial ()  in
                            bind uu____8643 (fun uu____8651  -> ret res)))
                   in
                bind uu____8603
                  (fun uu____8667  ->
                     match uu____8667 with
                     | (should_rewrite,ctrl1) ->
                         if Prims.op_Negation should_rewrite
                         then ret (t1, ctrl1)
                         else
                           (let uu____8691 =
                              FStar_TypeChecker_TcTerm.tc_term
                                (let uu___419_8700 = env  in
                                 {
                                   FStar_TypeChecker_Env.solver =
                                     (uu___419_8700.FStar_TypeChecker_Env.solver);
                                   FStar_TypeChecker_Env.range =
                                     (uu___419_8700.FStar_TypeChecker_Env.range);
                                   FStar_TypeChecker_Env.curmodule =
                                     (uu___419_8700.FStar_TypeChecker_Env.curmodule);
                                   FStar_TypeChecker_Env.gamma =
                                     (uu___419_8700.FStar_TypeChecker_Env.gamma);
                                   FStar_TypeChecker_Env.gamma_sig =
                                     (uu___419_8700.FStar_TypeChecker_Env.gamma_sig);
                                   FStar_TypeChecker_Env.gamma_cache =
                                     (uu___419_8700.FStar_TypeChecker_Env.gamma_cache);
                                   FStar_TypeChecker_Env.modules =
                                     (uu___419_8700.FStar_TypeChecker_Env.modules);
                                   FStar_TypeChecker_Env.expected_typ =
                                     (uu___419_8700.FStar_TypeChecker_Env.expected_typ);
                                   FStar_TypeChecker_Env.sigtab =
                                     (uu___419_8700.FStar_TypeChecker_Env.sigtab);
                                   FStar_TypeChecker_Env.attrtab =
                                     (uu___419_8700.FStar_TypeChecker_Env.attrtab);
                                   FStar_TypeChecker_Env.is_pattern =
                                     (uu___419_8700.FStar_TypeChecker_Env.is_pattern);
                                   FStar_TypeChecker_Env.instantiate_imp =
                                     (uu___419_8700.FStar_TypeChecker_Env.instantiate_imp);
                                   FStar_TypeChecker_Env.effects =
                                     (uu___419_8700.FStar_TypeChecker_Env.effects);
                                   FStar_TypeChecker_Env.generalize =
                                     (uu___419_8700.FStar_TypeChecker_Env.generalize);
                                   FStar_TypeChecker_Env.letrecs =
                                     (uu___419_8700.FStar_TypeChecker_Env.letrecs);
                                   FStar_TypeChecker_Env.top_level =
                                     (uu___419_8700.FStar_TypeChecker_Env.top_level);
                                   FStar_TypeChecker_Env.check_uvars =
                                     (uu___419_8700.FStar_TypeChecker_Env.check_uvars);
                                   FStar_TypeChecker_Env.use_eq =
                                     (uu___419_8700.FStar_TypeChecker_Env.use_eq);
                                   FStar_TypeChecker_Env.is_iface =
                                     (uu___419_8700.FStar_TypeChecker_Env.is_iface);
                                   FStar_TypeChecker_Env.admit =
                                     (uu___419_8700.FStar_TypeChecker_Env.admit);
                                   FStar_TypeChecker_Env.lax = true;
                                   FStar_TypeChecker_Env.lax_universes =
                                     (uu___419_8700.FStar_TypeChecker_Env.lax_universes);
                                   FStar_TypeChecker_Env.phase1 =
                                     (uu___419_8700.FStar_TypeChecker_Env.phase1);
                                   FStar_TypeChecker_Env.failhard =
                                     (uu___419_8700.FStar_TypeChecker_Env.failhard);
                                   FStar_TypeChecker_Env.nosynth =
                                     (uu___419_8700.FStar_TypeChecker_Env.nosynth);
                                   FStar_TypeChecker_Env.uvar_subtyping =
                                     (uu___419_8700.FStar_TypeChecker_Env.uvar_subtyping);
                                   FStar_TypeChecker_Env.tc_term =
                                     (uu___419_8700.FStar_TypeChecker_Env.tc_term);
                                   FStar_TypeChecker_Env.type_of =
                                     (uu___419_8700.FStar_TypeChecker_Env.type_of);
                                   FStar_TypeChecker_Env.universe_of =
                                     (uu___419_8700.FStar_TypeChecker_Env.universe_of);
                                   FStar_TypeChecker_Env.check_type_of =
                                     (uu___419_8700.FStar_TypeChecker_Env.check_type_of);
                                   FStar_TypeChecker_Env.use_bv_sorts =
                                     (uu___419_8700.FStar_TypeChecker_Env.use_bv_sorts);
                                   FStar_TypeChecker_Env.qtbl_name_and_index
                                     =
                                     (uu___419_8700.FStar_TypeChecker_Env.qtbl_name_and_index);
                                   FStar_TypeChecker_Env.normalized_eff_names
                                     =
                                     (uu___419_8700.FStar_TypeChecker_Env.normalized_eff_names);
                                   FStar_TypeChecker_Env.fv_delta_depths =
                                     (uu___419_8700.FStar_TypeChecker_Env.fv_delta_depths);
                                   FStar_TypeChecker_Env.proof_ns =
                                     (uu___419_8700.FStar_TypeChecker_Env.proof_ns);
                                   FStar_TypeChecker_Env.synth_hook =
                                     (uu___419_8700.FStar_TypeChecker_Env.synth_hook);
                                   FStar_TypeChecker_Env.splice =
                                     (uu___419_8700.FStar_TypeChecker_Env.splice);
                                   FStar_TypeChecker_Env.postprocess =
                                     (uu___419_8700.FStar_TypeChecker_Env.postprocess);
                                   FStar_TypeChecker_Env.is_native_tactic =
                                     (uu___419_8700.FStar_TypeChecker_Env.is_native_tactic);
                                   FStar_TypeChecker_Env.identifier_info =
                                     (uu___419_8700.FStar_TypeChecker_Env.identifier_info);
                                   FStar_TypeChecker_Env.tc_hooks =
                                     (uu___419_8700.FStar_TypeChecker_Env.tc_hooks);
                                   FStar_TypeChecker_Env.dsenv =
                                     (uu___419_8700.FStar_TypeChecker_Env.dsenv);
                                   FStar_TypeChecker_Env.nbe =
                                     (uu___419_8700.FStar_TypeChecker_Env.nbe)
                                 }) t1
                               in
                            match uu____8691 with
                            | (t2,lcomp,g) ->
                                let uu____8710 =
                                  (let uu____8713 =
                                     FStar_Syntax_Util.is_pure_or_ghost_lcomp
                                       lcomp
                                      in
                                   Prims.op_Negation uu____8713) ||
                                    (let uu____8715 =
                                       FStar_TypeChecker_Env.is_trivial g  in
                                     Prims.op_Negation uu____8715)
                                   in
                                if uu____8710
                                then ret (t2, globalStop)
                                else
                                  (let typ =
                                     lcomp.FStar_Syntax_Syntax.res_typ  in
                                   let uu____8728 =
                                     new_uvar "pointwise_rec" env typ  in
                                   bind uu____8728
                                     (fun uu____8748  ->
                                        match uu____8748 with
                                        | (ut,uvar_ut) ->
                                            (log ps
                                               (fun uu____8765  ->
                                                  let uu____8766 =
                                                    FStar_Syntax_Print.term_to_string
                                                      t2
                                                     in
                                                  let uu____8767 =
                                                    FStar_Syntax_Print.term_to_string
                                                      ut
                                                     in
                                                  FStar_Util.print2
                                                    "Pointwise_rec: making equality\n\t%s ==\n\t%s\n"
                                                    uu____8766 uu____8767);
                                             (let uu____8768 =
                                                let uu____8771 =
                                                  let uu____8772 =
                                                    FStar_TypeChecker_TcTerm.universe_of
                                                      env typ
                                                     in
                                                  FStar_Syntax_Util.mk_eq2
                                                    uu____8772 typ t2 ut
                                                   in
                                                add_irrelevant_goal
                                                  "rewrite_rec equation" env
                                                  uu____8771 opts label1
                                                 in
                                              bind uu____8768
                                                (fun uu____8779  ->
                                                   let uu____8780 =
                                                     bind rewriter
                                                       (fun uu____8794  ->
                                                          let ut1 =
                                                            FStar_TypeChecker_Normalize.reduce_uvar_solutions
                                                              env ut
                                                             in
                                                          log ps
                                                            (fun uu____8800 
                                                               ->
                                                               let uu____8801
                                                                 =
                                                                 FStar_Syntax_Print.term_to_string
                                                                   t2
                                                                  in
                                                               let uu____8802
                                                                 =
                                                                 FStar_Syntax_Print.term_to_string
                                                                   ut1
                                                                  in
                                                               FStar_Util.print2
                                                                 "rewrite_rec: succeeded rewriting\n\t%s to\n\t%s\n"
                                                                 uu____8801
                                                                 uu____8802);
                                                          ret (ut1, ctrl1))
                                                      in
                                                   focus uu____8780)))))))
  
let (topdown_rewrite :
  (FStar_Syntax_Syntax.term ->
     (Prims.bool,FStar_BigInt.t) FStar_Pervasives_Native.tuple2 tac)
    -> unit tac -> unit tac)
  =
  fun ctrl  ->
    fun rewriter  ->
      let uu____8843 =
        bind get
          (fun ps  ->
             let uu____8853 =
               match ps.FStar_Tactics_Types.goals with
               | g::gs -> (g, gs)
               | [] -> failwith "no goals"  in
             match uu____8853 with
             | (g,gs) ->
                 let gt1 = FStar_Tactics_Types.goal_type g  in
                 (log ps
                    (fun uu____8890  ->
                       let uu____8891 = FStar_Syntax_Print.term_to_string gt1
                          in
                       FStar_Util.print1 "Topdown_rewrite starting with %s\n"
                         uu____8891);
                  bind dismiss_all
                    (fun uu____8894  ->
                       let uu____8895 =
                         let uu____8902 = FStar_Tactics_Types.goal_env g  in
                         ctrl_tac_fold
                           (rewrite_rec ps ctrl rewriter
                              g.FStar_Tactics_Types.opts
                              g.FStar_Tactics_Types.label) uu____8902
                           keepGoing gt1
                          in
                       bind uu____8895
                         (fun uu____8914  ->
                            match uu____8914 with
                            | (gt',uu____8922) ->
                                (log ps
                                   (fun uu____8926  ->
                                      let uu____8927 =
                                        FStar_Syntax_Print.term_to_string gt'
                                         in
                                      FStar_Util.print1
                                        "Topdown_rewrite seems to have succeded with %s\n"
                                        uu____8927);
                                 (let uu____8928 = push_goals gs  in
                                  bind uu____8928
                                    (fun uu____8933  ->
                                       let uu____8934 =
                                         let uu____8937 =
                                           FStar_Tactics_Types.goal_with_type
                                             g gt'
                                            in
                                         [uu____8937]  in
                                       add_goals uu____8934)))))))
         in
      FStar_All.pipe_left (wrap_err "topdown_rewrite") uu____8843
  
let (pointwise : FStar_Tactics_Types.direction -> unit tac -> unit tac) =
  fun d  ->
    fun tau  ->
      let uu____8960 =
        bind get
          (fun ps  ->
             let uu____8970 =
               match ps.FStar_Tactics_Types.goals with
               | g::gs -> (g, gs)
               | [] -> failwith "no goals"  in
             match uu____8970 with
             | (g,gs) ->
                 let gt1 = FStar_Tactics_Types.goal_type g  in
                 (log ps
                    (fun uu____9007  ->
                       let uu____9008 = FStar_Syntax_Print.term_to_string gt1
                          in
                       FStar_Util.print1 "Pointwise starting with %s\n"
                         uu____9008);
                  bind dismiss_all
                    (fun uu____9011  ->
                       let uu____9012 =
                         let uu____9015 = FStar_Tactics_Types.goal_env g  in
                         tac_fold_env d
                           (pointwise_rec ps tau g.FStar_Tactics_Types.opts
                              g.FStar_Tactics_Types.label) uu____9015 gt1
                          in
                       bind uu____9012
                         (fun gt'  ->
                            log ps
                              (fun uu____9023  ->
                                 let uu____9024 =
                                   FStar_Syntax_Print.term_to_string gt'  in
                                 FStar_Util.print1
                                   "Pointwise seems to have succeded with %s\n"
                                   uu____9024);
                            (let uu____9025 = push_goals gs  in
                             bind uu____9025
                               (fun uu____9030  ->
                                  let uu____9031 =
                                    let uu____9034 =
                                      FStar_Tactics_Types.goal_with_type g
                                        gt'
                                       in
                                    [uu____9034]  in
                                  add_goals uu____9031))))))
         in
      FStar_All.pipe_left (wrap_err "pointwise") uu____8960
  
let (trefl : unit -> unit tac) =
  fun uu____9045  ->
    let uu____9048 =
      let uu____9051 = cur_goal ()  in
      bind uu____9051
        (fun g  ->
           let uu____9069 =
             let uu____9074 = FStar_Tactics_Types.goal_type g  in
             FStar_Syntax_Util.un_squash uu____9074  in
           match uu____9069 with
           | FStar_Pervasives_Native.Some t ->
               let uu____9082 = FStar_Syntax_Util.head_and_args' t  in
               (match uu____9082 with
                | (hd1,args) ->
                    let uu____9121 =
                      let uu____9134 =
                        let uu____9135 = FStar_Syntax_Util.un_uinst hd1  in
                        uu____9135.FStar_Syntax_Syntax.n  in
                      (uu____9134, args)  in
                    (match uu____9121 with
                     | (FStar_Syntax_Syntax.Tm_fvar
                        fv,uu____9149::(l,uu____9151)::(r,uu____9153)::[])
                         when
                         FStar_Syntax_Syntax.fv_eq_lid fv
                           FStar_Parser_Const.eq2_lid
                         ->
                         let uu____9200 =
                           let uu____9203 = FStar_Tactics_Types.goal_env g
                              in
                           do_unify uu____9203 l r  in
                         bind uu____9200
                           (fun b  ->
                              if b
                              then solve' g FStar_Syntax_Util.exp_unit
                              else
                                (let l1 =
                                   let uu____9210 =
                                     FStar_Tactics_Types.goal_env g  in
                                   FStar_TypeChecker_Normalize.normalize
                                     [FStar_TypeChecker_Env.UnfoldUntil
                                        FStar_Syntax_Syntax.delta_constant;
                                     FStar_TypeChecker_Env.Primops;
                                     FStar_TypeChecker_Env.UnfoldTac]
                                     uu____9210 l
                                    in
                                 let r1 =
                                   let uu____9212 =
                                     FStar_Tactics_Types.goal_env g  in
                                   FStar_TypeChecker_Normalize.normalize
                                     [FStar_TypeChecker_Env.UnfoldUntil
                                        FStar_Syntax_Syntax.delta_constant;
                                     FStar_TypeChecker_Env.Primops;
                                     FStar_TypeChecker_Env.UnfoldTac]
                                     uu____9212 r
                                    in
                                 let uu____9213 =
                                   let uu____9216 =
                                     FStar_Tactics_Types.goal_env g  in
                                   do_unify uu____9216 l1 r1  in
                                 bind uu____9213
                                   (fun b1  ->
                                      if b1
                                      then
                                        solve' g FStar_Syntax_Util.exp_unit
                                      else
                                        (let uu____9222 =
                                           let uu____9223 =
                                             FStar_Tactics_Types.goal_env g
                                              in
                                           tts uu____9223 l1  in
                                         let uu____9224 =
                                           let uu____9225 =
                                             FStar_Tactics_Types.goal_env g
                                              in
                                           tts uu____9225 r1  in
                                         fail2
                                           "not a trivial equality ((%s) vs (%s))"
                                           uu____9222 uu____9224))))
                     | (hd2,uu____9227) ->
                         let uu____9244 =
                           let uu____9245 = FStar_Tactics_Types.goal_env g
                              in
                           tts uu____9245 t  in
                         fail1 "trefl: not an equality (%s)" uu____9244))
           | FStar_Pervasives_Native.None  -> fail "not an irrelevant goal")
       in
    FStar_All.pipe_left (wrap_err "trefl") uu____9048
  
let (dup : unit -> unit tac) =
  fun uu____9258  ->
    let uu____9261 = cur_goal ()  in
    bind uu____9261
      (fun g  ->
         let uu____9267 =
           let uu____9274 = FStar_Tactics_Types.goal_env g  in
           let uu____9275 = FStar_Tactics_Types.goal_type g  in
           new_uvar "dup" uu____9274 uu____9275  in
         bind uu____9267
           (fun uu____9284  ->
              match uu____9284 with
              | (u,u_uvar) ->
                  let g' =
                    let uu___420_9294 = g  in
                    {
                      FStar_Tactics_Types.goal_main_env =
                        (uu___420_9294.FStar_Tactics_Types.goal_main_env);
                      FStar_Tactics_Types.goal_ctx_uvar = u_uvar;
                      FStar_Tactics_Types.opts =
                        (uu___420_9294.FStar_Tactics_Types.opts);
                      FStar_Tactics_Types.is_guard =
                        (uu___420_9294.FStar_Tactics_Types.is_guard);
                      FStar_Tactics_Types.label =
                        (uu___420_9294.FStar_Tactics_Types.label)
                    }  in
                  bind __dismiss
                    (fun uu____9297  ->
                       let uu____9298 =
                         let uu____9301 = FStar_Tactics_Types.goal_env g  in
                         let uu____9302 =
                           let uu____9303 =
                             let uu____9304 = FStar_Tactics_Types.goal_env g
                                in
                             let uu____9305 = FStar_Tactics_Types.goal_type g
                                in
                             FStar_TypeChecker_TcTerm.universe_of uu____9304
                               uu____9305
                              in
                           let uu____9306 = FStar_Tactics_Types.goal_type g
                              in
                           let uu____9307 =
                             FStar_Tactics_Types.goal_witness g  in
                           FStar_Syntax_Util.mk_eq2 uu____9303 uu____9306 u
                             uu____9307
                            in
                         add_irrelevant_goal "dup equation" uu____9301
                           uu____9302 g.FStar_Tactics_Types.opts
                           g.FStar_Tactics_Types.label
                          in
                       bind uu____9298
                         (fun uu____9310  ->
                            let uu____9311 = add_goals [g']  in
                            bind uu____9311 (fun uu____9315  -> ret ())))))
  
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
              let uu____9438 = f x y  in
              if uu____9438 then aux (x :: acc) xs ys else (acc, xs, ys)
          | uu____9458 -> (acc, l11, l21)  in
        let uu____9473 = aux [] l1 l2  in
        match uu____9473 with | (pr,t1,t2) -> ((FStar_List.rev pr), t1, t2)
  
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
      let uu____9578 = get_phi g1  in
      match uu____9578 with
      | FStar_Pervasives_Native.None  -> fail "goal 1 is not irrelevant"
      | FStar_Pervasives_Native.Some phi1 ->
          let uu____9584 = get_phi g2  in
          (match uu____9584 with
           | FStar_Pervasives_Native.None  -> fail "goal 2 is not irrelevant"
           | FStar_Pervasives_Native.Some phi2 ->
               let gamma1 =
                 (g1.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_gamma
                  in
               let gamma2 =
                 (g2.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_gamma
                  in
               let uu____9596 =
                 longest_prefix FStar_Syntax_Syntax.eq_binding
                   (FStar_List.rev gamma1) (FStar_List.rev gamma2)
                  in
               (match uu____9596 with
                | (gamma,r1,r2) ->
                    let t1 =
                      let uu____9627 =
                        FStar_TypeChecker_Env.binders_of_bindings
                          (FStar_List.rev r1)
                         in
                      close_forall_no_univs1 uu____9627 phi1  in
                    let t2 =
                      let uu____9637 =
                        FStar_TypeChecker_Env.binders_of_bindings
                          (FStar_List.rev r2)
                         in
                      close_forall_no_univs1 uu____9637 phi2  in
                    let uu____9646 =
                      set_solution g1 FStar_Syntax_Util.exp_unit  in
                    bind uu____9646
                      (fun uu____9651  ->
                         let uu____9652 =
                           set_solution g2 FStar_Syntax_Util.exp_unit  in
                         bind uu____9652
                           (fun uu____9659  ->
                              let ng = FStar_Syntax_Util.mk_conj t1 t2  in
                              let nenv =
                                let uu___421_9664 =
                                  FStar_Tactics_Types.goal_env g1  in
                                let uu____9665 =
                                  FStar_Util.smap_create
                                    (Prims.parse_int "100")
                                   in
                                {
                                  FStar_TypeChecker_Env.solver =
                                    (uu___421_9664.FStar_TypeChecker_Env.solver);
                                  FStar_TypeChecker_Env.range =
                                    (uu___421_9664.FStar_TypeChecker_Env.range);
                                  FStar_TypeChecker_Env.curmodule =
                                    (uu___421_9664.FStar_TypeChecker_Env.curmodule);
                                  FStar_TypeChecker_Env.gamma =
                                    (FStar_List.rev gamma);
                                  FStar_TypeChecker_Env.gamma_sig =
                                    (uu___421_9664.FStar_TypeChecker_Env.gamma_sig);
                                  FStar_TypeChecker_Env.gamma_cache =
                                    uu____9665;
                                  FStar_TypeChecker_Env.modules =
                                    (uu___421_9664.FStar_TypeChecker_Env.modules);
                                  FStar_TypeChecker_Env.expected_typ =
                                    (uu___421_9664.FStar_TypeChecker_Env.expected_typ);
                                  FStar_TypeChecker_Env.sigtab =
                                    (uu___421_9664.FStar_TypeChecker_Env.sigtab);
                                  FStar_TypeChecker_Env.attrtab =
                                    (uu___421_9664.FStar_TypeChecker_Env.attrtab);
                                  FStar_TypeChecker_Env.is_pattern =
                                    (uu___421_9664.FStar_TypeChecker_Env.is_pattern);
                                  FStar_TypeChecker_Env.instantiate_imp =
                                    (uu___421_9664.FStar_TypeChecker_Env.instantiate_imp);
                                  FStar_TypeChecker_Env.effects =
                                    (uu___421_9664.FStar_TypeChecker_Env.effects);
                                  FStar_TypeChecker_Env.generalize =
                                    (uu___421_9664.FStar_TypeChecker_Env.generalize);
                                  FStar_TypeChecker_Env.letrecs =
                                    (uu___421_9664.FStar_TypeChecker_Env.letrecs);
                                  FStar_TypeChecker_Env.top_level =
                                    (uu___421_9664.FStar_TypeChecker_Env.top_level);
                                  FStar_TypeChecker_Env.check_uvars =
                                    (uu___421_9664.FStar_TypeChecker_Env.check_uvars);
                                  FStar_TypeChecker_Env.use_eq =
                                    (uu___421_9664.FStar_TypeChecker_Env.use_eq);
                                  FStar_TypeChecker_Env.is_iface =
                                    (uu___421_9664.FStar_TypeChecker_Env.is_iface);
                                  FStar_TypeChecker_Env.admit =
                                    (uu___421_9664.FStar_TypeChecker_Env.admit);
                                  FStar_TypeChecker_Env.lax =
                                    (uu___421_9664.FStar_TypeChecker_Env.lax);
                                  FStar_TypeChecker_Env.lax_universes =
                                    (uu___421_9664.FStar_TypeChecker_Env.lax_universes);
                                  FStar_TypeChecker_Env.phase1 =
                                    (uu___421_9664.FStar_TypeChecker_Env.phase1);
                                  FStar_TypeChecker_Env.failhard =
                                    (uu___421_9664.FStar_TypeChecker_Env.failhard);
                                  FStar_TypeChecker_Env.nosynth =
                                    (uu___421_9664.FStar_TypeChecker_Env.nosynth);
                                  FStar_TypeChecker_Env.uvar_subtyping =
                                    (uu___421_9664.FStar_TypeChecker_Env.uvar_subtyping);
                                  FStar_TypeChecker_Env.tc_term =
                                    (uu___421_9664.FStar_TypeChecker_Env.tc_term);
                                  FStar_TypeChecker_Env.type_of =
                                    (uu___421_9664.FStar_TypeChecker_Env.type_of);
                                  FStar_TypeChecker_Env.universe_of =
                                    (uu___421_9664.FStar_TypeChecker_Env.universe_of);
                                  FStar_TypeChecker_Env.check_type_of =
                                    (uu___421_9664.FStar_TypeChecker_Env.check_type_of);
                                  FStar_TypeChecker_Env.use_bv_sorts =
                                    (uu___421_9664.FStar_TypeChecker_Env.use_bv_sorts);
                                  FStar_TypeChecker_Env.qtbl_name_and_index =
                                    (uu___421_9664.FStar_TypeChecker_Env.qtbl_name_and_index);
                                  FStar_TypeChecker_Env.normalized_eff_names
                                    =
                                    (uu___421_9664.FStar_TypeChecker_Env.normalized_eff_names);
                                  FStar_TypeChecker_Env.fv_delta_depths =
                                    (uu___421_9664.FStar_TypeChecker_Env.fv_delta_depths);
                                  FStar_TypeChecker_Env.proof_ns =
                                    (uu___421_9664.FStar_TypeChecker_Env.proof_ns);
                                  FStar_TypeChecker_Env.synth_hook =
                                    (uu___421_9664.FStar_TypeChecker_Env.synth_hook);
                                  FStar_TypeChecker_Env.splice =
                                    (uu___421_9664.FStar_TypeChecker_Env.splice);
                                  FStar_TypeChecker_Env.postprocess =
                                    (uu___421_9664.FStar_TypeChecker_Env.postprocess);
                                  FStar_TypeChecker_Env.is_native_tactic =
                                    (uu___421_9664.FStar_TypeChecker_Env.is_native_tactic);
                                  FStar_TypeChecker_Env.identifier_info =
                                    (uu___421_9664.FStar_TypeChecker_Env.identifier_info);
                                  FStar_TypeChecker_Env.tc_hooks =
                                    (uu___421_9664.FStar_TypeChecker_Env.tc_hooks);
                                  FStar_TypeChecker_Env.dsenv =
                                    (uu___421_9664.FStar_TypeChecker_Env.dsenv);
                                  FStar_TypeChecker_Env.nbe =
                                    (uu___421_9664.FStar_TypeChecker_Env.nbe)
                                }  in
                              let uu____9668 =
                                mk_irrelevant_goal "joined" nenv ng
                                  g1.FStar_Tactics_Types.opts
                                  g1.FStar_Tactics_Types.label
                                 in
                              bind uu____9668
                                (fun goal  ->
                                   mlog
                                     (fun uu____9677  ->
                                        let uu____9678 =
                                          goal_to_string_verbose g1  in
                                        let uu____9679 =
                                          goal_to_string_verbose g2  in
                                        let uu____9680 =
                                          goal_to_string_verbose goal  in
                                        FStar_Util.print3
                                          "join_goals of\n(%s)\nand\n(%s)\n= (%s)\n"
                                          uu____9678 uu____9679 uu____9680)
                                     (fun uu____9682  -> ret goal))))))
  
let (join : unit -> unit tac) =
  fun uu____9689  ->
    bind get
      (fun ps  ->
         match ps.FStar_Tactics_Types.goals with
         | g1::g2::gs ->
             let uu____9705 =
               set
                 (let uu___422_9710 = ps  in
                  {
                    FStar_Tactics_Types.main_context =
                      (uu___422_9710.FStar_Tactics_Types.main_context);
                    FStar_Tactics_Types.main_goal =
                      (uu___422_9710.FStar_Tactics_Types.main_goal);
                    FStar_Tactics_Types.all_implicits =
                      (uu___422_9710.FStar_Tactics_Types.all_implicits);
                    FStar_Tactics_Types.goals = gs;
                    FStar_Tactics_Types.smt_goals =
                      (uu___422_9710.FStar_Tactics_Types.smt_goals);
                    FStar_Tactics_Types.depth =
                      (uu___422_9710.FStar_Tactics_Types.depth);
                    FStar_Tactics_Types.__dump =
                      (uu___422_9710.FStar_Tactics_Types.__dump);
                    FStar_Tactics_Types.psc =
                      (uu___422_9710.FStar_Tactics_Types.psc);
                    FStar_Tactics_Types.entry_range =
                      (uu___422_9710.FStar_Tactics_Types.entry_range);
                    FStar_Tactics_Types.guard_policy =
                      (uu___422_9710.FStar_Tactics_Types.guard_policy);
                    FStar_Tactics_Types.freshness =
                      (uu___422_9710.FStar_Tactics_Types.freshness);
                    FStar_Tactics_Types.tac_verb_dbg =
                      (uu___422_9710.FStar_Tactics_Types.tac_verb_dbg);
                    FStar_Tactics_Types.local_state =
                      (uu___422_9710.FStar_Tactics_Types.local_state)
                  })
                in
             bind uu____9705
               (fun uu____9713  ->
                  let uu____9714 = join_goals g1 g2  in
                  bind uu____9714 (fun g12  -> add_goals [g12]))
         | uu____9719 -> fail "join: less than 2 goals")
  
let (cases :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 tac)
  =
  fun t  ->
    let uu____9739 =
      let uu____9746 = cur_goal ()  in
      bind uu____9746
        (fun g  ->
           let uu____9756 =
             let uu____9765 = FStar_Tactics_Types.goal_env g  in
             __tc uu____9765 t  in
           bind uu____9756
             (fun uu____9793  ->
                match uu____9793 with
                | (t1,typ,guard) ->
                    let uu____9809 = FStar_Syntax_Util.head_and_args typ  in
                    (match uu____9809 with
                     | (hd1,args) ->
                         let uu____9858 =
                           let uu____9873 =
                             let uu____9874 = FStar_Syntax_Util.un_uinst hd1
                                in
                             uu____9874.FStar_Syntax_Syntax.n  in
                           (uu____9873, args)  in
                         (match uu____9858 with
                          | (FStar_Syntax_Syntax.Tm_fvar
                             fv,(p,uu____9895)::(q,uu____9897)::[]) when
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
                                let uu____9951 =
                                  let uu____9952 =
                                    FStar_Tactics_Types.goal_env g  in
                                  FStar_TypeChecker_Env.push_bv uu____9952
                                    v_p
                                   in
                                FStar_Tactics_Types.goal_with_env g
                                  uu____9951
                                 in
                              let g2 =
                                let uu____9954 =
                                  let uu____9955 =
                                    FStar_Tactics_Types.goal_env g  in
                                  FStar_TypeChecker_Env.push_bv uu____9955
                                    v_q
                                   in
                                FStar_Tactics_Types.goal_with_env g
                                  uu____9954
                                 in
                              bind __dismiss
                                (fun uu____9962  ->
                                   let uu____9963 = add_goals [g1; g2]  in
                                   bind uu____9963
                                     (fun uu____9972  ->
                                        let uu____9973 =
                                          let uu____9978 =
                                            FStar_Syntax_Syntax.bv_to_name
                                              v_p
                                             in
                                          let uu____9979 =
                                            FStar_Syntax_Syntax.bv_to_name
                                              v_q
                                             in
                                          (uu____9978, uu____9979)  in
                                        ret uu____9973))
                          | uu____9984 ->
                              let uu____9999 =
                                let uu____10000 =
                                  FStar_Tactics_Types.goal_env g  in
                                tts uu____10000 typ  in
                              fail1 "Not a disjunction: %s" uu____9999))))
       in
    FStar_All.pipe_left (wrap_err "cases") uu____9739
  
let (set_options : Prims.string -> unit tac) =
  fun s  ->
    let uu____10030 =
      let uu____10033 = cur_goal ()  in
      bind uu____10033
        (fun g  ->
           FStar_Options.push ();
           (let uu____10046 = FStar_Util.smap_copy g.FStar_Tactics_Types.opts
               in
            FStar_Options.set uu____10046);
           (let res = FStar_Options.set_options FStar_Options.Set s  in
            let opts' = FStar_Options.peek ()  in
            FStar_Options.pop ();
            (match res with
             | FStar_Getopt.Success  ->
                 let g' =
                   let uu___423_10053 = g  in
                   {
                     FStar_Tactics_Types.goal_main_env =
                       (uu___423_10053.FStar_Tactics_Types.goal_main_env);
                     FStar_Tactics_Types.goal_ctx_uvar =
                       (uu___423_10053.FStar_Tactics_Types.goal_ctx_uvar);
                     FStar_Tactics_Types.opts = opts';
                     FStar_Tactics_Types.is_guard =
                       (uu___423_10053.FStar_Tactics_Types.is_guard);
                     FStar_Tactics_Types.label =
                       (uu___423_10053.FStar_Tactics_Types.label)
                   }  in
                 replace_cur g'
             | FStar_Getopt.Error err ->
                 fail2 "Setting options `%s` failed: %s" s err
             | FStar_Getopt.Help  ->
                 fail1 "Setting options `%s` failed (got `Help`?)" s)))
       in
    FStar_All.pipe_left (wrap_err "set_options") uu____10030
  
let (top_env : unit -> env tac) =
  fun uu____10065  ->
    bind get
      (fun ps  -> FStar_All.pipe_left ret ps.FStar_Tactics_Types.main_context)
  
let (lax_on : unit -> Prims.bool tac) =
  fun uu____10078  ->
    let uu____10081 = cur_goal ()  in
    bind uu____10081
      (fun g  ->
         let uu____10087 =
           (FStar_Options.lax ()) ||
             (let uu____10089 = FStar_Tactics_Types.goal_env g  in
              uu____10089.FStar_TypeChecker_Env.lax)
            in
         ret uu____10087)
  
let (unquote :
  FStar_Reflection_Data.typ ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term tac)
  =
  fun ty  ->
    fun tm  ->
      let uu____10104 =
        mlog
          (fun uu____10109  ->
             let uu____10110 = FStar_Syntax_Print.term_to_string tm  in
             FStar_Util.print1 "unquote: tm = %s\n" uu____10110)
          (fun uu____10113  ->
             let uu____10114 = cur_goal ()  in
             bind uu____10114
               (fun goal  ->
                  let env =
                    let uu____10122 = FStar_Tactics_Types.goal_env goal  in
                    FStar_TypeChecker_Env.set_expected_typ uu____10122 ty  in
                  let uu____10123 = __tc_ghost env tm  in
                  bind uu____10123
                    (fun uu____10142  ->
                       match uu____10142 with
                       | (tm1,typ,guard) ->
                           mlog
                             (fun uu____10156  ->
                                let uu____10157 =
                                  FStar_Syntax_Print.term_to_string tm1  in
                                FStar_Util.print1 "unquote: tm' = %s\n"
                                  uu____10157)
                             (fun uu____10159  ->
                                mlog
                                  (fun uu____10162  ->
                                     let uu____10163 =
                                       FStar_Syntax_Print.term_to_string typ
                                        in
                                     FStar_Util.print1 "unquote: typ = %s\n"
                                       uu____10163)
                                  (fun uu____10166  ->
                                     let uu____10167 =
                                       proc_guard "unquote" env guard  in
                                     bind uu____10167
                                       (fun uu____10171  -> ret tm1))))))
         in
      FStar_All.pipe_left (wrap_err "unquote") uu____10104
  
let (uvar_env :
  env ->
    FStar_Reflection_Data.typ FStar_Pervasives_Native.option ->
      FStar_Syntax_Syntax.term tac)
  =
  fun env  ->
    fun ty  ->
      let uu____10194 =
        match ty with
        | FStar_Pervasives_Native.Some ty1 -> ret ty1
        | FStar_Pervasives_Native.None  ->
            let uu____10200 =
              let uu____10207 =
                let uu____10208 = FStar_Syntax_Util.type_u ()  in
                FStar_All.pipe_left FStar_Pervasives_Native.fst uu____10208
                 in
              new_uvar "uvar_env.2" env uu____10207  in
            bind uu____10200
              (fun uu____10224  ->
                 match uu____10224 with | (typ,uvar_typ) -> ret typ)
         in
      bind uu____10194
        (fun typ  ->
           let uu____10236 = new_uvar "uvar_env" env typ  in
           bind uu____10236
             (fun uu____10250  ->
                match uu____10250 with | (t,uvar_t) -> ret t))
  
let (unshelve : FStar_Syntax_Syntax.term -> unit tac) =
  fun t  ->
    let uu____10268 =
      bind get
        (fun ps  ->
           let env = ps.FStar_Tactics_Types.main_context  in
           let opts =
             match ps.FStar_Tactics_Types.goals with
             | g::uu____10287 -> g.FStar_Tactics_Types.opts
             | uu____10290 -> FStar_Options.peek ()  in
           let uu____10293 = FStar_Syntax_Util.head_and_args t  in
           match uu____10293 with
           | ({
                FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                  (ctx_uvar,uu____10313);
                FStar_Syntax_Syntax.pos = uu____10314;
                FStar_Syntax_Syntax.vars = uu____10315;_},uu____10316)
               ->
               let env1 =
                 let uu___424_10358 = env  in
                 {
                   FStar_TypeChecker_Env.solver =
                     (uu___424_10358.FStar_TypeChecker_Env.solver);
                   FStar_TypeChecker_Env.range =
                     (uu___424_10358.FStar_TypeChecker_Env.range);
                   FStar_TypeChecker_Env.curmodule =
                     (uu___424_10358.FStar_TypeChecker_Env.curmodule);
                   FStar_TypeChecker_Env.gamma =
                     (ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_gamma);
                   FStar_TypeChecker_Env.gamma_sig =
                     (uu___424_10358.FStar_TypeChecker_Env.gamma_sig);
                   FStar_TypeChecker_Env.gamma_cache =
                     (uu___424_10358.FStar_TypeChecker_Env.gamma_cache);
                   FStar_TypeChecker_Env.modules =
                     (uu___424_10358.FStar_TypeChecker_Env.modules);
                   FStar_TypeChecker_Env.expected_typ =
                     (uu___424_10358.FStar_TypeChecker_Env.expected_typ);
                   FStar_TypeChecker_Env.sigtab =
                     (uu___424_10358.FStar_TypeChecker_Env.sigtab);
                   FStar_TypeChecker_Env.attrtab =
                     (uu___424_10358.FStar_TypeChecker_Env.attrtab);
                   FStar_TypeChecker_Env.is_pattern =
                     (uu___424_10358.FStar_TypeChecker_Env.is_pattern);
                   FStar_TypeChecker_Env.instantiate_imp =
                     (uu___424_10358.FStar_TypeChecker_Env.instantiate_imp);
                   FStar_TypeChecker_Env.effects =
                     (uu___424_10358.FStar_TypeChecker_Env.effects);
                   FStar_TypeChecker_Env.generalize =
                     (uu___424_10358.FStar_TypeChecker_Env.generalize);
                   FStar_TypeChecker_Env.letrecs =
                     (uu___424_10358.FStar_TypeChecker_Env.letrecs);
                   FStar_TypeChecker_Env.top_level =
                     (uu___424_10358.FStar_TypeChecker_Env.top_level);
                   FStar_TypeChecker_Env.check_uvars =
                     (uu___424_10358.FStar_TypeChecker_Env.check_uvars);
                   FStar_TypeChecker_Env.use_eq =
                     (uu___424_10358.FStar_TypeChecker_Env.use_eq);
                   FStar_TypeChecker_Env.is_iface =
                     (uu___424_10358.FStar_TypeChecker_Env.is_iface);
                   FStar_TypeChecker_Env.admit =
                     (uu___424_10358.FStar_TypeChecker_Env.admit);
                   FStar_TypeChecker_Env.lax =
                     (uu___424_10358.FStar_TypeChecker_Env.lax);
                   FStar_TypeChecker_Env.lax_universes =
                     (uu___424_10358.FStar_TypeChecker_Env.lax_universes);
                   FStar_TypeChecker_Env.phase1 =
                     (uu___424_10358.FStar_TypeChecker_Env.phase1);
                   FStar_TypeChecker_Env.failhard =
                     (uu___424_10358.FStar_TypeChecker_Env.failhard);
                   FStar_TypeChecker_Env.nosynth =
                     (uu___424_10358.FStar_TypeChecker_Env.nosynth);
                   FStar_TypeChecker_Env.uvar_subtyping =
                     (uu___424_10358.FStar_TypeChecker_Env.uvar_subtyping);
                   FStar_TypeChecker_Env.tc_term =
                     (uu___424_10358.FStar_TypeChecker_Env.tc_term);
                   FStar_TypeChecker_Env.type_of =
                     (uu___424_10358.FStar_TypeChecker_Env.type_of);
                   FStar_TypeChecker_Env.universe_of =
                     (uu___424_10358.FStar_TypeChecker_Env.universe_of);
                   FStar_TypeChecker_Env.check_type_of =
                     (uu___424_10358.FStar_TypeChecker_Env.check_type_of);
                   FStar_TypeChecker_Env.use_bv_sorts =
                     (uu___424_10358.FStar_TypeChecker_Env.use_bv_sorts);
                   FStar_TypeChecker_Env.qtbl_name_and_index =
                     (uu___424_10358.FStar_TypeChecker_Env.qtbl_name_and_index);
                   FStar_TypeChecker_Env.normalized_eff_names =
                     (uu___424_10358.FStar_TypeChecker_Env.normalized_eff_names);
                   FStar_TypeChecker_Env.fv_delta_depths =
                     (uu___424_10358.FStar_TypeChecker_Env.fv_delta_depths);
                   FStar_TypeChecker_Env.proof_ns =
                     (uu___424_10358.FStar_TypeChecker_Env.proof_ns);
                   FStar_TypeChecker_Env.synth_hook =
                     (uu___424_10358.FStar_TypeChecker_Env.synth_hook);
                   FStar_TypeChecker_Env.splice =
                     (uu___424_10358.FStar_TypeChecker_Env.splice);
                   FStar_TypeChecker_Env.postprocess =
                     (uu___424_10358.FStar_TypeChecker_Env.postprocess);
                   FStar_TypeChecker_Env.is_native_tactic =
                     (uu___424_10358.FStar_TypeChecker_Env.is_native_tactic);
                   FStar_TypeChecker_Env.identifier_info =
                     (uu___424_10358.FStar_TypeChecker_Env.identifier_info);
                   FStar_TypeChecker_Env.tc_hooks =
                     (uu___424_10358.FStar_TypeChecker_Env.tc_hooks);
                   FStar_TypeChecker_Env.dsenv =
                     (uu___424_10358.FStar_TypeChecker_Env.dsenv);
                   FStar_TypeChecker_Env.nbe =
                     (uu___424_10358.FStar_TypeChecker_Env.nbe)
                 }  in
               let g =
                 FStar_Tactics_Types.mk_goal env1 ctx_uvar opts false ""  in
               let uu____10360 =
                 let uu____10363 = bnorm_goal g  in [uu____10363]  in
               add_goals uu____10360
           | uu____10364 -> fail "not a uvar")
       in
    FStar_All.pipe_left (wrap_err "unshelve") uu____10268
  
let (tac_and : Prims.bool tac -> Prims.bool tac -> Prims.bool tac) =
  fun t1  ->
    fun t2  ->
      let comp =
        bind t1
          (fun b  ->
             let uu____10413 = if b then t2 else ret false  in
             bind uu____10413 (fun b'  -> if b' then ret b' else fail ""))
         in
      let uu____10424 = trytac comp  in
      bind uu____10424
        (fun uu___354_10432  ->
           match uu___354_10432 with
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
        let uu____10458 =
          bind get
            (fun ps  ->
               let uu____10464 = __tc e t1  in
               bind uu____10464
                 (fun uu____10484  ->
                    match uu____10484 with
                    | (t11,ty1,g1) ->
                        let uu____10496 = __tc e t2  in
                        bind uu____10496
                          (fun uu____10516  ->
                             match uu____10516 with
                             | (t21,ty2,g2) ->
                                 let uu____10528 =
                                   proc_guard "unify_env g1" e g1  in
                                 bind uu____10528
                                   (fun uu____10533  ->
                                      let uu____10534 =
                                        proc_guard "unify_env g2" e g2  in
                                      bind uu____10534
                                        (fun uu____10540  ->
                                           let uu____10541 =
                                             do_unify e ty1 ty2  in
                                           let uu____10544 =
                                             do_unify e t11 t21  in
                                           tac_and uu____10541 uu____10544)))))
           in
        FStar_All.pipe_left (wrap_err "unify_env") uu____10458
  
let (launch_process :
  Prims.string -> Prims.string Prims.list -> Prims.string -> Prims.string tac)
  =
  fun prog  ->
    fun args  ->
      fun input  ->
        bind idtac
          (fun uu____10577  ->
             let uu____10578 = FStar_Options.unsafe_tactic_exec ()  in
             if uu____10578
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
        (fun uu____10599  ->
           let uu____10600 =
             FStar_Syntax_Syntax.gen_bv nm FStar_Pervasives_Native.None t  in
           ret uu____10600)
  
let (change : FStar_Reflection_Data.typ -> unit tac) =
  fun ty  ->
    let uu____10610 =
      mlog
        (fun uu____10615  ->
           let uu____10616 = FStar_Syntax_Print.term_to_string ty  in
           FStar_Util.print1 "change: ty = %s\n" uu____10616)
        (fun uu____10619  ->
           let uu____10620 = cur_goal ()  in
           bind uu____10620
             (fun g  ->
                let uu____10626 =
                  let uu____10635 = FStar_Tactics_Types.goal_env g  in
                  __tc uu____10635 ty  in
                bind uu____10626
                  (fun uu____10647  ->
                     match uu____10647 with
                     | (ty1,uu____10657,guard) ->
                         let uu____10659 =
                           let uu____10662 = FStar_Tactics_Types.goal_env g
                              in
                           proc_guard "change" uu____10662 guard  in
                         bind uu____10659
                           (fun uu____10665  ->
                              let uu____10666 =
                                let uu____10669 =
                                  FStar_Tactics_Types.goal_env g  in
                                let uu____10670 =
                                  FStar_Tactics_Types.goal_type g  in
                                do_unify uu____10669 uu____10670 ty1  in
                              bind uu____10666
                                (fun bb  ->
                                   if bb
                                   then
                                     let uu____10676 =
                                       FStar_Tactics_Types.goal_with_type g
                                         ty1
                                        in
                                     replace_cur uu____10676
                                   else
                                     (let steps =
                                        [FStar_TypeChecker_Env.AllowUnboundUniverses;
                                        FStar_TypeChecker_Env.UnfoldUntil
                                          FStar_Syntax_Syntax.delta_constant;
                                        FStar_TypeChecker_Env.Primops]  in
                                      let ng =
                                        let uu____10682 =
                                          FStar_Tactics_Types.goal_env g  in
                                        let uu____10683 =
                                          FStar_Tactics_Types.goal_type g  in
                                        normalize steps uu____10682
                                          uu____10683
                                         in
                                      let nty =
                                        let uu____10685 =
                                          FStar_Tactics_Types.goal_env g  in
                                        normalize steps uu____10685 ty1  in
                                      let uu____10686 =
                                        let uu____10689 =
                                          FStar_Tactics_Types.goal_env g  in
                                        do_unify uu____10689 ng nty  in
                                      bind uu____10686
                                        (fun b  ->
                                           if b
                                           then
                                             let uu____10695 =
                                               FStar_Tactics_Types.goal_with_type
                                                 g ty1
                                                in
                                             replace_cur uu____10695
                                           else fail "not convertible")))))))
       in
    FStar_All.pipe_left (wrap_err "change") uu____10610
  
let failwhen : 'a . Prims.bool -> Prims.string -> (unit -> 'a tac) -> 'a tac
  = fun b  -> fun msg  -> fun k  -> if b then fail msg else k () 
let (t_destruct :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.fv,FStar_BigInt.t) FStar_Pervasives_Native.tuple2
      Prims.list tac)
  =
  fun s_tm  ->
    let uu____10758 =
      let uu____10767 = cur_goal ()  in
      bind uu____10767
        (fun g  ->
           let uu____10779 =
             let uu____10788 = FStar_Tactics_Types.goal_env g  in
             __tc uu____10788 s_tm  in
           bind uu____10779
             (fun uu____10806  ->
                match uu____10806 with
                | (s_tm1,s_ty,guard) ->
                    let uu____10824 =
                      let uu____10827 = FStar_Tactics_Types.goal_env g  in
                      proc_guard "destruct" uu____10827 guard  in
                    bind uu____10824
                      (fun uu____10839  ->
                         let uu____10840 =
                           FStar_Syntax_Util.head_and_args' s_ty  in
                         match uu____10840 with
                         | (h,args) ->
                             let uu____10885 =
                               let uu____10892 =
                                 let uu____10893 =
                                   FStar_Syntax_Subst.compress h  in
                                 uu____10893.FStar_Syntax_Syntax.n  in
                               match uu____10892 with
                               | FStar_Syntax_Syntax.Tm_fvar fv ->
                                   ret (fv, [])
                               | FStar_Syntax_Syntax.Tm_uinst
                                   ({
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.Tm_fvar fv;
                                      FStar_Syntax_Syntax.pos = uu____10908;
                                      FStar_Syntax_Syntax.vars = uu____10909;_},us)
                                   -> ret (fv, us)
                               | uu____10919 -> fail "type is not an fv"  in
                             bind uu____10885
                               (fun uu____10939  ->
                                  match uu____10939 with
                                  | (fv,a_us) ->
                                      let t_lid =
                                        FStar_Syntax_Syntax.lid_of_fv fv  in
                                      let uu____10955 =
                                        let uu____10958 =
                                          FStar_Tactics_Types.goal_env g  in
                                        FStar_TypeChecker_Env.lookup_sigelt
                                          uu____10958 t_lid
                                         in
                                      (match uu____10955 with
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
                                                  (fun uu____11007  ->
                                                     let uu____11008 =
                                                       FStar_Syntax_Subst.open_term
                                                         t_ps t_ty
                                                        in
                                                     match uu____11008 with
                                                     | (t_ps1,t_ty1) ->
                                                         let uu____11023 =
                                                           mapM
                                                             (fun c_lid  ->
                                                                let uu____11051
                                                                  =
                                                                  let uu____11054
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    g  in
                                                                  FStar_TypeChecker_Env.lookup_sigelt
                                                                    uu____11054
                                                                    c_lid
                                                                   in
                                                                match uu____11051
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
                                                                    uu____11124
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
                                                                    let uu____11129
                                                                    =
                                                                    FStar_TypeChecker_Env.inst_tscheme
                                                                    (c_us,
                                                                    c_ty1)
                                                                     in
                                                                    match uu____11129
                                                                    with
                                                                    | 
                                                                    (c_us1,c_ty2)
                                                                    ->
                                                                    let uu____11152
                                                                    =
                                                                    FStar_Syntax_Util.arrow_formals_comp
                                                                    c_ty2  in
                                                                    (match uu____11152
                                                                    with
                                                                    | 
                                                                    (bs,comp)
                                                                    ->
                                                                    let uu____11195
                                                                    =
                                                                    FStar_List.splitAt
                                                                    nparam bs
                                                                     in
                                                                    (match uu____11195
                                                                    with
                                                                    | 
                                                                    (d_ps,bs1)
                                                                    ->
                                                                    let uu____11268
                                                                    =
                                                                    let uu____11269
                                                                    =
                                                                    FStar_Syntax_Util.is_total_comp
                                                                    comp  in
                                                                    Prims.op_Negation
                                                                    uu____11269
                                                                     in
                                                                    failwhen
                                                                    uu____11268
                                                                    "not total?"
                                                                    (fun
                                                                    uu____11286
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
                                                                    uu___355_11302
                                                                    =
                                                                    match uu___355_11302
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    (FStar_Syntax_Syntax.Implicit
                                                                    uu____11305)
                                                                    -> true
                                                                    | 
                                                                    uu____11306
                                                                    -> false
                                                                     in
                                                                    let uu____11309
                                                                    =
                                                                    FStar_List.splitAt
                                                                    nparam
                                                                    args  in
                                                                    match uu____11309
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
                                                                    uu____11442
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
                                                                    uu____11504
                                                                     ->
                                                                    match uu____11504
                                                                    with
                                                                    | 
                                                                    ((bv,uu____11524),
                                                                    (t,uu____11526))
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
                                                                    uu____11594
                                                                     ->
                                                                    match uu____11594
                                                                    with
                                                                    | 
                                                                    ((bv,uu____11620),
                                                                    (t,uu____11622))
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
                                                                    uu____11677
                                                                     ->
                                                                    match uu____11677
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
                                                                    let uu____11727
                                                                    =
                                                                    FStar_TypeChecker_TcTerm.tc_pat
                                                                    (let uu___425_11744
                                                                    = env  in
                                                                    {
                                                                    FStar_TypeChecker_Env.solver
                                                                    =
                                                                    (uu___425_11744.FStar_TypeChecker_Env.solver);
                                                                    FStar_TypeChecker_Env.range
                                                                    =
                                                                    (uu___425_11744.FStar_TypeChecker_Env.range);
                                                                    FStar_TypeChecker_Env.curmodule
                                                                    =
                                                                    (uu___425_11744.FStar_TypeChecker_Env.curmodule);
                                                                    FStar_TypeChecker_Env.gamma
                                                                    =
                                                                    (uu___425_11744.FStar_TypeChecker_Env.gamma);
                                                                    FStar_TypeChecker_Env.gamma_sig
                                                                    =
                                                                    (uu___425_11744.FStar_TypeChecker_Env.gamma_sig);
                                                                    FStar_TypeChecker_Env.gamma_cache
                                                                    =
                                                                    (uu___425_11744.FStar_TypeChecker_Env.gamma_cache);
                                                                    FStar_TypeChecker_Env.modules
                                                                    =
                                                                    (uu___425_11744.FStar_TypeChecker_Env.modules);
                                                                    FStar_TypeChecker_Env.expected_typ
                                                                    =
                                                                    (uu___425_11744.FStar_TypeChecker_Env.expected_typ);
                                                                    FStar_TypeChecker_Env.sigtab
                                                                    =
                                                                    (uu___425_11744.FStar_TypeChecker_Env.sigtab);
                                                                    FStar_TypeChecker_Env.attrtab
                                                                    =
                                                                    (uu___425_11744.FStar_TypeChecker_Env.attrtab);
                                                                    FStar_TypeChecker_Env.is_pattern
                                                                    =
                                                                    (uu___425_11744.FStar_TypeChecker_Env.is_pattern);
                                                                    FStar_TypeChecker_Env.instantiate_imp
                                                                    =
                                                                    (uu___425_11744.FStar_TypeChecker_Env.instantiate_imp);
                                                                    FStar_TypeChecker_Env.effects
                                                                    =
                                                                    (uu___425_11744.FStar_TypeChecker_Env.effects);
                                                                    FStar_TypeChecker_Env.generalize
                                                                    =
                                                                    (uu___425_11744.FStar_TypeChecker_Env.generalize);
                                                                    FStar_TypeChecker_Env.letrecs
                                                                    =
                                                                    (uu___425_11744.FStar_TypeChecker_Env.letrecs);
                                                                    FStar_TypeChecker_Env.top_level
                                                                    =
                                                                    (uu___425_11744.FStar_TypeChecker_Env.top_level);
                                                                    FStar_TypeChecker_Env.check_uvars
                                                                    =
                                                                    (uu___425_11744.FStar_TypeChecker_Env.check_uvars);
                                                                    FStar_TypeChecker_Env.use_eq
                                                                    =
                                                                    (uu___425_11744.FStar_TypeChecker_Env.use_eq);
                                                                    FStar_TypeChecker_Env.is_iface
                                                                    =
                                                                    (uu___425_11744.FStar_TypeChecker_Env.is_iface);
                                                                    FStar_TypeChecker_Env.admit
                                                                    =
                                                                    (uu___425_11744.FStar_TypeChecker_Env.admit);
                                                                    FStar_TypeChecker_Env.lax
                                                                    = true;
                                                                    FStar_TypeChecker_Env.lax_universes
                                                                    =
                                                                    (uu___425_11744.FStar_TypeChecker_Env.lax_universes);
                                                                    FStar_TypeChecker_Env.phase1
                                                                    =
                                                                    (uu___425_11744.FStar_TypeChecker_Env.phase1);
                                                                    FStar_TypeChecker_Env.failhard
                                                                    =
                                                                    (uu___425_11744.FStar_TypeChecker_Env.failhard);
                                                                    FStar_TypeChecker_Env.nosynth
                                                                    =
                                                                    (uu___425_11744.FStar_TypeChecker_Env.nosynth);
                                                                    FStar_TypeChecker_Env.uvar_subtyping
                                                                    =
                                                                    (uu___425_11744.FStar_TypeChecker_Env.uvar_subtyping);
                                                                    FStar_TypeChecker_Env.tc_term
                                                                    =
                                                                    (uu___425_11744.FStar_TypeChecker_Env.tc_term);
                                                                    FStar_TypeChecker_Env.type_of
                                                                    =
                                                                    (uu___425_11744.FStar_TypeChecker_Env.type_of);
                                                                    FStar_TypeChecker_Env.universe_of
                                                                    =
                                                                    (uu___425_11744.FStar_TypeChecker_Env.universe_of);
                                                                    FStar_TypeChecker_Env.check_type_of
                                                                    =
                                                                    (uu___425_11744.FStar_TypeChecker_Env.check_type_of);
                                                                    FStar_TypeChecker_Env.use_bv_sorts
                                                                    =
                                                                    (uu___425_11744.FStar_TypeChecker_Env.use_bv_sorts);
                                                                    FStar_TypeChecker_Env.qtbl_name_and_index
                                                                    =
                                                                    (uu___425_11744.FStar_TypeChecker_Env.qtbl_name_and_index);
                                                                    FStar_TypeChecker_Env.normalized_eff_names
                                                                    =
                                                                    (uu___425_11744.FStar_TypeChecker_Env.normalized_eff_names);
                                                                    FStar_TypeChecker_Env.fv_delta_depths
                                                                    =
                                                                    (uu___425_11744.FStar_TypeChecker_Env.fv_delta_depths);
                                                                    FStar_TypeChecker_Env.proof_ns
                                                                    =
                                                                    (uu___425_11744.FStar_TypeChecker_Env.proof_ns);
                                                                    FStar_TypeChecker_Env.synth_hook
                                                                    =
                                                                    (uu___425_11744.FStar_TypeChecker_Env.synth_hook);
                                                                    FStar_TypeChecker_Env.splice
                                                                    =
                                                                    (uu___425_11744.FStar_TypeChecker_Env.splice);
                                                                    FStar_TypeChecker_Env.postprocess
                                                                    =
                                                                    (uu___425_11744.FStar_TypeChecker_Env.postprocess);
                                                                    FStar_TypeChecker_Env.is_native_tactic
                                                                    =
                                                                    (uu___425_11744.FStar_TypeChecker_Env.is_native_tactic);
                                                                    FStar_TypeChecker_Env.identifier_info
                                                                    =
                                                                    (uu___425_11744.FStar_TypeChecker_Env.identifier_info);
                                                                    FStar_TypeChecker_Env.tc_hooks
                                                                    =
                                                                    (uu___425_11744.FStar_TypeChecker_Env.tc_hooks);
                                                                    FStar_TypeChecker_Env.dsenv
                                                                    =
                                                                    (uu___425_11744.FStar_TypeChecker_Env.dsenv);
                                                                    FStar_TypeChecker_Env.nbe
                                                                    =
                                                                    (uu___425_11744.FStar_TypeChecker_Env.nbe)
                                                                    }) s_ty
                                                                    pat  in
                                                                    match uu____11727
                                                                    with
                                                                    | 
                                                                    (uu____11757,uu____11758,uu____11759,pat_t,uu____11761,_guard_pat)
                                                                    ->
                                                                    let eq_b
                                                                    =
                                                                    let uu____11768
                                                                    =
                                                                    let uu____11769
                                                                    =
                                                                    FStar_Syntax_Util.mk_eq2
                                                                    equ s_ty
                                                                    s_tm1
                                                                    pat_t  in
                                                                    FStar_Syntax_Util.mk_squash
                                                                    equ
                                                                    uu____11769
                                                                     in
                                                                    FStar_Syntax_Syntax.gen_bv
                                                                    "breq"
                                                                    FStar_Pervasives_Native.None
                                                                    uu____11768
                                                                     in
                                                                    let cod1
                                                                    =
                                                                    let uu____11773
                                                                    =
                                                                    let uu____11782
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_binder
                                                                    eq_b  in
                                                                    [uu____11782]
                                                                     in
                                                                    let uu____11801
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Total
                                                                    cod  in
                                                                    FStar_Syntax_Util.arrow
                                                                    uu____11773
                                                                    uu____11801
                                                                     in
                                                                    let nty =
                                                                    let uu____11807
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Total
                                                                    cod1  in
                                                                    FStar_Syntax_Util.arrow
                                                                    bs2
                                                                    uu____11807
                                                                     in
                                                                    let uu____11810
                                                                    =
                                                                    new_uvar
                                                                    "destruct branch"
                                                                    env nty
                                                                     in
                                                                    bind
                                                                    uu____11810
                                                                    (fun
                                                                    uu____11839
                                                                     ->
                                                                    match uu____11839
                                                                    with
                                                                    | 
                                                                    (uvt,uv)
                                                                    ->
                                                                    let g' =
                                                                    FStar_Tactics_Types.mk_goal
                                                                    env uv
                                                                    g.FStar_Tactics_Types.opts
                                                                    false
                                                                    g.FStar_Tactics_Types.label
                                                                     in
                                                                    let brt =
                                                                    FStar_Syntax_Util.mk_app_binders
                                                                    uvt bs2
                                                                     in
                                                                    let brt1
                                                                    =
                                                                    let uu____11865
                                                                    =
                                                                    let uu____11876
                                                                    =
                                                                    FStar_Syntax_Syntax.as_arg
                                                                    FStar_Syntax_Util.exp_unit
                                                                     in
                                                                    [uu____11876]
                                                                     in
                                                                    FStar_Syntax_Util.mk_app
                                                                    brt
                                                                    uu____11865
                                                                     in
                                                                    let br =
                                                                    FStar_Syntax_Subst.close_branch
                                                                    (pat,
                                                                    FStar_Pervasives_Native.None,
                                                                    brt1)  in
                                                                    let uu____11912
                                                                    =
                                                                    let uu____11923
                                                                    =
                                                                    let uu____11928
                                                                    =
                                                                    FStar_BigInt.of_int_fs
                                                                    (FStar_List.length
                                                                    bs2)  in
                                                                    (fv1,
                                                                    uu____11928)
                                                                     in
                                                                    (g', br,
                                                                    uu____11923)
                                                                     in
                                                                    ret
                                                                    uu____11912))))))
                                                                    | 
                                                                    uu____11949
                                                                    ->
                                                                    fail
                                                                    "impossible: not a ctor"))
                                                             c_lids
                                                            in
                                                         bind uu____11023
                                                           (fun goal_brs  ->
                                                              let uu____11998
                                                                =
                                                                FStar_List.unzip3
                                                                  goal_brs
                                                                 in
                                                              match uu____11998
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
                                                                  let uu____12071
                                                                    =
                                                                    solve' g
                                                                    w  in
                                                                  bind
                                                                    uu____12071
                                                                    (
                                                                    fun
                                                                    uu____12082
                                                                     ->
                                                                    let uu____12083
                                                                    =
                                                                    add_goals
                                                                    goals  in
                                                                    bind
                                                                    uu____12083
                                                                    (fun
                                                                    uu____12093
                                                                     ->
                                                                    ret infos))))
                                            | uu____12100 ->
                                                fail "not an inductive type"))))))
       in
    FStar_All.pipe_left (wrap_err "destruct") uu____10758
  
let rec last : 'a . 'a Prims.list -> 'a =
  fun l  ->
    match l with
    | [] -> failwith "last: empty list"
    | x::[] -> x
    | uu____12145::xs -> last xs
  
let rec init : 'a . 'a Prims.list -> 'a Prims.list =
  fun l  ->
    match l with
    | [] -> failwith "init: empty list"
    | x::[] -> []
    | x::xs -> let uu____12173 = init xs  in x :: uu____12173
  
let rec (inspect :
  FStar_Syntax_Syntax.term -> FStar_Reflection_Data.term_view tac) =
  fun t  ->
    let uu____12185 =
      let t1 = FStar_Syntax_Util.unascribe t  in
      let t2 = FStar_Syntax_Util.un_uinst t1  in
      let t3 = FStar_Syntax_Util.unlazy_emb t2  in
      match t3.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_meta (t4,uu____12194) -> inspect t4
      | FStar_Syntax_Syntax.Tm_name bv ->
          FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_Var bv)
      | FStar_Syntax_Syntax.Tm_bvar bv ->
          FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_BVar bv)
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_FVar fv)
      | FStar_Syntax_Syntax.Tm_app (hd1,[]) ->
          failwith "empty arguments on Tm_app"
      | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
          let uu____12259 = last args  in
          (match uu____12259 with
           | (a,q) ->
               let q' = FStar_Reflection_Basic.inspect_aqual q  in
               let uu____12289 =
                 let uu____12290 =
                   let uu____12295 =
                     let uu____12296 =
                       let uu____12301 = init args  in
                       FStar_Syntax_Syntax.mk_Tm_app hd1 uu____12301  in
                     uu____12296 FStar_Pervasives_Native.None
                       t3.FStar_Syntax_Syntax.pos
                      in
                   (uu____12295, (a, q'))  in
                 FStar_Reflection_Data.Tv_App uu____12290  in
               FStar_All.pipe_left ret uu____12289)
      | FStar_Syntax_Syntax.Tm_abs ([],uu____12314,uu____12315) ->
          failwith "empty arguments on Tm_abs"
      | FStar_Syntax_Syntax.Tm_abs (bs,t4,k) ->
          let uu____12367 = FStar_Syntax_Subst.open_term bs t4  in
          (match uu____12367 with
           | (bs1,t5) ->
               (match bs1 with
                | [] -> failwith "impossible"
                | b::bs2 ->
                    let uu____12408 =
                      let uu____12409 =
                        let uu____12414 = FStar_Syntax_Util.abs bs2 t5 k  in
                        (b, uu____12414)  in
                      FStar_Reflection_Data.Tv_Abs uu____12409  in
                    FStar_All.pipe_left ret uu____12408))
      | FStar_Syntax_Syntax.Tm_type uu____12417 ->
          FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_Type ())
      | FStar_Syntax_Syntax.Tm_arrow ([],k) ->
          failwith "empty binders on arrow"
      | FStar_Syntax_Syntax.Tm_arrow uu____12441 ->
          let uu____12456 = FStar_Syntax_Util.arrow_one t3  in
          (match uu____12456 with
           | FStar_Pervasives_Native.Some (b,c) ->
               FStar_All.pipe_left ret
                 (FStar_Reflection_Data.Tv_Arrow (b, c))
           | FStar_Pervasives_Native.None  -> failwith "impossible")
      | FStar_Syntax_Syntax.Tm_refine (bv,t4) ->
          let b = FStar_Syntax_Syntax.mk_binder bv  in
          let uu____12486 = FStar_Syntax_Subst.open_term [b] t4  in
          (match uu____12486 with
           | (b',t5) ->
               let b1 =
                 match b' with
                 | b'1::[] -> b'1
                 | uu____12539 -> failwith "impossible"  in
               FStar_All.pipe_left ret
                 (FStar_Reflection_Data.Tv_Refine
                    ((FStar_Pervasives_Native.fst b1), t5)))
      | FStar_Syntax_Syntax.Tm_constant c ->
          let uu____12551 =
            let uu____12552 = FStar_Reflection_Basic.inspect_const c  in
            FStar_Reflection_Data.Tv_Const uu____12552  in
          FStar_All.pipe_left ret uu____12551
      | FStar_Syntax_Syntax.Tm_uvar (ctx_u,s) ->
          let uu____12573 =
            let uu____12574 =
              let uu____12579 =
                let uu____12580 =
                  FStar_Syntax_Unionfind.uvar_id
                    ctx_u.FStar_Syntax_Syntax.ctx_uvar_head
                   in
                FStar_BigInt.of_int_fs uu____12580  in
              (uu____12579, (ctx_u, s))  in
            FStar_Reflection_Data.Tv_Uvar uu____12574  in
          FStar_All.pipe_left ret uu____12573
      | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),t21) ->
          if lb.FStar_Syntax_Syntax.lbunivs <> []
          then FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown
          else
            (match lb.FStar_Syntax_Syntax.lbname with
             | FStar_Util.Inr uu____12614 ->
                 FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown
             | FStar_Util.Inl bv ->
                 let b = FStar_Syntax_Syntax.mk_binder bv  in
                 let uu____12619 = FStar_Syntax_Subst.open_term [b] t21  in
                 (match uu____12619 with
                  | (bs,t22) ->
                      let b1 =
                        match bs with
                        | b1::[] -> b1
                        | uu____12672 ->
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
             | FStar_Util.Inr uu____12706 ->
                 FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown
             | FStar_Util.Inl bv ->
                 let uu____12710 = FStar_Syntax_Subst.open_let_rec [lb] t21
                    in
                 (match uu____12710 with
                  | (lbs,t22) ->
                      (match lbs with
                       | lb1::[] ->
                           (match lb1.FStar_Syntax_Syntax.lbname with
                            | FStar_Util.Inr uu____12730 ->
                                ret FStar_Reflection_Data.Tv_Unknown
                            | FStar_Util.Inl bv1 ->
                                FStar_All.pipe_left ret
                                  (FStar_Reflection_Data.Tv_Let
                                     (true, bv1,
                                       (lb1.FStar_Syntax_Syntax.lbdef), t22)))
                       | uu____12734 ->
                           failwith
                             "impossible: open_term returned different amount of binders")))
      | FStar_Syntax_Syntax.Tm_match (t4,brs) ->
          let rec inspect_pat p =
            match p.FStar_Syntax_Syntax.v with
            | FStar_Syntax_Syntax.Pat_constant c ->
                let uu____12788 = FStar_Reflection_Basic.inspect_const c  in
                FStar_Reflection_Data.Pat_Constant uu____12788
            | FStar_Syntax_Syntax.Pat_cons (fv,ps) ->
                let uu____12807 =
                  let uu____12814 =
                    FStar_List.map
                      (fun uu____12826  ->
                         match uu____12826 with
                         | (p1,uu____12834) -> inspect_pat p1) ps
                     in
                  (fv, uu____12814)  in
                FStar_Reflection_Data.Pat_Cons uu____12807
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
              (fun uu___356_12928  ->
                 match uu___356_12928 with
                 | (pat,uu____12950,t5) ->
                     let uu____12968 = inspect_pat pat  in (uu____12968, t5))
              brs1
             in
          FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_Match (t4, brs2))
      | FStar_Syntax_Syntax.Tm_unknown  ->
          FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown
      | uu____12977 ->
          ((let uu____12979 =
              let uu____12984 =
                let uu____12985 = FStar_Syntax_Print.tag_of_term t3  in
                let uu____12986 = FStar_Syntax_Print.term_to_string t3  in
                FStar_Util.format2
                  "inspect: outside of expected syntax (%s, %s)\n"
                  uu____12985 uu____12986
                 in
              (FStar_Errors.Warning_CantInspect, uu____12984)  in
            FStar_Errors.log_issue t3.FStar_Syntax_Syntax.pos uu____12979);
           FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown)
       in
    wrap_err "inspect" uu____12185
  
let (pack : FStar_Reflection_Data.term_view -> FStar_Syntax_Syntax.term tac)
  =
  fun tv  ->
    match tv with
    | FStar_Reflection_Data.Tv_Var bv ->
        let uu____12999 = FStar_Syntax_Syntax.bv_to_name bv  in
        FStar_All.pipe_left ret uu____12999
    | FStar_Reflection_Data.Tv_BVar bv ->
        let uu____13003 = FStar_Syntax_Syntax.bv_to_tm bv  in
        FStar_All.pipe_left ret uu____13003
    | FStar_Reflection_Data.Tv_FVar fv ->
        let uu____13007 = FStar_Syntax_Syntax.fv_to_tm fv  in
        FStar_All.pipe_left ret uu____13007
    | FStar_Reflection_Data.Tv_App (l,(r,q)) ->
        let q' = FStar_Reflection_Basic.pack_aqual q  in
        let uu____13014 = FStar_Syntax_Util.mk_app l [(r, q')]  in
        FStar_All.pipe_left ret uu____13014
    | FStar_Reflection_Data.Tv_Abs (b,t) ->
        let uu____13039 =
          FStar_Syntax_Util.abs [b] t FStar_Pervasives_Native.None  in
        FStar_All.pipe_left ret uu____13039
    | FStar_Reflection_Data.Tv_Arrow (b,c) ->
        let uu____13056 = FStar_Syntax_Util.arrow [b] c  in
        FStar_All.pipe_left ret uu____13056
    | FStar_Reflection_Data.Tv_Type () ->
        FStar_All.pipe_left ret FStar_Syntax_Util.ktype
    | FStar_Reflection_Data.Tv_Refine (bv,t) ->
        let uu____13075 = FStar_Syntax_Util.refine bv t  in
        FStar_All.pipe_left ret uu____13075
    | FStar_Reflection_Data.Tv_Const c ->
        let uu____13079 =
          let uu____13080 =
            let uu____13087 =
              let uu____13088 = FStar_Reflection_Basic.pack_const c  in
              FStar_Syntax_Syntax.Tm_constant uu____13088  in
            FStar_Syntax_Syntax.mk uu____13087  in
          uu____13080 FStar_Pervasives_Native.None FStar_Range.dummyRange  in
        FStar_All.pipe_left ret uu____13079
    | FStar_Reflection_Data.Tv_Uvar (_u,ctx_u_s) ->
        let uu____13096 =
          FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_uvar ctx_u_s)
            FStar_Pervasives_Native.None FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____13096
    | FStar_Reflection_Data.Tv_Let (false ,bv,t1,t2) ->
        let lb =
          FStar_Syntax_Util.mk_letbinding (FStar_Util.Inl bv) []
            bv.FStar_Syntax_Syntax.sort FStar_Parser_Const.effect_Tot_lid t1
            [] FStar_Range.dummyRange
           in
        let uu____13105 =
          let uu____13106 =
            let uu____13113 =
              let uu____13114 =
                let uu____13127 =
                  let uu____13130 =
                    let uu____13131 = FStar_Syntax_Syntax.mk_binder bv  in
                    [uu____13131]  in
                  FStar_Syntax_Subst.close uu____13130 t2  in
                ((false, [lb]), uu____13127)  in
              FStar_Syntax_Syntax.Tm_let uu____13114  in
            FStar_Syntax_Syntax.mk uu____13113  in
          uu____13106 FStar_Pervasives_Native.None FStar_Range.dummyRange  in
        FStar_All.pipe_left ret uu____13105
    | FStar_Reflection_Data.Tv_Let (true ,bv,t1,t2) ->
        let lb =
          FStar_Syntax_Util.mk_letbinding (FStar_Util.Inl bv) []
            bv.FStar_Syntax_Syntax.sort FStar_Parser_Const.effect_Tot_lid t1
            [] FStar_Range.dummyRange
           in
        let uu____13171 = FStar_Syntax_Subst.close_let_rec [lb] t2  in
        (match uu____13171 with
         | (lbs,body) ->
             let uu____13186 =
               FStar_Syntax_Syntax.mk
                 (FStar_Syntax_Syntax.Tm_let ((true, lbs), body))
                 FStar_Pervasives_Native.None FStar_Range.dummyRange
                in
             FStar_All.pipe_left ret uu____13186)
    | FStar_Reflection_Data.Tv_Match (t,brs) ->
        let wrap v1 =
          {
            FStar_Syntax_Syntax.v = v1;
            FStar_Syntax_Syntax.p = FStar_Range.dummyRange
          }  in
        let rec pack_pat p =
          match p with
          | FStar_Reflection_Data.Pat_Constant c ->
              let uu____13220 =
                let uu____13221 = FStar_Reflection_Basic.pack_const c  in
                FStar_Syntax_Syntax.Pat_constant uu____13221  in
              FStar_All.pipe_left wrap uu____13220
          | FStar_Reflection_Data.Pat_Cons (fv,ps) ->
              let uu____13228 =
                let uu____13229 =
                  let uu____13242 =
                    FStar_List.map
                      (fun p1  ->
                         let uu____13258 = pack_pat p1  in
                         (uu____13258, false)) ps
                     in
                  (fv, uu____13242)  in
                FStar_Syntax_Syntax.Pat_cons uu____13229  in
              FStar_All.pipe_left wrap uu____13228
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
            (fun uu___357_13304  ->
               match uu___357_13304 with
               | (pat,t1) ->
                   let uu____13321 = pack_pat pat  in
                   (uu____13321, FStar_Pervasives_Native.None, t1)) brs
           in
        let brs2 = FStar_List.map FStar_Syntax_Subst.close_branch brs1  in
        let uu____13369 =
          FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_match (t, brs2))
            FStar_Pervasives_Native.None FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____13369
    | FStar_Reflection_Data.Tv_AscribedT (e,t,tacopt) ->
        let uu____13397 =
          FStar_Syntax_Syntax.mk
            (FStar_Syntax_Syntax.Tm_ascribed
               (e, ((FStar_Util.Inl t), tacopt),
                 FStar_Pervasives_Native.None)) FStar_Pervasives_Native.None
            FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____13397
    | FStar_Reflection_Data.Tv_AscribedC (e,c,tacopt) ->
        let uu____13443 =
          FStar_Syntax_Syntax.mk
            (FStar_Syntax_Syntax.Tm_ascribed
               (e, ((FStar_Util.Inr c), tacopt),
                 FStar_Pervasives_Native.None)) FStar_Pervasives_Native.None
            FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____13443
    | FStar_Reflection_Data.Tv_Unknown  ->
        let uu____13482 =
          FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown
            FStar_Pervasives_Native.None FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____13482
  
let (lget :
  FStar_Reflection_Data.typ -> Prims.string -> FStar_Syntax_Syntax.term tac)
  =
  fun ty  ->
    fun k  ->
      let uu____13499 =
        bind get
          (fun ps  ->
             let uu____13505 =
               FStar_Util.psmap_try_find ps.FStar_Tactics_Types.local_state k
                in
             match uu____13505 with
             | FStar_Pervasives_Native.None  -> fail "not found"
             | FStar_Pervasives_Native.Some t -> unquote ty t)
         in
      FStar_All.pipe_left (wrap_err "lget") uu____13499
  
let (lset :
  FStar_Reflection_Data.typ ->
    Prims.string -> FStar_Syntax_Syntax.term -> unit tac)
  =
  fun _ty  ->
    fun k  ->
      fun t  ->
        let uu____13534 =
          bind get
            (fun ps  ->
               let ps1 =
                 let uu___426_13541 = ps  in
                 let uu____13542 =
                   FStar_Util.psmap_add ps.FStar_Tactics_Types.local_state k
                     t
                    in
                 {
                   FStar_Tactics_Types.main_context =
                     (uu___426_13541.FStar_Tactics_Types.main_context);
                   FStar_Tactics_Types.main_goal =
                     (uu___426_13541.FStar_Tactics_Types.main_goal);
                   FStar_Tactics_Types.all_implicits =
                     (uu___426_13541.FStar_Tactics_Types.all_implicits);
                   FStar_Tactics_Types.goals =
                     (uu___426_13541.FStar_Tactics_Types.goals);
                   FStar_Tactics_Types.smt_goals =
                     (uu___426_13541.FStar_Tactics_Types.smt_goals);
                   FStar_Tactics_Types.depth =
                     (uu___426_13541.FStar_Tactics_Types.depth);
                   FStar_Tactics_Types.__dump =
                     (uu___426_13541.FStar_Tactics_Types.__dump);
                   FStar_Tactics_Types.psc =
                     (uu___426_13541.FStar_Tactics_Types.psc);
                   FStar_Tactics_Types.entry_range =
                     (uu___426_13541.FStar_Tactics_Types.entry_range);
                   FStar_Tactics_Types.guard_policy =
                     (uu___426_13541.FStar_Tactics_Types.guard_policy);
                   FStar_Tactics_Types.freshness =
                     (uu___426_13541.FStar_Tactics_Types.freshness);
                   FStar_Tactics_Types.tac_verb_dbg =
                     (uu___426_13541.FStar_Tactics_Types.tac_verb_dbg);
                   FStar_Tactics_Types.local_state = uu____13542
                 }  in
               set ps1)
           in
        FStar_All.pipe_left (wrap_err "lset") uu____13534
  
let (goal_of_goal_ty :
  env ->
    FStar_Reflection_Data.typ ->
      (FStar_Tactics_Types.goal,FStar_TypeChecker_Env.guard_t)
        FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun typ  ->
      let uu____13567 =
        FStar_TypeChecker_Util.new_implicit_var "proofstate_of_goal_ty"
          typ.FStar_Syntax_Syntax.pos env typ
         in
      match uu____13567 with
      | (u,ctx_uvars,g_u) ->
          let uu____13599 = FStar_List.hd ctx_uvars  in
          (match uu____13599 with
           | (ctx_uvar,uu____13613) ->
               let g =
                 let uu____13615 = FStar_Options.peek ()  in
                 FStar_Tactics_Types.mk_goal env ctx_uvar uu____13615 false
                   ""
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
        let uu____13635 = goal_of_goal_ty env typ  in
        match uu____13635 with
        | (g,g_u) ->
            let ps =
              let uu____13647 =
                FStar_TypeChecker_Env.debug env
                  (FStar_Options.Other "TacVerbose")
                 in
              let uu____13648 = FStar_Util.psmap_empty ()  in
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
                FStar_Tactics_Types.tac_verb_dbg = uu____13647;
                FStar_Tactics_Types.local_state = uu____13648
              }  in
            let uu____13655 = FStar_Tactics_Types.goal_witness g  in
            (ps, uu____13655)
  