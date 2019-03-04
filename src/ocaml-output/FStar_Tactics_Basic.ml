open Prims
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
    let uu____68814 =
      let uu____68815 = FStar_Tactics_Types.goal_env g  in
      let uu____68816 = FStar_Tactics_Types.goal_type g  in
      bnorm uu____68815 uu____68816  in
    FStar_Tactics_Types.goal_with_type g uu____68814
  
type 'a tac =
  {
  tac_f: FStar_Tactics_Types.proofstate -> 'a FStar_Tactics_Result.__result }
let __proj__Mktac__item__tac_f :
  'a .
    'a tac ->
      FStar_Tactics_Types.proofstate -> 'a FStar_Tactics_Result.__result
  = fun projectee  -> match projectee with | { tac_f;_} -> tac_f 
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
      let uu____68930 = FStar_Options.tactics_failhard ()  in
      if uu____68930
      then run t p
      else
        (try (fun uu___640_68940  -> match () with | () -> run t p) ()
         with
         | FStar_Errors.Err (uu____68949,msg) ->
             FStar_Tactics_Result.Failed
               ((FStar_Tactics_Types.TacticFailure msg), p)
         | FStar_Errors.Error (uu____68953,msg,uu____68955) ->
             FStar_Tactics_Result.Failed
               ((FStar_Tactics_Types.TacticFailure msg), p)
         | e -> FStar_Tactics_Result.Failed (e, p))
  
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
           let uu____69035 = run t1 p  in
           match uu____69035 with
           | FStar_Tactics_Result.Success (a,q) ->
               let uu____69042 = t2 a  in run uu____69042 q
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
    let uu____69065 =
      FStar_Syntax_Unionfind.find uv.FStar_Syntax_Syntax.ctx_uvar_head  in
    match uu____69065 with
    | FStar_Pervasives_Native.Some t -> FStar_Pervasives_Native.Some t
    | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
  
let (check_goal_solved :
  FStar_Tactics_Types.goal ->
    FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  = fun goal  -> get_uvar_solved goal.FStar_Tactics_Types.goal_ctx_uvar 
let (goal_to_string_verbose : FStar_Tactics_Types.goal -> Prims.string) =
  fun g  ->
    let uu____69087 =
      FStar_Syntax_Print.ctx_uvar_to_string
        g.FStar_Tactics_Types.goal_ctx_uvar
       in
    let uu____69089 =
      let uu____69091 = check_goal_solved g  in
      match uu____69091 with
      | FStar_Pervasives_Native.None  -> ""
      | FStar_Pervasives_Native.Some t ->
          let uu____69097 = FStar_Syntax_Print.term_to_string t  in
          FStar_Util.format1 "\tGOAL ALREADY SOLVED!: %s" uu____69097
       in
    FStar_Util.format2 "%s%s\n" uu____69087 uu____69089
  
let (goal_to_string :
  Prims.string ->
    (Prims.int * Prims.int) FStar_Pervasives_Native.option ->
      FStar_Tactics_Types.proofstate ->
        FStar_Tactics_Types.goal -> Prims.string)
  =
  fun kind  ->
    fun maybe_num  ->
      fun ps  ->
        fun g  ->
          let w =
            let uu____69144 = FStar_Options.print_implicits ()  in
            if uu____69144
            then
              let uu____69148 = FStar_Tactics_Types.goal_env g  in
              let uu____69149 = FStar_Tactics_Types.goal_witness g  in
              tts uu____69148 uu____69149
            else
              (let uu____69152 =
                 get_uvar_solved g.FStar_Tactics_Types.goal_ctx_uvar  in
               match uu____69152 with
               | FStar_Pervasives_Native.None  -> "_"
               | FStar_Pervasives_Native.Some t ->
                   let uu____69158 = FStar_Tactics_Types.goal_env g  in
                   let uu____69159 = FStar_Tactics_Types.goal_witness g  in
                   tts uu____69158 uu____69159)
             in
          let num =
            match maybe_num with
            | FStar_Pervasives_Native.None  -> ""
            | FStar_Pervasives_Native.Some (i,n1) ->
                let uu____69182 = FStar_Util.string_of_int i  in
                let uu____69184 = FStar_Util.string_of_int n1  in
                FStar_Util.format2 " %s/%s" uu____69182 uu____69184
             in
          let maybe_label =
            match g.FStar_Tactics_Types.label with
            | "" -> ""
            | l -> Prims.op_Hat " (" (Prims.op_Hat l ")")  in
          let actual_goal =
            if ps.FStar_Tactics_Types.tac_verb_dbg
            then goal_to_string_verbose g
            else
              (let uu____69202 =
                 FStar_Syntax_Print.binders_to_string ", "
                   (g.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_binders
                  in
               let uu____69205 =
                 let uu____69207 = FStar_Tactics_Types.goal_env g  in
                 tts uu____69207
                   (g.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_typ
                  in
               FStar_Util.format3 "%s |- %s : %s\n" uu____69202 w uu____69205)
             in
          FStar_Util.format4 "%s%s%s:\n%s\n" kind num maybe_label actual_goal
  
let (tacprint : Prims.string -> unit) =
  fun s  -> FStar_Util.print1 "TAC>> %s\n" s 
let (tacprint1 : Prims.string -> Prims.string -> unit) =
  fun s  ->
    fun x  ->
      let uu____69234 = FStar_Util.format1 s x  in
      FStar_Util.print1 "TAC>> %s\n" uu____69234
  
let (tacprint2 : Prims.string -> Prims.string -> Prims.string -> unit) =
  fun s  ->
    fun x  ->
      fun y  ->
        let uu____69259 = FStar_Util.format2 s x y  in
        FStar_Util.print1 "TAC>> %s\n" uu____69259
  
let (tacprint3 :
  Prims.string -> Prims.string -> Prims.string -> Prims.string -> unit) =
  fun s  ->
    fun x  ->
      fun y  ->
        fun z  ->
          let uu____69291 = FStar_Util.format3 s x y z  in
          FStar_Util.print1 "TAC>> %s\n" uu____69291
  
let (comp_to_typ : FStar_Syntax_Syntax.comp -> FStar_Reflection_Data.typ) =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Total (t,uu____69301) -> t
    | FStar_Syntax_Syntax.GTotal (t,uu____69311) -> t
    | FStar_Syntax_Syntax.Comp ct -> ct.FStar_Syntax_Syntax.result_typ
  
let (get_phi :
  FStar_Tactics_Types.goal ->
    FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun g  ->
    let uu____69331 =
      let uu____69332 = FStar_Tactics_Types.goal_env g  in
      let uu____69333 = FStar_Tactics_Types.goal_type g  in
      FStar_TypeChecker_Normalize.unfold_whnf uu____69332 uu____69333  in
    FStar_Syntax_Util.un_squash uu____69331
  
let (is_irrelevant : FStar_Tactics_Types.goal -> Prims.bool) =
  fun g  -> let uu____69342 = get_phi g  in FStar_Option.isSome uu____69342 
let (print : Prims.string -> unit tac) = fun msg  -> tacprint msg; ret () 
let (debugging : unit -> Prims.bool tac) =
  fun uu____69366  ->
    bind get
      (fun ps  ->
         let uu____69374 =
           FStar_TypeChecker_Env.debug ps.FStar_Tactics_Types.main_context
             (FStar_Options.Other "Tac")
            in
         ret uu____69374)
  
let (ps_to_string :
  (Prims.string * FStar_Tactics_Types.proofstate) -> Prims.string) =
  fun uu____69389  ->
    match uu____69389 with
    | (msg,ps) ->
        let p_imp imp =
          FStar_Syntax_Print.uvar_to_string
            (imp.FStar_TypeChecker_Env.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_head
           in
        let n_active = FStar_List.length ps.FStar_Tactics_Types.goals  in
        let n_smt = FStar_List.length ps.FStar_Tactics_Types.smt_goals  in
        let n1 = n_active + n_smt  in
        let uu____69421 =
          let uu____69425 =
            let uu____69429 =
              let uu____69431 =
                FStar_Util.string_of_int ps.FStar_Tactics_Types.depth  in
              FStar_Util.format2 "State dump @ depth %s (%s):\n" uu____69431
                msg
               in
            let uu____69434 =
              let uu____69438 =
                if
                  ps.FStar_Tactics_Types.entry_range <>
                    FStar_Range.dummyRange
                then
                  let uu____69442 =
                    FStar_Range.string_of_def_range
                      ps.FStar_Tactics_Types.entry_range
                     in
                  FStar_Util.format1 "Location: %s\n" uu____69442
                else ""  in
              let uu____69448 =
                let uu____69452 =
                  let uu____69454 =
                    FStar_TypeChecker_Env.debug
                      ps.FStar_Tactics_Types.main_context
                      (FStar_Options.Other "Imp")
                     in
                  if uu____69454
                  then
                    let uu____69459 =
                      FStar_Common.string_of_list p_imp
                        ps.FStar_Tactics_Types.all_implicits
                       in
                    FStar_Util.format1 "Imps: %s\n" uu____69459
                  else ""  in
                [uu____69452]  in
              uu____69438 :: uu____69448  in
            uu____69429 :: uu____69434  in
          let uu____69469 =
            let uu____69473 =
              FStar_List.mapi
                (fun i  ->
                   fun g  ->
                     goal_to_string "Goal"
                       (FStar_Pervasives_Native.Some
                          (((Prims.parse_int "1") + i), n1)) ps g)
                ps.FStar_Tactics_Types.goals
               in
            let uu____69493 =
              FStar_List.mapi
                (fun i  ->
                   fun g  ->
                     goal_to_string "SMT Goal"
                       (FStar_Pervasives_Native.Some
                          ((((Prims.parse_int "1") + n_active) + i), n1)) ps
                       g) ps.FStar_Tactics_Types.smt_goals
               in
            FStar_List.append uu____69473 uu____69493  in
          FStar_List.append uu____69425 uu____69469  in
        FStar_String.concat "" uu____69421
  
let (goal_to_json : FStar_Tactics_Types.goal -> FStar_Util.json) =
  fun g  ->
    let g_binders =
      let uu____69527 =
        let uu____69528 = FStar_Tactics_Types.goal_env g  in
        FStar_TypeChecker_Env.all_binders uu____69528  in
      let uu____69529 =
        let uu____69534 =
          let uu____69535 = FStar_Tactics_Types.goal_env g  in
          FStar_TypeChecker_Env.dsenv uu____69535  in
        FStar_Syntax_Print.binders_to_json uu____69534  in
      FStar_All.pipe_right uu____69527 uu____69529  in
    let uu____69536 =
      let uu____69544 =
        let uu____69552 =
          let uu____69558 =
            let uu____69559 =
              let uu____69567 =
                let uu____69573 =
                  let uu____69574 =
                    let uu____69576 = FStar_Tactics_Types.goal_env g  in
                    let uu____69577 = FStar_Tactics_Types.goal_witness g  in
                    tts uu____69576 uu____69577  in
                  FStar_Util.JsonStr uu____69574  in
                ("witness", uu____69573)  in
              let uu____69580 =
                let uu____69588 =
                  let uu____69594 =
                    let uu____69595 =
                      let uu____69597 = FStar_Tactics_Types.goal_env g  in
                      let uu____69598 = FStar_Tactics_Types.goal_type g  in
                      tts uu____69597 uu____69598  in
                    FStar_Util.JsonStr uu____69595  in
                  ("type", uu____69594)  in
                [uu____69588;
                ("label", (FStar_Util.JsonStr (g.FStar_Tactics_Types.label)))]
                 in
              uu____69567 :: uu____69580  in
            FStar_Util.JsonAssoc uu____69559  in
          ("goal", uu____69558)  in
        [uu____69552]  in
      ("hyps", g_binders) :: uu____69544  in
    FStar_Util.JsonAssoc uu____69536
  
let (ps_to_json :
  (Prims.string * FStar_Tactics_Types.proofstate) -> FStar_Util.json) =
  fun uu____69652  ->
    match uu____69652 with
    | (msg,ps) ->
        let uu____69662 =
          let uu____69670 =
            let uu____69678 =
              let uu____69686 =
                let uu____69694 =
                  let uu____69700 =
                    let uu____69701 =
                      FStar_List.map goal_to_json
                        ps.FStar_Tactics_Types.goals
                       in
                    FStar_Util.JsonList uu____69701  in
                  ("goals", uu____69700)  in
                let uu____69706 =
                  let uu____69714 =
                    let uu____69720 =
                      let uu____69721 =
                        FStar_List.map goal_to_json
                          ps.FStar_Tactics_Types.smt_goals
                         in
                      FStar_Util.JsonList uu____69721  in
                    ("smt-goals", uu____69720)  in
                  [uu____69714]  in
                uu____69694 :: uu____69706  in
              ("depth", (FStar_Util.JsonInt (ps.FStar_Tactics_Types.depth)))
                :: uu____69686
               in
            ("label", (FStar_Util.JsonStr msg)) :: uu____69678  in
          let uu____69755 =
            if ps.FStar_Tactics_Types.entry_range <> FStar_Range.dummyRange
            then
              let uu____69771 =
                let uu____69777 =
                  FStar_Range.json_of_def_range
                    ps.FStar_Tactics_Types.entry_range
                   in
                ("location", uu____69777)  in
              [uu____69771]
            else []  in
          FStar_List.append uu____69670 uu____69755  in
        FStar_Util.JsonAssoc uu____69662
  
let (dump_proofstate :
  FStar_Tactics_Types.proofstate -> Prims.string -> unit) =
  fun ps  ->
    fun msg  ->
      FStar_Options.with_saved_options
        (fun uu____69817  ->
           FStar_Options.set_option "print_effect_args"
             (FStar_Options.Bool true);
           FStar_Util.print_generic "proof-state" ps_to_string ps_to_json
             (msg, ps))
  
let (print_proof_state : Prims.string -> unit tac) =
  fun msg  ->
    mk_tac
      (fun ps  ->
         let psc = ps.FStar_Tactics_Types.psc  in
         let subst1 = FStar_TypeChecker_Cfg.psc_subst psc  in
         (let uu____69848 = FStar_Tactics_Types.subst_proof_state subst1 ps
             in
          dump_proofstate uu____69848 msg);
         FStar_Tactics_Result.Success ((), ps))
  
let mlog : 'a . (unit -> unit) -> (unit -> 'a tac) -> 'a tac =
  fun f  -> fun cont  -> bind get (fun ps  -> log ps f; cont ()) 
let traise : 'a . Prims.exn -> 'a tac =
  fun e  -> mk_tac (fun ps  -> FStar_Tactics_Result.Failed (e, ps)) 
let fail : 'a . Prims.string -> 'a tac =
  fun msg  ->
    mk_tac
      (fun ps  ->
         (let uu____69921 =
            FStar_TypeChecker_Env.debug ps.FStar_Tactics_Types.main_context
              (FStar_Options.Other "TacFail")
             in
          if uu____69921
          then dump_proofstate ps (Prims.op_Hat "TACTIC FAILING: " msg)
          else ());
         FStar_Tactics_Result.Failed
           ((FStar_Tactics_Types.TacticFailure msg), ps))
  
let fail1 : 'Auu____69935 . Prims.string -> Prims.string -> 'Auu____69935 tac
  =
  fun msg  ->
    fun x  -> let uu____69952 = FStar_Util.format1 msg x  in fail uu____69952
  
let fail2 :
  'Auu____69963 .
    Prims.string -> Prims.string -> Prims.string -> 'Auu____69963 tac
  =
  fun msg  ->
    fun x  ->
      fun y  ->
        let uu____69987 = FStar_Util.format2 msg x y  in fail uu____69987
  
let fail3 :
  'Auu____70000 .
    Prims.string ->
      Prims.string -> Prims.string -> Prims.string -> 'Auu____70000 tac
  =
  fun msg  ->
    fun x  ->
      fun y  ->
        fun z  ->
          let uu____70031 = FStar_Util.format3 msg x y z  in fail uu____70031
  
let fail4 :
  'Auu____70046 .
    Prims.string ->
      Prims.string ->
        Prims.string -> Prims.string -> Prims.string -> 'Auu____70046 tac
  =
  fun msg  ->
    fun x  ->
      fun y  ->
        fun z  ->
          fun w  ->
            let uu____70084 = FStar_Util.format4 msg x y z w  in
            fail uu____70084
  
let catch : 'a . 'a tac -> (Prims.exn,'a) FStar_Util.either tac =
  fun t  ->
    mk_tac
      (fun ps  ->
         let tx = FStar_Syntax_Unionfind.new_transaction ()  in
         let uu____70119 = run t ps  in
         match uu____70119 with
         | FStar_Tactics_Result.Success (a,q) ->
             (FStar_Syntax_Unionfind.commit tx;
              FStar_Tactics_Result.Success ((FStar_Util.Inr a), q))
         | FStar_Tactics_Result.Failed (m,q) ->
             (FStar_Syntax_Unionfind.rollback tx;
              (let ps1 =
                 let uu___802_70143 = ps  in
                 {
                   FStar_Tactics_Types.main_context =
                     (uu___802_70143.FStar_Tactics_Types.main_context);
                   FStar_Tactics_Types.main_goal =
                     (uu___802_70143.FStar_Tactics_Types.main_goal);
                   FStar_Tactics_Types.all_implicits =
                     (uu___802_70143.FStar_Tactics_Types.all_implicits);
                   FStar_Tactics_Types.goals =
                     (uu___802_70143.FStar_Tactics_Types.goals);
                   FStar_Tactics_Types.smt_goals =
                     (uu___802_70143.FStar_Tactics_Types.smt_goals);
                   FStar_Tactics_Types.depth =
                     (uu___802_70143.FStar_Tactics_Types.depth);
                   FStar_Tactics_Types.__dump =
                     (uu___802_70143.FStar_Tactics_Types.__dump);
                   FStar_Tactics_Types.psc =
                     (uu___802_70143.FStar_Tactics_Types.psc);
                   FStar_Tactics_Types.entry_range =
                     (uu___802_70143.FStar_Tactics_Types.entry_range);
                   FStar_Tactics_Types.guard_policy =
                     (uu___802_70143.FStar_Tactics_Types.guard_policy);
                   FStar_Tactics_Types.freshness =
                     (q.FStar_Tactics_Types.freshness);
                   FStar_Tactics_Types.tac_verb_dbg =
                     (uu___802_70143.FStar_Tactics_Types.tac_verb_dbg);
                   FStar_Tactics_Types.local_state =
                     (uu___802_70143.FStar_Tactics_Types.local_state)
                 }  in
               FStar_Tactics_Result.Success ((FStar_Util.Inl m), ps1))))
  
let recover : 'a . 'a tac -> (Prims.exn,'a) FStar_Util.either tac =
  fun t  ->
    mk_tac
      (fun ps  ->
         let uu____70182 = run t ps  in
         match uu____70182 with
         | FStar_Tactics_Result.Success (a,q) ->
             FStar_Tactics_Result.Success ((FStar_Util.Inr a), q)
         | FStar_Tactics_Result.Failed (m,q) ->
             FStar_Tactics_Result.Success ((FStar_Util.Inl m), q))
  
let trytac : 'a . 'a tac -> 'a FStar_Pervasives_Native.option tac =
  fun t  ->
    let uu____70230 = catch t  in
    bind uu____70230
      (fun r  ->
         match r with
         | FStar_Util.Inr v1 -> ret (FStar_Pervasives_Native.Some v1)
         | FStar_Util.Inl uu____70257 -> ret FStar_Pervasives_Native.None)
  
let trytac_exn : 'a . 'a tac -> 'a FStar_Pervasives_Native.option tac =
  fun t  ->
    mk_tac
      (fun ps  ->
         try
           (fun uu___828_70289  ->
              match () with
              | () -> let uu____70294 = trytac t  in run uu____70294 ps) ()
         with
         | FStar_Errors.Err (uu____70310,msg) ->
             (log ps
                (fun uu____70316  ->
                   FStar_Util.print1 "trytac_exn error: (%s)" msg);
              FStar_Tactics_Result.Success (FStar_Pervasives_Native.None, ps))
         | FStar_Errors.Error (uu____70322,msg,uu____70324) ->
             (log ps
                (fun uu____70329  ->
                   FStar_Util.print1 "trytac_exn error: (%s)" msg);
              FStar_Tactics_Result.Success (FStar_Pervasives_Native.None, ps)))
  
let wrap_err : 'a . Prims.string -> 'a tac -> 'a tac =
  fun pref  ->
    fun t  ->
      mk_tac
        (fun ps  ->
           let uu____70366 = run t ps  in
           match uu____70366 with
           | FStar_Tactics_Result.Success (a,q) ->
               FStar_Tactics_Result.Success (a, q)
           | FStar_Tactics_Result.Failed
               (FStar_Tactics_Types.TacticFailure msg,q) ->
               FStar_Tactics_Result.Failed
                 ((FStar_Tactics_Types.TacticFailure
                     (Prims.op_Hat pref (Prims.op_Hat ": " msg))), q)
           | FStar_Tactics_Result.Failed (e,q) ->
               FStar_Tactics_Result.Failed (e, q))
  
let (set : FStar_Tactics_Types.proofstate -> unit tac) =
  fun p  -> mk_tac (fun uu____70390  -> FStar_Tactics_Result.Success ((), p)) 
let (add_implicits : implicits -> unit tac) =
  fun i  ->
    bind get
      (fun p  ->
         set
           (let uu___863_70405 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___863_70405.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___863_70405.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (FStar_List.append i p.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___863_70405.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (uu___863_70405.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___863_70405.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___863_70405.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___863_70405.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___863_70405.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___863_70405.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___863_70405.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___863_70405.FStar_Tactics_Types.tac_verb_dbg);
              FStar_Tactics_Types.local_state =
                (uu___863_70405.FStar_Tactics_Types.local_state)
            }))
  
let (__do_unify :
  env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.bool tac)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        (let uu____70429 =
           FStar_TypeChecker_Env.debug env (FStar_Options.Other "1346")  in
         if uu____70429
         then
           let uu____70433 = FStar_Syntax_Print.term_to_string t1  in
           let uu____70435 = FStar_Syntax_Print.term_to_string t2  in
           FStar_Util.print2 "%%%%%%%%do_unify %s =? %s\n" uu____70433
             uu____70435
         else ());
        (try
           (fun uu___871_70446  ->
              match () with
              | () ->
                  let res = FStar_TypeChecker_Rel.teq_nosmt env t1 t2  in
                  ((let uu____70454 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "1346")
                       in
                    if uu____70454
                    then
                      let uu____70458 =
                        FStar_Common.string_of_option
                          (FStar_TypeChecker_Rel.guard_to_string env) res
                         in
                      let uu____70460 = FStar_Syntax_Print.term_to_string t1
                         in
                      let uu____70462 = FStar_Syntax_Print.term_to_string t2
                         in
                      FStar_Util.print3
                        "%%%%%%%%do_unify (RESULT %s) %s =? %s\n" uu____70458
                        uu____70460 uu____70462
                    else ());
                   (match res with
                    | FStar_Pervasives_Native.None  -> ret false
                    | FStar_Pervasives_Native.Some g ->
                        let uu____70473 =
                          add_implicits g.FStar_TypeChecker_Env.implicits  in
                        bind uu____70473 (fun uu____70478  -> ret true)))) ()
         with
         | FStar_Errors.Err (uu____70488,msg) ->
             mlog
               (fun uu____70494  ->
                  FStar_Util.print1 ">> do_unify error, (%s)\n" msg)
               (fun uu____70497  -> ret false)
         | FStar_Errors.Error (uu____70500,msg,r) ->
             mlog
               (fun uu____70508  ->
                  let uu____70509 = FStar_Range.string_of_range r  in
                  FStar_Util.print2 ">> do_unify error, (%s) at (%s)\n" msg
                    uu____70509) (fun uu____70513  -> ret false))
  
let (compress_implicits : unit tac) =
  bind get
    (fun ps  ->
       let imps = ps.FStar_Tactics_Types.all_implicits  in
       let g =
         let uu___897_70527 = FStar_TypeChecker_Env.trivial_guard  in
         {
           FStar_TypeChecker_Env.guard_f =
             (uu___897_70527.FStar_TypeChecker_Env.guard_f);
           FStar_TypeChecker_Env.deferred =
             (uu___897_70527.FStar_TypeChecker_Env.deferred);
           FStar_TypeChecker_Env.univ_ineqs =
             (uu___897_70527.FStar_TypeChecker_Env.univ_ineqs);
           FStar_TypeChecker_Env.implicits = imps
         }  in
       let g1 =
         FStar_TypeChecker_Rel.resolve_implicits_tac
           ps.FStar_Tactics_Types.main_context g
          in
       let ps' =
         let uu___901_70530 = ps  in
         {
           FStar_Tactics_Types.main_context =
             (uu___901_70530.FStar_Tactics_Types.main_context);
           FStar_Tactics_Types.main_goal =
             (uu___901_70530.FStar_Tactics_Types.main_goal);
           FStar_Tactics_Types.all_implicits =
             (g1.FStar_TypeChecker_Env.implicits);
           FStar_Tactics_Types.goals =
             (uu___901_70530.FStar_Tactics_Types.goals);
           FStar_Tactics_Types.smt_goals =
             (uu___901_70530.FStar_Tactics_Types.smt_goals);
           FStar_Tactics_Types.depth =
             (uu___901_70530.FStar_Tactics_Types.depth);
           FStar_Tactics_Types.__dump =
             (uu___901_70530.FStar_Tactics_Types.__dump);
           FStar_Tactics_Types.psc = (uu___901_70530.FStar_Tactics_Types.psc);
           FStar_Tactics_Types.entry_range =
             (uu___901_70530.FStar_Tactics_Types.entry_range);
           FStar_Tactics_Types.guard_policy =
             (uu___901_70530.FStar_Tactics_Types.guard_policy);
           FStar_Tactics_Types.freshness =
             (uu___901_70530.FStar_Tactics_Types.freshness);
           FStar_Tactics_Types.tac_verb_dbg =
             (uu___901_70530.FStar_Tactics_Types.tac_verb_dbg);
           FStar_Tactics_Types.local_state =
             (uu___901_70530.FStar_Tactics_Types.local_state)
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
          (fun uu____70557  ->
             (let uu____70559 =
                FStar_TypeChecker_Env.debug env (FStar_Options.Other "1346")
                 in
              if uu____70559
              then
                (FStar_Options.push ();
                 (let uu____70564 =
                    FStar_Options.set_options FStar_Options.Set
                      "--debug_level Rel --debug_level RelCheck"
                     in
                  ()))
              else ());
             (let uu____70568 = __do_unify env t1 t2  in
              bind uu____70568
                (fun r  ->
                   (let uu____70579 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "1346")
                       in
                    if uu____70579 then FStar_Options.pop () else ());
                   ret r)))
  
let (remove_solved_goals : unit tac) =
  bind get
    (fun ps  ->
       let ps' =
         let uu___916_70593 = ps  in
         let uu____70594 =
           FStar_List.filter
             (fun g  ->
                let uu____70600 = check_goal_solved g  in
                FStar_Option.isNone uu____70600) ps.FStar_Tactics_Types.goals
            in
         {
           FStar_Tactics_Types.main_context =
             (uu___916_70593.FStar_Tactics_Types.main_context);
           FStar_Tactics_Types.main_goal =
             (uu___916_70593.FStar_Tactics_Types.main_goal);
           FStar_Tactics_Types.all_implicits =
             (uu___916_70593.FStar_Tactics_Types.all_implicits);
           FStar_Tactics_Types.goals = uu____70594;
           FStar_Tactics_Types.smt_goals =
             (uu___916_70593.FStar_Tactics_Types.smt_goals);
           FStar_Tactics_Types.depth =
             (uu___916_70593.FStar_Tactics_Types.depth);
           FStar_Tactics_Types.__dump =
             (uu___916_70593.FStar_Tactics_Types.__dump);
           FStar_Tactics_Types.psc = (uu___916_70593.FStar_Tactics_Types.psc);
           FStar_Tactics_Types.entry_range =
             (uu___916_70593.FStar_Tactics_Types.entry_range);
           FStar_Tactics_Types.guard_policy =
             (uu___916_70593.FStar_Tactics_Types.guard_policy);
           FStar_Tactics_Types.freshness =
             (uu___916_70593.FStar_Tactics_Types.freshness);
           FStar_Tactics_Types.tac_verb_dbg =
             (uu___916_70593.FStar_Tactics_Types.tac_verb_dbg);
           FStar_Tactics_Types.local_state =
             (uu___916_70593.FStar_Tactics_Types.local_state)
         }  in
       set ps')
  
let (set_solution :
  FStar_Tactics_Types.goal -> FStar_Syntax_Syntax.term -> unit tac) =
  fun goal  ->
    fun solution  ->
      let uu____70618 =
        FStar_Syntax_Unionfind.find
          (goal.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_head
         in
      match uu____70618 with
      | FStar_Pervasives_Native.Some uu____70623 ->
          let uu____70624 =
            let uu____70626 = goal_to_string_verbose goal  in
            FStar_Util.format1 "Goal %s is already solved" uu____70626  in
          fail uu____70624
      | FStar_Pervasives_Native.None  ->
          (FStar_Syntax_Unionfind.change
             (goal.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_head
             solution;
           ret ())
  
let (trysolve :
  FStar_Tactics_Types.goal -> FStar_Syntax_Syntax.term -> Prims.bool tac) =
  fun goal  ->
    fun solution  ->
      let uu____70647 = FStar_Tactics_Types.goal_env goal  in
      let uu____70648 = FStar_Tactics_Types.goal_witness goal  in
      do_unify uu____70647 solution uu____70648
  
let (__dismiss : unit tac) =
  bind get
    (fun p  ->
       let uu____70655 =
         let uu___929_70656 = p  in
         let uu____70657 = FStar_List.tl p.FStar_Tactics_Types.goals  in
         {
           FStar_Tactics_Types.main_context =
             (uu___929_70656.FStar_Tactics_Types.main_context);
           FStar_Tactics_Types.main_goal =
             (uu___929_70656.FStar_Tactics_Types.main_goal);
           FStar_Tactics_Types.all_implicits =
             (uu___929_70656.FStar_Tactics_Types.all_implicits);
           FStar_Tactics_Types.goals = uu____70657;
           FStar_Tactics_Types.smt_goals =
             (uu___929_70656.FStar_Tactics_Types.smt_goals);
           FStar_Tactics_Types.depth =
             (uu___929_70656.FStar_Tactics_Types.depth);
           FStar_Tactics_Types.__dump =
             (uu___929_70656.FStar_Tactics_Types.__dump);
           FStar_Tactics_Types.psc = (uu___929_70656.FStar_Tactics_Types.psc);
           FStar_Tactics_Types.entry_range =
             (uu___929_70656.FStar_Tactics_Types.entry_range);
           FStar_Tactics_Types.guard_policy =
             (uu___929_70656.FStar_Tactics_Types.guard_policy);
           FStar_Tactics_Types.freshness =
             (uu___929_70656.FStar_Tactics_Types.freshness);
           FStar_Tactics_Types.tac_verb_dbg =
             (uu___929_70656.FStar_Tactics_Types.tac_verb_dbg);
           FStar_Tactics_Types.local_state =
             (uu___929_70656.FStar_Tactics_Types.local_state)
         }  in
       set uu____70655)
  
let (solve :
  FStar_Tactics_Types.goal -> FStar_Syntax_Syntax.term -> unit tac) =
  fun goal  ->
    fun solution  ->
      let e = FStar_Tactics_Types.goal_env goal  in
      mlog
        (fun uu____70679  ->
           let uu____70680 =
             let uu____70682 = FStar_Tactics_Types.goal_witness goal  in
             FStar_Syntax_Print.term_to_string uu____70682  in
           let uu____70683 = FStar_Syntax_Print.term_to_string solution  in
           FStar_Util.print2 "solve %s := %s\n" uu____70680 uu____70683)
        (fun uu____70688  ->
           let uu____70689 = trysolve goal solution  in
           bind uu____70689
             (fun b  ->
                if b
                then bind __dismiss (fun uu____70701  -> remove_solved_goals)
                else
                  (let uu____70704 =
                     let uu____70706 =
                       let uu____70708 = FStar_Tactics_Types.goal_env goal
                          in
                       tts uu____70708 solution  in
                     let uu____70709 =
                       let uu____70711 = FStar_Tactics_Types.goal_env goal
                          in
                       let uu____70712 =
                         FStar_Tactics_Types.goal_witness goal  in
                       tts uu____70711 uu____70712  in
                     let uu____70713 =
                       let uu____70715 = FStar_Tactics_Types.goal_env goal
                          in
                       let uu____70716 = FStar_Tactics_Types.goal_type goal
                          in
                       tts uu____70715 uu____70716  in
                     FStar_Util.format3 "%s does not solve %s : %s"
                       uu____70706 uu____70709 uu____70713
                      in
                   fail uu____70704)))
  
let (solve' :
  FStar_Tactics_Types.goal -> FStar_Syntax_Syntax.term -> unit tac) =
  fun goal  ->
    fun solution  ->
      let uu____70733 = set_solution goal solution  in
      bind uu____70733
        (fun uu____70737  ->
           bind __dismiss (fun uu____70739  -> remove_solved_goals))
  
let (set_goals : FStar_Tactics_Types.goal Prims.list -> unit tac) =
  fun gs  ->
    bind get
      (fun ps  ->
         set
           (let uu___945_70758 = ps  in
            {
              FStar_Tactics_Types.main_context =
                (uu___945_70758.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___945_70758.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___945_70758.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals = gs;
              FStar_Tactics_Types.smt_goals =
                (uu___945_70758.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___945_70758.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___945_70758.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___945_70758.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___945_70758.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___945_70758.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___945_70758.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___945_70758.FStar_Tactics_Types.tac_verb_dbg);
              FStar_Tactics_Types.local_state =
                (uu___945_70758.FStar_Tactics_Types.local_state)
            }))
  
let (set_smt_goals : FStar_Tactics_Types.goal Prims.list -> unit tac) =
  fun gs  ->
    bind get
      (fun ps  ->
         set
           (let uu___949_70777 = ps  in
            {
              FStar_Tactics_Types.main_context =
                (uu___949_70777.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___949_70777.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___949_70777.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___949_70777.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals = gs;
              FStar_Tactics_Types.depth =
                (uu___949_70777.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___949_70777.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___949_70777.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___949_70777.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___949_70777.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___949_70777.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___949_70777.FStar_Tactics_Types.tac_verb_dbg);
              FStar_Tactics_Types.local_state =
                (uu___949_70777.FStar_Tactics_Types.local_state)
            }))
  
let (dismiss_all : unit tac) = set_goals [] 
let (nwarn : Prims.int FStar_ST.ref) =
  FStar_Util.mk_ref (Prims.parse_int "0") 
let (check_valid_goal : FStar_Tactics_Types.goal -> unit) =
  fun g  ->
    let uu____70804 = FStar_Options.defensive ()  in
    if uu____70804
    then
      let b = true  in
      let env = FStar_Tactics_Types.goal_env g  in
      let b1 =
        b &&
          (let uu____70814 = FStar_Tactics_Types.goal_witness g  in
           FStar_TypeChecker_Env.closed env uu____70814)
         in
      let b2 =
        b1 &&
          (let uu____70818 = FStar_Tactics_Types.goal_type g  in
           FStar_TypeChecker_Env.closed env uu____70818)
         in
      let rec aux b3 e =
        let uu____70833 = FStar_TypeChecker_Env.pop_bv e  in
        match uu____70833 with
        | FStar_Pervasives_Native.None  -> b3
        | FStar_Pervasives_Native.Some (bv,e1) ->
            let b4 =
              b3 &&
                (FStar_TypeChecker_Env.closed e1 bv.FStar_Syntax_Syntax.sort)
               in
            aux b4 e1
         in
      let uu____70853 =
        (let uu____70857 = aux b2 env  in Prims.op_Negation uu____70857) &&
          (let uu____70860 = FStar_ST.op_Bang nwarn  in
           uu____70860 < (Prims.parse_int "5"))
         in
      (if uu____70853
       then
         ((let uu____70886 =
             let uu____70887 = FStar_Tactics_Types.goal_type g  in
             uu____70887.FStar_Syntax_Syntax.pos  in
           let uu____70890 =
             let uu____70896 =
               let uu____70898 = goal_to_string_verbose g  in
               FStar_Util.format1
                 "The following goal is ill-formed. Keeping calm and carrying on...\n<%s>\n\n"
                 uu____70898
                in
             (FStar_Errors.Warning_IllFormedGoal, uu____70896)  in
           FStar_Errors.log_issue uu____70886 uu____70890);
          (let uu____70902 =
             let uu____70904 = FStar_ST.op_Bang nwarn  in
             uu____70904 + (Prims.parse_int "1")  in
           FStar_ST.op_Colon_Equals nwarn uu____70902))
       else ())
    else ()
  
let (add_goals : FStar_Tactics_Types.goal Prims.list -> unit tac) =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___971_70973 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___971_70973.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___971_70973.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___971_70973.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (FStar_List.append gs p.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (uu___971_70973.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___971_70973.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___971_70973.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___971_70973.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___971_70973.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___971_70973.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___971_70973.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___971_70973.FStar_Tactics_Types.tac_verb_dbg);
              FStar_Tactics_Types.local_state =
                (uu___971_70973.FStar_Tactics_Types.local_state)
            }))
  
let (add_smt_goals : FStar_Tactics_Types.goal Prims.list -> unit tac) =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___976_70994 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___976_70994.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___976_70994.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___976_70994.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___976_70994.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (FStar_List.append gs p.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___976_70994.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___976_70994.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___976_70994.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___976_70994.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___976_70994.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___976_70994.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___976_70994.FStar_Tactics_Types.tac_verb_dbg);
              FStar_Tactics_Types.local_state =
                (uu___976_70994.FStar_Tactics_Types.local_state)
            }))
  
let (push_goals : FStar_Tactics_Types.goal Prims.list -> unit tac) =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___981_71015 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___981_71015.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___981_71015.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___981_71015.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (FStar_List.append p.FStar_Tactics_Types.goals gs);
              FStar_Tactics_Types.smt_goals =
                (uu___981_71015.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___981_71015.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___981_71015.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___981_71015.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___981_71015.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___981_71015.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___981_71015.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___981_71015.FStar_Tactics_Types.tac_verb_dbg);
              FStar_Tactics_Types.local_state =
                (uu___981_71015.FStar_Tactics_Types.local_state)
            }))
  
let (push_smt_goals : FStar_Tactics_Types.goal Prims.list -> unit tac) =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___986_71036 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___986_71036.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___986_71036.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___986_71036.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___986_71036.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (FStar_List.append p.FStar_Tactics_Types.smt_goals gs);
              FStar_Tactics_Types.depth =
                (uu___986_71036.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___986_71036.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___986_71036.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___986_71036.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___986_71036.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___986_71036.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___986_71036.FStar_Tactics_Types.tac_verb_dbg);
              FStar_Tactics_Types.local_state =
                (uu___986_71036.FStar_Tactics_Types.local_state)
            }))
  
let (replace_cur : FStar_Tactics_Types.goal -> unit tac) =
  fun g  -> bind __dismiss (fun uu____71048  -> add_goals [g]) 
let (new_uvar :
  Prims.string ->
    env ->
      FStar_Reflection_Data.typ ->
        (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.ctx_uvar) tac)
  =
  fun reason  ->
    fun env  ->
      fun typ  ->
        let uu____71079 =
          FStar_TypeChecker_Env.new_implicit_var_aux reason
            typ.FStar_Syntax_Syntax.pos env typ
            FStar_Syntax_Syntax.Allow_untyped FStar_Pervasives_Native.None
           in
        match uu____71079 with
        | (u,ctx_uvar,g_u) ->
            let uu____71117 =
              add_implicits g_u.FStar_TypeChecker_Env.implicits  in
            bind uu____71117
              (fun uu____71126  ->
                 let uu____71127 =
                   let uu____71132 =
                     let uu____71133 = FStar_List.hd ctx_uvar  in
                     FStar_Pervasives_Native.fst uu____71133  in
                   (u, uu____71132)  in
                 ret uu____71127)
  
let (is_true : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____71154 = FStar_Syntax_Util.un_squash t1  in
    match uu____71154 with
    | FStar_Pervasives_Native.Some t' ->
        let t'1 = FStar_Syntax_Util.unascribe t'  in
        let uu____71166 =
          let uu____71167 = FStar_Syntax_Subst.compress t'1  in
          uu____71167.FStar_Syntax_Syntax.n  in
        (match uu____71166 with
         | FStar_Syntax_Syntax.Tm_fvar fv ->
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.true_lid
         | uu____71172 -> false)
    | uu____71174 -> false
  
let (is_false : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____71187 = FStar_Syntax_Util.un_squash t  in
    match uu____71187 with
    | FStar_Pervasives_Native.Some t' ->
        let uu____71198 =
          let uu____71199 = FStar_Syntax_Subst.compress t'  in
          uu____71199.FStar_Syntax_Syntax.n  in
        (match uu____71198 with
         | FStar_Syntax_Syntax.Tm_fvar fv ->
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.false_lid
         | uu____71204 -> false)
    | uu____71206 -> false
  
let (cur_goal : unit -> FStar_Tactics_Types.goal tac) =
  fun uu____71219  ->
    bind get
      (fun p  ->
         match p.FStar_Tactics_Types.goals with
         | [] -> fail "No more goals (1)"
         | hd1::tl1 ->
             let uu____71231 =
               FStar_Syntax_Unionfind.find
                 (hd1.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_head
                in
             (match uu____71231 with
              | FStar_Pervasives_Native.None  -> ret hd1
              | FStar_Pervasives_Native.Some t ->
                  ((let uu____71238 = goal_to_string_verbose hd1  in
                    let uu____71240 = FStar_Syntax_Print.term_to_string t  in
                    FStar_Util.print2
                      "!!!!!!!!!!!! GOAL IS ALREADY SOLVED! %s\nsol is %s\n"
                      uu____71238 uu____71240);
                   ret hd1)))
  
let (tadmit_t : FStar_Syntax_Syntax.term -> unit tac) =
  fun t  ->
    let uu____71253 =
      bind get
        (fun ps  ->
           let uu____71259 = cur_goal ()  in
           bind uu____71259
             (fun g  ->
                (let uu____71266 =
                   let uu____71267 = FStar_Tactics_Types.goal_type g  in
                   uu____71267.FStar_Syntax_Syntax.pos  in
                 let uu____71270 =
                   let uu____71276 =
                     let uu____71278 =
                       goal_to_string "" FStar_Pervasives_Native.None ps g
                        in
                     FStar_Util.format1 "Tactics admitted goal <%s>\n\n"
                       uu____71278
                      in
                   (FStar_Errors.Warning_TacAdmit, uu____71276)  in
                 FStar_Errors.log_issue uu____71266 uu____71270);
                solve' g t))
       in
    FStar_All.pipe_left (wrap_err "tadmit_t") uu____71253
  
let (fresh : unit -> FStar_BigInt.t tac) =
  fun uu____71301  ->
    bind get
      (fun ps  ->
         let n1 = ps.FStar_Tactics_Types.freshness  in
         let ps1 =
           let uu___1031_71312 = ps  in
           {
             FStar_Tactics_Types.main_context =
               (uu___1031_71312.FStar_Tactics_Types.main_context);
             FStar_Tactics_Types.main_goal =
               (uu___1031_71312.FStar_Tactics_Types.main_goal);
             FStar_Tactics_Types.all_implicits =
               (uu___1031_71312.FStar_Tactics_Types.all_implicits);
             FStar_Tactics_Types.goals =
               (uu___1031_71312.FStar_Tactics_Types.goals);
             FStar_Tactics_Types.smt_goals =
               (uu___1031_71312.FStar_Tactics_Types.smt_goals);
             FStar_Tactics_Types.depth =
               (uu___1031_71312.FStar_Tactics_Types.depth);
             FStar_Tactics_Types.__dump =
               (uu___1031_71312.FStar_Tactics_Types.__dump);
             FStar_Tactics_Types.psc =
               (uu___1031_71312.FStar_Tactics_Types.psc);
             FStar_Tactics_Types.entry_range =
               (uu___1031_71312.FStar_Tactics_Types.entry_range);
             FStar_Tactics_Types.guard_policy =
               (uu___1031_71312.FStar_Tactics_Types.guard_policy);
             FStar_Tactics_Types.freshness = (n1 + (Prims.parse_int "1"));
             FStar_Tactics_Types.tac_verb_dbg =
               (uu___1031_71312.FStar_Tactics_Types.tac_verb_dbg);
             FStar_Tactics_Types.local_state =
               (uu___1031_71312.FStar_Tactics_Types.local_state)
           }  in
         let uu____71314 = set ps1  in
         bind uu____71314
           (fun uu____71319  ->
              let uu____71320 = FStar_BigInt.of_int_fs n1  in ret uu____71320))
  
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
              let uu____71358 = env.FStar_TypeChecker_Env.universe_of env phi
                 in
              FStar_Syntax_Util.mk_squash uu____71358 phi  in
            let uu____71359 = new_uvar reason env typ  in
            bind uu____71359
              (fun uu____71374  ->
                 match uu____71374 with
                 | (uu____71381,ctx_uvar) ->
                     let goal =
                       FStar_Tactics_Types.mk_goal env ctx_uvar opts false
                         label1
                        in
                     ret goal)
  
let (__tc :
  env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term * FStar_Reflection_Data.typ *
        FStar_TypeChecker_Env.guard_t) tac)
  =
  fun e  ->
    fun t  ->
      bind get
        (fun ps  ->
           mlog
             (fun uu____71428  ->
                let uu____71429 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.print1 "Tac> __tc(%s)\n" uu____71429)
             (fun uu____71434  ->
                let e1 =
                  let uu___1049_71436 = e  in
                  {
                    FStar_TypeChecker_Env.solver =
                      (uu___1049_71436.FStar_TypeChecker_Env.solver);
                    FStar_TypeChecker_Env.range =
                      (uu___1049_71436.FStar_TypeChecker_Env.range);
                    FStar_TypeChecker_Env.curmodule =
                      (uu___1049_71436.FStar_TypeChecker_Env.curmodule);
                    FStar_TypeChecker_Env.gamma =
                      (uu___1049_71436.FStar_TypeChecker_Env.gamma);
                    FStar_TypeChecker_Env.gamma_sig =
                      (uu___1049_71436.FStar_TypeChecker_Env.gamma_sig);
                    FStar_TypeChecker_Env.gamma_cache =
                      (uu___1049_71436.FStar_TypeChecker_Env.gamma_cache);
                    FStar_TypeChecker_Env.modules =
                      (uu___1049_71436.FStar_TypeChecker_Env.modules);
                    FStar_TypeChecker_Env.expected_typ =
                      (uu___1049_71436.FStar_TypeChecker_Env.expected_typ);
                    FStar_TypeChecker_Env.sigtab =
                      (uu___1049_71436.FStar_TypeChecker_Env.sigtab);
                    FStar_TypeChecker_Env.attrtab =
                      (uu___1049_71436.FStar_TypeChecker_Env.attrtab);
                    FStar_TypeChecker_Env.is_pattern =
                      (uu___1049_71436.FStar_TypeChecker_Env.is_pattern);
                    FStar_TypeChecker_Env.instantiate_imp =
                      (uu___1049_71436.FStar_TypeChecker_Env.instantiate_imp);
                    FStar_TypeChecker_Env.effects =
                      (uu___1049_71436.FStar_TypeChecker_Env.effects);
                    FStar_TypeChecker_Env.generalize =
                      (uu___1049_71436.FStar_TypeChecker_Env.generalize);
                    FStar_TypeChecker_Env.letrecs =
                      (uu___1049_71436.FStar_TypeChecker_Env.letrecs);
                    FStar_TypeChecker_Env.top_level =
                      (uu___1049_71436.FStar_TypeChecker_Env.top_level);
                    FStar_TypeChecker_Env.check_uvars =
                      (uu___1049_71436.FStar_TypeChecker_Env.check_uvars);
                    FStar_TypeChecker_Env.use_eq =
                      (uu___1049_71436.FStar_TypeChecker_Env.use_eq);
                    FStar_TypeChecker_Env.is_iface =
                      (uu___1049_71436.FStar_TypeChecker_Env.is_iface);
                    FStar_TypeChecker_Env.admit =
                      (uu___1049_71436.FStar_TypeChecker_Env.admit);
                    FStar_TypeChecker_Env.lax =
                      (uu___1049_71436.FStar_TypeChecker_Env.lax);
                    FStar_TypeChecker_Env.lax_universes =
                      (uu___1049_71436.FStar_TypeChecker_Env.lax_universes);
                    FStar_TypeChecker_Env.phase1 =
                      (uu___1049_71436.FStar_TypeChecker_Env.phase1);
                    FStar_TypeChecker_Env.failhard =
                      (uu___1049_71436.FStar_TypeChecker_Env.failhard);
                    FStar_TypeChecker_Env.nosynth =
                      (uu___1049_71436.FStar_TypeChecker_Env.nosynth);
                    FStar_TypeChecker_Env.uvar_subtyping = false;
                    FStar_TypeChecker_Env.tc_term =
                      (uu___1049_71436.FStar_TypeChecker_Env.tc_term);
                    FStar_TypeChecker_Env.type_of =
                      (uu___1049_71436.FStar_TypeChecker_Env.type_of);
                    FStar_TypeChecker_Env.universe_of =
                      (uu___1049_71436.FStar_TypeChecker_Env.universe_of);
                    FStar_TypeChecker_Env.check_type_of =
                      (uu___1049_71436.FStar_TypeChecker_Env.check_type_of);
                    FStar_TypeChecker_Env.use_bv_sorts =
                      (uu___1049_71436.FStar_TypeChecker_Env.use_bv_sorts);
                    FStar_TypeChecker_Env.qtbl_name_and_index =
                      (uu___1049_71436.FStar_TypeChecker_Env.qtbl_name_and_index);
                    FStar_TypeChecker_Env.normalized_eff_names =
                      (uu___1049_71436.FStar_TypeChecker_Env.normalized_eff_names);
                    FStar_TypeChecker_Env.fv_delta_depths =
                      (uu___1049_71436.FStar_TypeChecker_Env.fv_delta_depths);
                    FStar_TypeChecker_Env.proof_ns =
                      (uu___1049_71436.FStar_TypeChecker_Env.proof_ns);
                    FStar_TypeChecker_Env.synth_hook =
                      (uu___1049_71436.FStar_TypeChecker_Env.synth_hook);
                    FStar_TypeChecker_Env.splice =
                      (uu___1049_71436.FStar_TypeChecker_Env.splice);
                    FStar_TypeChecker_Env.postprocess =
                      (uu___1049_71436.FStar_TypeChecker_Env.postprocess);
                    FStar_TypeChecker_Env.is_native_tactic =
                      (uu___1049_71436.FStar_TypeChecker_Env.is_native_tactic);
                    FStar_TypeChecker_Env.identifier_info =
                      (uu___1049_71436.FStar_TypeChecker_Env.identifier_info);
                    FStar_TypeChecker_Env.tc_hooks =
                      (uu___1049_71436.FStar_TypeChecker_Env.tc_hooks);
                    FStar_TypeChecker_Env.dsenv =
                      (uu___1049_71436.FStar_TypeChecker_Env.dsenv);
                    FStar_TypeChecker_Env.nbe =
                      (uu___1049_71436.FStar_TypeChecker_Env.nbe)
                  }  in
                try
                  (fun uu___1053_71448  ->
                     match () with
                     | () ->
                         let uu____71457 =
                           FStar_TypeChecker_TcTerm.type_of_tot_term e1 t  in
                         ret uu____71457) ()
                with
                | FStar_Errors.Err (uu____71484,msg) ->
                    let uu____71488 = tts e1 t  in
                    let uu____71490 =
                      let uu____71492 = FStar_TypeChecker_Env.all_binders e1
                         in
                      FStar_All.pipe_right uu____71492
                        (FStar_Syntax_Print.binders_to_string ", ")
                       in
                    fail3 "Cannot type %s in context (%s). Error = (%s)"
                      uu____71488 uu____71490 msg
                | FStar_Errors.Error (uu____71502,msg,uu____71504) ->
                    let uu____71507 = tts e1 t  in
                    let uu____71509 =
                      let uu____71511 = FStar_TypeChecker_Env.all_binders e1
                         in
                      FStar_All.pipe_right uu____71511
                        (FStar_Syntax_Print.binders_to_string ", ")
                       in
                    fail3 "Cannot type %s in context (%s). Error = (%s)"
                      uu____71507 uu____71509 msg))
  
let (__tc_ghost :
  env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term * FStar_Reflection_Data.typ *
        FStar_TypeChecker_Env.guard_t) tac)
  =
  fun e  ->
    fun t  ->
      bind get
        (fun ps  ->
           mlog
             (fun uu____71564  ->
                let uu____71565 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.print1 "Tac> __tc_ghost(%s)\n" uu____71565)
             (fun uu____71570  ->
                let e1 =
                  let uu___1070_71572 = e  in
                  {
                    FStar_TypeChecker_Env.solver =
                      (uu___1070_71572.FStar_TypeChecker_Env.solver);
                    FStar_TypeChecker_Env.range =
                      (uu___1070_71572.FStar_TypeChecker_Env.range);
                    FStar_TypeChecker_Env.curmodule =
                      (uu___1070_71572.FStar_TypeChecker_Env.curmodule);
                    FStar_TypeChecker_Env.gamma =
                      (uu___1070_71572.FStar_TypeChecker_Env.gamma);
                    FStar_TypeChecker_Env.gamma_sig =
                      (uu___1070_71572.FStar_TypeChecker_Env.gamma_sig);
                    FStar_TypeChecker_Env.gamma_cache =
                      (uu___1070_71572.FStar_TypeChecker_Env.gamma_cache);
                    FStar_TypeChecker_Env.modules =
                      (uu___1070_71572.FStar_TypeChecker_Env.modules);
                    FStar_TypeChecker_Env.expected_typ =
                      (uu___1070_71572.FStar_TypeChecker_Env.expected_typ);
                    FStar_TypeChecker_Env.sigtab =
                      (uu___1070_71572.FStar_TypeChecker_Env.sigtab);
                    FStar_TypeChecker_Env.attrtab =
                      (uu___1070_71572.FStar_TypeChecker_Env.attrtab);
                    FStar_TypeChecker_Env.is_pattern =
                      (uu___1070_71572.FStar_TypeChecker_Env.is_pattern);
                    FStar_TypeChecker_Env.instantiate_imp =
                      (uu___1070_71572.FStar_TypeChecker_Env.instantiate_imp);
                    FStar_TypeChecker_Env.effects =
                      (uu___1070_71572.FStar_TypeChecker_Env.effects);
                    FStar_TypeChecker_Env.generalize =
                      (uu___1070_71572.FStar_TypeChecker_Env.generalize);
                    FStar_TypeChecker_Env.letrecs =
                      (uu___1070_71572.FStar_TypeChecker_Env.letrecs);
                    FStar_TypeChecker_Env.top_level =
                      (uu___1070_71572.FStar_TypeChecker_Env.top_level);
                    FStar_TypeChecker_Env.check_uvars =
                      (uu___1070_71572.FStar_TypeChecker_Env.check_uvars);
                    FStar_TypeChecker_Env.use_eq =
                      (uu___1070_71572.FStar_TypeChecker_Env.use_eq);
                    FStar_TypeChecker_Env.is_iface =
                      (uu___1070_71572.FStar_TypeChecker_Env.is_iface);
                    FStar_TypeChecker_Env.admit =
                      (uu___1070_71572.FStar_TypeChecker_Env.admit);
                    FStar_TypeChecker_Env.lax =
                      (uu___1070_71572.FStar_TypeChecker_Env.lax);
                    FStar_TypeChecker_Env.lax_universes =
                      (uu___1070_71572.FStar_TypeChecker_Env.lax_universes);
                    FStar_TypeChecker_Env.phase1 =
                      (uu___1070_71572.FStar_TypeChecker_Env.phase1);
                    FStar_TypeChecker_Env.failhard =
                      (uu___1070_71572.FStar_TypeChecker_Env.failhard);
                    FStar_TypeChecker_Env.nosynth =
                      (uu___1070_71572.FStar_TypeChecker_Env.nosynth);
                    FStar_TypeChecker_Env.uvar_subtyping = false;
                    FStar_TypeChecker_Env.tc_term =
                      (uu___1070_71572.FStar_TypeChecker_Env.tc_term);
                    FStar_TypeChecker_Env.type_of =
                      (uu___1070_71572.FStar_TypeChecker_Env.type_of);
                    FStar_TypeChecker_Env.universe_of =
                      (uu___1070_71572.FStar_TypeChecker_Env.universe_of);
                    FStar_TypeChecker_Env.check_type_of =
                      (uu___1070_71572.FStar_TypeChecker_Env.check_type_of);
                    FStar_TypeChecker_Env.use_bv_sorts =
                      (uu___1070_71572.FStar_TypeChecker_Env.use_bv_sorts);
                    FStar_TypeChecker_Env.qtbl_name_and_index =
                      (uu___1070_71572.FStar_TypeChecker_Env.qtbl_name_and_index);
                    FStar_TypeChecker_Env.normalized_eff_names =
                      (uu___1070_71572.FStar_TypeChecker_Env.normalized_eff_names);
                    FStar_TypeChecker_Env.fv_delta_depths =
                      (uu___1070_71572.FStar_TypeChecker_Env.fv_delta_depths);
                    FStar_TypeChecker_Env.proof_ns =
                      (uu___1070_71572.FStar_TypeChecker_Env.proof_ns);
                    FStar_TypeChecker_Env.synth_hook =
                      (uu___1070_71572.FStar_TypeChecker_Env.synth_hook);
                    FStar_TypeChecker_Env.splice =
                      (uu___1070_71572.FStar_TypeChecker_Env.splice);
                    FStar_TypeChecker_Env.postprocess =
                      (uu___1070_71572.FStar_TypeChecker_Env.postprocess);
                    FStar_TypeChecker_Env.is_native_tactic =
                      (uu___1070_71572.FStar_TypeChecker_Env.is_native_tactic);
                    FStar_TypeChecker_Env.identifier_info =
                      (uu___1070_71572.FStar_TypeChecker_Env.identifier_info);
                    FStar_TypeChecker_Env.tc_hooks =
                      (uu___1070_71572.FStar_TypeChecker_Env.tc_hooks);
                    FStar_TypeChecker_Env.dsenv =
                      (uu___1070_71572.FStar_TypeChecker_Env.dsenv);
                    FStar_TypeChecker_Env.nbe =
                      (uu___1070_71572.FStar_TypeChecker_Env.nbe)
                  }  in
                try
                  (fun uu___1074_71587  ->
                     match () with
                     | () ->
                         let uu____71596 =
                           FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term e1 t
                            in
                         (match uu____71596 with
                          | (t1,lc,g) ->
                              ret (t1, (lc.FStar_Syntax_Syntax.res_typ), g)))
                    ()
                with
                | FStar_Errors.Err (uu____71634,msg) ->
                    let uu____71638 = tts e1 t  in
                    let uu____71640 =
                      let uu____71642 = FStar_TypeChecker_Env.all_binders e1
                         in
                      FStar_All.pipe_right uu____71642
                        (FStar_Syntax_Print.binders_to_string ", ")
                       in
                    fail3 "Cannot type %s in context (%s). Error = (%s)"
                      uu____71638 uu____71640 msg
                | FStar_Errors.Error (uu____71652,msg,uu____71654) ->
                    let uu____71657 = tts e1 t  in
                    let uu____71659 =
                      let uu____71661 = FStar_TypeChecker_Env.all_binders e1
                         in
                      FStar_All.pipe_right uu____71661
                        (FStar_Syntax_Print.binders_to_string ", ")
                       in
                    fail3 "Cannot type %s in context (%s). Error = (%s)"
                      uu____71657 uu____71659 msg))
  
let (__tc_lax :
  env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term * FStar_Reflection_Data.typ *
        FStar_TypeChecker_Env.guard_t) tac)
  =
  fun e  ->
    fun t  ->
      bind get
        (fun ps  ->
           mlog
             (fun uu____71714  ->
                let uu____71715 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.print1 "Tac> __tc(%s)\n" uu____71715)
             (fun uu____71721  ->
                let e1 =
                  let uu___1095_71723 = e  in
                  {
                    FStar_TypeChecker_Env.solver =
                      (uu___1095_71723.FStar_TypeChecker_Env.solver);
                    FStar_TypeChecker_Env.range =
                      (uu___1095_71723.FStar_TypeChecker_Env.range);
                    FStar_TypeChecker_Env.curmodule =
                      (uu___1095_71723.FStar_TypeChecker_Env.curmodule);
                    FStar_TypeChecker_Env.gamma =
                      (uu___1095_71723.FStar_TypeChecker_Env.gamma);
                    FStar_TypeChecker_Env.gamma_sig =
                      (uu___1095_71723.FStar_TypeChecker_Env.gamma_sig);
                    FStar_TypeChecker_Env.gamma_cache =
                      (uu___1095_71723.FStar_TypeChecker_Env.gamma_cache);
                    FStar_TypeChecker_Env.modules =
                      (uu___1095_71723.FStar_TypeChecker_Env.modules);
                    FStar_TypeChecker_Env.expected_typ =
                      (uu___1095_71723.FStar_TypeChecker_Env.expected_typ);
                    FStar_TypeChecker_Env.sigtab =
                      (uu___1095_71723.FStar_TypeChecker_Env.sigtab);
                    FStar_TypeChecker_Env.attrtab =
                      (uu___1095_71723.FStar_TypeChecker_Env.attrtab);
                    FStar_TypeChecker_Env.is_pattern =
                      (uu___1095_71723.FStar_TypeChecker_Env.is_pattern);
                    FStar_TypeChecker_Env.instantiate_imp =
                      (uu___1095_71723.FStar_TypeChecker_Env.instantiate_imp);
                    FStar_TypeChecker_Env.effects =
                      (uu___1095_71723.FStar_TypeChecker_Env.effects);
                    FStar_TypeChecker_Env.generalize =
                      (uu___1095_71723.FStar_TypeChecker_Env.generalize);
                    FStar_TypeChecker_Env.letrecs =
                      (uu___1095_71723.FStar_TypeChecker_Env.letrecs);
                    FStar_TypeChecker_Env.top_level =
                      (uu___1095_71723.FStar_TypeChecker_Env.top_level);
                    FStar_TypeChecker_Env.check_uvars =
                      (uu___1095_71723.FStar_TypeChecker_Env.check_uvars);
                    FStar_TypeChecker_Env.use_eq =
                      (uu___1095_71723.FStar_TypeChecker_Env.use_eq);
                    FStar_TypeChecker_Env.is_iface =
                      (uu___1095_71723.FStar_TypeChecker_Env.is_iface);
                    FStar_TypeChecker_Env.admit =
                      (uu___1095_71723.FStar_TypeChecker_Env.admit);
                    FStar_TypeChecker_Env.lax =
                      (uu___1095_71723.FStar_TypeChecker_Env.lax);
                    FStar_TypeChecker_Env.lax_universes =
                      (uu___1095_71723.FStar_TypeChecker_Env.lax_universes);
                    FStar_TypeChecker_Env.phase1 =
                      (uu___1095_71723.FStar_TypeChecker_Env.phase1);
                    FStar_TypeChecker_Env.failhard =
                      (uu___1095_71723.FStar_TypeChecker_Env.failhard);
                    FStar_TypeChecker_Env.nosynth =
                      (uu___1095_71723.FStar_TypeChecker_Env.nosynth);
                    FStar_TypeChecker_Env.uvar_subtyping = false;
                    FStar_TypeChecker_Env.tc_term =
                      (uu___1095_71723.FStar_TypeChecker_Env.tc_term);
                    FStar_TypeChecker_Env.type_of =
                      (uu___1095_71723.FStar_TypeChecker_Env.type_of);
                    FStar_TypeChecker_Env.universe_of =
                      (uu___1095_71723.FStar_TypeChecker_Env.universe_of);
                    FStar_TypeChecker_Env.check_type_of =
                      (uu___1095_71723.FStar_TypeChecker_Env.check_type_of);
                    FStar_TypeChecker_Env.use_bv_sorts =
                      (uu___1095_71723.FStar_TypeChecker_Env.use_bv_sorts);
                    FStar_TypeChecker_Env.qtbl_name_and_index =
                      (uu___1095_71723.FStar_TypeChecker_Env.qtbl_name_and_index);
                    FStar_TypeChecker_Env.normalized_eff_names =
                      (uu___1095_71723.FStar_TypeChecker_Env.normalized_eff_names);
                    FStar_TypeChecker_Env.fv_delta_depths =
                      (uu___1095_71723.FStar_TypeChecker_Env.fv_delta_depths);
                    FStar_TypeChecker_Env.proof_ns =
                      (uu___1095_71723.FStar_TypeChecker_Env.proof_ns);
                    FStar_TypeChecker_Env.synth_hook =
                      (uu___1095_71723.FStar_TypeChecker_Env.synth_hook);
                    FStar_TypeChecker_Env.splice =
                      (uu___1095_71723.FStar_TypeChecker_Env.splice);
                    FStar_TypeChecker_Env.postprocess =
                      (uu___1095_71723.FStar_TypeChecker_Env.postprocess);
                    FStar_TypeChecker_Env.is_native_tactic =
                      (uu___1095_71723.FStar_TypeChecker_Env.is_native_tactic);
                    FStar_TypeChecker_Env.identifier_info =
                      (uu___1095_71723.FStar_TypeChecker_Env.identifier_info);
                    FStar_TypeChecker_Env.tc_hooks =
                      (uu___1095_71723.FStar_TypeChecker_Env.tc_hooks);
                    FStar_TypeChecker_Env.dsenv =
                      (uu___1095_71723.FStar_TypeChecker_Env.dsenv);
                    FStar_TypeChecker_Env.nbe =
                      (uu___1095_71723.FStar_TypeChecker_Env.nbe)
                  }  in
                let e2 =
                  let uu___1098_71726 = e1  in
                  {
                    FStar_TypeChecker_Env.solver =
                      (uu___1098_71726.FStar_TypeChecker_Env.solver);
                    FStar_TypeChecker_Env.range =
                      (uu___1098_71726.FStar_TypeChecker_Env.range);
                    FStar_TypeChecker_Env.curmodule =
                      (uu___1098_71726.FStar_TypeChecker_Env.curmodule);
                    FStar_TypeChecker_Env.gamma =
                      (uu___1098_71726.FStar_TypeChecker_Env.gamma);
                    FStar_TypeChecker_Env.gamma_sig =
                      (uu___1098_71726.FStar_TypeChecker_Env.gamma_sig);
                    FStar_TypeChecker_Env.gamma_cache =
                      (uu___1098_71726.FStar_TypeChecker_Env.gamma_cache);
                    FStar_TypeChecker_Env.modules =
                      (uu___1098_71726.FStar_TypeChecker_Env.modules);
                    FStar_TypeChecker_Env.expected_typ =
                      (uu___1098_71726.FStar_TypeChecker_Env.expected_typ);
                    FStar_TypeChecker_Env.sigtab =
                      (uu___1098_71726.FStar_TypeChecker_Env.sigtab);
                    FStar_TypeChecker_Env.attrtab =
                      (uu___1098_71726.FStar_TypeChecker_Env.attrtab);
                    FStar_TypeChecker_Env.is_pattern =
                      (uu___1098_71726.FStar_TypeChecker_Env.is_pattern);
                    FStar_TypeChecker_Env.instantiate_imp =
                      (uu___1098_71726.FStar_TypeChecker_Env.instantiate_imp);
                    FStar_TypeChecker_Env.effects =
                      (uu___1098_71726.FStar_TypeChecker_Env.effects);
                    FStar_TypeChecker_Env.generalize =
                      (uu___1098_71726.FStar_TypeChecker_Env.generalize);
                    FStar_TypeChecker_Env.letrecs =
                      (uu___1098_71726.FStar_TypeChecker_Env.letrecs);
                    FStar_TypeChecker_Env.top_level =
                      (uu___1098_71726.FStar_TypeChecker_Env.top_level);
                    FStar_TypeChecker_Env.check_uvars =
                      (uu___1098_71726.FStar_TypeChecker_Env.check_uvars);
                    FStar_TypeChecker_Env.use_eq =
                      (uu___1098_71726.FStar_TypeChecker_Env.use_eq);
                    FStar_TypeChecker_Env.is_iface =
                      (uu___1098_71726.FStar_TypeChecker_Env.is_iface);
                    FStar_TypeChecker_Env.admit =
                      (uu___1098_71726.FStar_TypeChecker_Env.admit);
                    FStar_TypeChecker_Env.lax = true;
                    FStar_TypeChecker_Env.lax_universes =
                      (uu___1098_71726.FStar_TypeChecker_Env.lax_universes);
                    FStar_TypeChecker_Env.phase1 =
                      (uu___1098_71726.FStar_TypeChecker_Env.phase1);
                    FStar_TypeChecker_Env.failhard =
                      (uu___1098_71726.FStar_TypeChecker_Env.failhard);
                    FStar_TypeChecker_Env.nosynth =
                      (uu___1098_71726.FStar_TypeChecker_Env.nosynth);
                    FStar_TypeChecker_Env.uvar_subtyping =
                      (uu___1098_71726.FStar_TypeChecker_Env.uvar_subtyping);
                    FStar_TypeChecker_Env.tc_term =
                      (uu___1098_71726.FStar_TypeChecker_Env.tc_term);
                    FStar_TypeChecker_Env.type_of =
                      (uu___1098_71726.FStar_TypeChecker_Env.type_of);
                    FStar_TypeChecker_Env.universe_of =
                      (uu___1098_71726.FStar_TypeChecker_Env.universe_of);
                    FStar_TypeChecker_Env.check_type_of =
                      (uu___1098_71726.FStar_TypeChecker_Env.check_type_of);
                    FStar_TypeChecker_Env.use_bv_sorts =
                      (uu___1098_71726.FStar_TypeChecker_Env.use_bv_sorts);
                    FStar_TypeChecker_Env.qtbl_name_and_index =
                      (uu___1098_71726.FStar_TypeChecker_Env.qtbl_name_and_index);
                    FStar_TypeChecker_Env.normalized_eff_names =
                      (uu___1098_71726.FStar_TypeChecker_Env.normalized_eff_names);
                    FStar_TypeChecker_Env.fv_delta_depths =
                      (uu___1098_71726.FStar_TypeChecker_Env.fv_delta_depths);
                    FStar_TypeChecker_Env.proof_ns =
                      (uu___1098_71726.FStar_TypeChecker_Env.proof_ns);
                    FStar_TypeChecker_Env.synth_hook =
                      (uu___1098_71726.FStar_TypeChecker_Env.synth_hook);
                    FStar_TypeChecker_Env.splice =
                      (uu___1098_71726.FStar_TypeChecker_Env.splice);
                    FStar_TypeChecker_Env.postprocess =
                      (uu___1098_71726.FStar_TypeChecker_Env.postprocess);
                    FStar_TypeChecker_Env.is_native_tactic =
                      (uu___1098_71726.FStar_TypeChecker_Env.is_native_tactic);
                    FStar_TypeChecker_Env.identifier_info =
                      (uu___1098_71726.FStar_TypeChecker_Env.identifier_info);
                    FStar_TypeChecker_Env.tc_hooks =
                      (uu___1098_71726.FStar_TypeChecker_Env.tc_hooks);
                    FStar_TypeChecker_Env.dsenv =
                      (uu___1098_71726.FStar_TypeChecker_Env.dsenv);
                    FStar_TypeChecker_Env.nbe =
                      (uu___1098_71726.FStar_TypeChecker_Env.nbe)
                  }  in
                try
                  (fun uu___1102_71741  ->
                     match () with
                     | () ->
                         let uu____71750 =
                           FStar_TypeChecker_TcTerm.tc_term e2 t  in
                         (match uu____71750 with
                          | (t1,lc,g) ->
                              ret (t1, (lc.FStar_Syntax_Syntax.res_typ), g)))
                    ()
                with
                | FStar_Errors.Err (uu____71788,msg) ->
                    let uu____71792 = tts e2 t  in
                    let uu____71794 =
                      let uu____71796 = FStar_TypeChecker_Env.all_binders e2
                         in
                      FStar_All.pipe_right uu____71796
                        (FStar_Syntax_Print.binders_to_string ", ")
                       in
                    fail3 "Cannot type %s in context (%s). Error = (%s)"
                      uu____71792 uu____71794 msg
                | FStar_Errors.Error (uu____71806,msg,uu____71808) ->
                    let uu____71811 = tts e2 t  in
                    let uu____71813 =
                      let uu____71815 = FStar_TypeChecker_Env.all_binders e2
                         in
                      FStar_All.pipe_right uu____71815
                        (FStar_Syntax_Print.binders_to_string ", ")
                       in
                    fail3 "Cannot type %s in context (%s). Error = (%s)"
                      uu____71811 uu____71813 msg))
  
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
  fun uu____71849  ->
    bind get (fun ps  -> ret ps.FStar_Tactics_Types.guard_policy)
  
let (set_guard_policy : FStar_Tactics_Types.guard_policy -> unit tac) =
  fun pol  ->
    bind get
      (fun ps  ->
         set
           (let uu___1127_71868 = ps  in
            {
              FStar_Tactics_Types.main_context =
                (uu___1127_71868.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___1127_71868.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___1127_71868.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___1127_71868.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (uu___1127_71868.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___1127_71868.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___1127_71868.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___1127_71868.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___1127_71868.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy = pol;
              FStar_Tactics_Types.freshness =
                (uu___1127_71868.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___1127_71868.FStar_Tactics_Types.tac_verb_dbg);
              FStar_Tactics_Types.local_state =
                (uu___1127_71868.FStar_Tactics_Types.local_state)
            }))
  
let with_policy : 'a . FStar_Tactics_Types.guard_policy -> 'a tac -> 'a tac =
  fun pol  ->
    fun t  ->
      let uu____71893 = get_guard_policy ()  in
      bind uu____71893
        (fun old_pol  ->
           let uu____71899 = set_guard_policy pol  in
           bind uu____71899
             (fun uu____71903  ->
                bind t
                  (fun r  ->
                     let uu____71907 = set_guard_policy old_pol  in
                     bind uu____71907 (fun uu____71911  -> ret r))))
  
let (getopts : FStar_Options.optionstate tac) =
  let uu____71915 = let uu____71920 = cur_goal ()  in trytac uu____71920  in
  bind uu____71915
    (fun uu___609_71927  ->
       match uu___609_71927 with
       | FStar_Pervasives_Native.Some g -> ret g.FStar_Tactics_Types.opts
       | FStar_Pervasives_Native.None  ->
           let uu____71933 = FStar_Options.peek ()  in ret uu____71933)
  
let (proc_guard :
  Prims.string -> env -> FStar_TypeChecker_Env.guard_t -> unit tac) =
  fun reason  ->
    fun e  ->
      fun g  ->
        mlog
          (fun uu____71958  ->
             let uu____71959 = FStar_TypeChecker_Rel.guard_to_string e g  in
             FStar_Util.print2 "Processing guard (%s:%s)\n" reason
               uu____71959)
          (fun uu____71964  ->
             let uu____71965 =
               add_implicits g.FStar_TypeChecker_Env.implicits  in
             bind uu____71965
               (fun uu____71969  ->
                  bind getopts
                    (fun opts  ->
                       let uu____71973 =
                         let uu____71974 =
                           FStar_TypeChecker_Rel.simplify_guard e g  in
                         uu____71974.FStar_TypeChecker_Env.guard_f  in
                       match uu____71973 with
                       | FStar_TypeChecker_Common.Trivial  -> ret ()
                       | FStar_TypeChecker_Common.NonTrivial f ->
                           let uu____71978 = istrivial e f  in
                           if uu____71978
                           then ret ()
                           else
                             bind get
                               (fun ps  ->
                                  match ps.FStar_Tactics_Types.guard_policy
                                  with
                                  | FStar_Tactics_Types.Drop  ->
                                      ((let uu____71991 =
                                          let uu____71997 =
                                            let uu____71999 =
                                              FStar_TypeChecker_Rel.guard_to_string
                                                e g
                                               in
                                            FStar_Util.format1
                                              "Tactics admitted guard <%s>\n\n"
                                              uu____71999
                                             in
                                          (FStar_Errors.Warning_TacAdmit,
                                            uu____71997)
                                           in
                                        FStar_Errors.log_issue
                                          e.FStar_TypeChecker_Env.range
                                          uu____71991);
                                       ret ())
                                  | FStar_Tactics_Types.Goal  ->
                                      mlog
                                        (fun uu____72005  ->
                                           let uu____72006 =
                                             FStar_TypeChecker_Rel.guard_to_string
                                               e g
                                              in
                                           FStar_Util.print2
                                             "Making guard (%s:%s) into a goal\n"
                                             reason uu____72006)
                                        (fun uu____72011  ->
                                           let uu____72012 =
                                             mk_irrelevant_goal reason e f
                                               opts ""
                                              in
                                           bind uu____72012
                                             (fun goal  ->
                                                let goal1 =
                                                  let uu___1156_72020 = goal
                                                     in
                                                  {
                                                    FStar_Tactics_Types.goal_main_env
                                                      =
                                                      (uu___1156_72020.FStar_Tactics_Types.goal_main_env);
                                                    FStar_Tactics_Types.goal_ctx_uvar
                                                      =
                                                      (uu___1156_72020.FStar_Tactics_Types.goal_ctx_uvar);
                                                    FStar_Tactics_Types.opts
                                                      =
                                                      (uu___1156_72020.FStar_Tactics_Types.opts);
                                                    FStar_Tactics_Types.is_guard
                                                      = true;
                                                    FStar_Tactics_Types.label
                                                      =
                                                      (uu___1156_72020.FStar_Tactics_Types.label)
                                                  }  in
                                                push_goals [goal1]))
                                  | FStar_Tactics_Types.SMT  ->
                                      mlog
                                        (fun uu____72024  ->
                                           let uu____72025 =
                                             FStar_TypeChecker_Rel.guard_to_string
                                               e g
                                              in
                                           FStar_Util.print2
                                             "Sending guard (%s:%s) to SMT goal\n"
                                             reason uu____72025)
                                        (fun uu____72030  ->
                                           let uu____72031 =
                                             mk_irrelevant_goal reason e f
                                               opts ""
                                              in
                                           bind uu____72031
                                             (fun goal  ->
                                                let goal1 =
                                                  let uu___1163_72039 = goal
                                                     in
                                                  {
                                                    FStar_Tactics_Types.goal_main_env
                                                      =
                                                      (uu___1163_72039.FStar_Tactics_Types.goal_main_env);
                                                    FStar_Tactics_Types.goal_ctx_uvar
                                                      =
                                                      (uu___1163_72039.FStar_Tactics_Types.goal_ctx_uvar);
                                                    FStar_Tactics_Types.opts
                                                      =
                                                      (uu___1163_72039.FStar_Tactics_Types.opts);
                                                    FStar_Tactics_Types.is_guard
                                                      = true;
                                                    FStar_Tactics_Types.label
                                                      =
                                                      (uu___1163_72039.FStar_Tactics_Types.label)
                                                  }  in
                                                push_smt_goals [goal1]))
                                  | FStar_Tactics_Types.Force  ->
                                      mlog
                                        (fun uu____72043  ->
                                           let uu____72044 =
                                             FStar_TypeChecker_Rel.guard_to_string
                                               e g
                                              in
                                           FStar_Util.print2
                                             "Forcing guard (%s:%s)\n" reason
                                             uu____72044)
                                        (fun uu____72048  ->
                                           try
                                             (fun uu___1170_72053  ->
                                                match () with
                                                | () ->
                                                    let uu____72056 =
                                                      let uu____72058 =
                                                        let uu____72060 =
                                                          FStar_TypeChecker_Rel.discharge_guard_no_smt
                                                            e g
                                                           in
                                                        FStar_All.pipe_left
                                                          FStar_TypeChecker_Env.is_trivial
                                                          uu____72060
                                                         in
                                                      Prims.op_Negation
                                                        uu____72058
                                                       in
                                                    if uu____72056
                                                    then
                                                      mlog
                                                        (fun uu____72067  ->
                                                           let uu____72068 =
                                                             FStar_TypeChecker_Rel.guard_to_string
                                                               e g
                                                              in
                                                           FStar_Util.print1
                                                             "guard = %s\n"
                                                             uu____72068)
                                                        (fun uu____72072  ->
                                                           fail1
                                                             "Forcing the guard failed (%s)"
                                                             reason)
                                                    else ret ()) ()
                                           with
                                           | uu___1169_72077 ->
                                               mlog
                                                 (fun uu____72082  ->
                                                    let uu____72083 =
                                                      FStar_TypeChecker_Rel.guard_to_string
                                                        e g
                                                       in
                                                    FStar_Util.print1
                                                      "guard = %s\n"
                                                      uu____72083)
                                                 (fun uu____72087  ->
                                                    fail1
                                                      "Forcing the guard failed (%s)"
                                                      reason))))))
  
let (tc : FStar_Syntax_Syntax.term -> FStar_Reflection_Data.typ tac) =
  fun t  ->
    let uu____72099 =
      let uu____72102 = cur_goal ()  in
      bind uu____72102
        (fun goal  ->
           let uu____72108 =
             let uu____72117 = FStar_Tactics_Types.goal_env goal  in
             __tc_lax uu____72117 t  in
           bind uu____72108
             (fun uu____72128  ->
                match uu____72128 with
                | (uu____72137,typ,uu____72139) -> ret typ))
       in
    FStar_All.pipe_left (wrap_err "tc") uu____72099
  
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
            let uu____72179 = mk_irrelevant_goal reason env phi opts label1
               in
            bind uu____72179 (fun goal  -> add_goals [goal])
  
let (trivial : unit -> unit tac) =
  fun uu____72191  ->
    let uu____72194 = cur_goal ()  in
    bind uu____72194
      (fun goal  ->
         let uu____72200 =
           let uu____72202 = FStar_Tactics_Types.goal_env goal  in
           let uu____72203 = FStar_Tactics_Types.goal_type goal  in
           istrivial uu____72202 uu____72203  in
         if uu____72200
         then solve' goal FStar_Syntax_Util.exp_unit
         else
           (let uu____72209 =
              let uu____72211 = FStar_Tactics_Types.goal_env goal  in
              let uu____72212 = FStar_Tactics_Types.goal_type goal  in
              tts uu____72211 uu____72212  in
            fail1 "Not a trivial goal: %s" uu____72209))
  
let divide : 'a 'b . FStar_BigInt.t -> 'a tac -> 'b tac -> ('a * 'b) tac =
  fun n1  ->
    fun l  ->
      fun r  ->
        bind get
          (fun p  ->
             let uu____72263 =
               try
                 (fun uu___1226_72286  ->
                    match () with
                    | () ->
                        let uu____72297 =
                          let uu____72306 = FStar_BigInt.to_int_fs n1  in
                          FStar_List.splitAt uu____72306
                            p.FStar_Tactics_Types.goals
                           in
                        ret uu____72297) ()
               with | uu___1225_72317 -> fail "divide: not enough goals"  in
             bind uu____72263
               (fun uu____72354  ->
                  match uu____72354 with
                  | (lgs,rgs) ->
                      let lp =
                        let uu___1208_72380 = p  in
                        {
                          FStar_Tactics_Types.main_context =
                            (uu___1208_72380.FStar_Tactics_Types.main_context);
                          FStar_Tactics_Types.main_goal =
                            (uu___1208_72380.FStar_Tactics_Types.main_goal);
                          FStar_Tactics_Types.all_implicits =
                            (uu___1208_72380.FStar_Tactics_Types.all_implicits);
                          FStar_Tactics_Types.goals = lgs;
                          FStar_Tactics_Types.smt_goals = [];
                          FStar_Tactics_Types.depth =
                            (uu___1208_72380.FStar_Tactics_Types.depth);
                          FStar_Tactics_Types.__dump =
                            (uu___1208_72380.FStar_Tactics_Types.__dump);
                          FStar_Tactics_Types.psc =
                            (uu___1208_72380.FStar_Tactics_Types.psc);
                          FStar_Tactics_Types.entry_range =
                            (uu___1208_72380.FStar_Tactics_Types.entry_range);
                          FStar_Tactics_Types.guard_policy =
                            (uu___1208_72380.FStar_Tactics_Types.guard_policy);
                          FStar_Tactics_Types.freshness =
                            (uu___1208_72380.FStar_Tactics_Types.freshness);
                          FStar_Tactics_Types.tac_verb_dbg =
                            (uu___1208_72380.FStar_Tactics_Types.tac_verb_dbg);
                          FStar_Tactics_Types.local_state =
                            (uu___1208_72380.FStar_Tactics_Types.local_state)
                        }  in
                      let uu____72381 = set lp  in
                      bind uu____72381
                        (fun uu____72389  ->
                           bind l
                             (fun a  ->
                                bind get
                                  (fun lp'  ->
                                     let rp =
                                       let uu___1214_72405 = lp'  in
                                       {
                                         FStar_Tactics_Types.main_context =
                                           (uu___1214_72405.FStar_Tactics_Types.main_context);
                                         FStar_Tactics_Types.main_goal =
                                           (uu___1214_72405.FStar_Tactics_Types.main_goal);
                                         FStar_Tactics_Types.all_implicits =
                                           (uu___1214_72405.FStar_Tactics_Types.all_implicits);
                                         FStar_Tactics_Types.goals = rgs;
                                         FStar_Tactics_Types.smt_goals = [];
                                         FStar_Tactics_Types.depth =
                                           (uu___1214_72405.FStar_Tactics_Types.depth);
                                         FStar_Tactics_Types.__dump =
                                           (uu___1214_72405.FStar_Tactics_Types.__dump);
                                         FStar_Tactics_Types.psc =
                                           (uu___1214_72405.FStar_Tactics_Types.psc);
                                         FStar_Tactics_Types.entry_range =
                                           (uu___1214_72405.FStar_Tactics_Types.entry_range);
                                         FStar_Tactics_Types.guard_policy =
                                           (uu___1214_72405.FStar_Tactics_Types.guard_policy);
                                         FStar_Tactics_Types.freshness =
                                           (uu___1214_72405.FStar_Tactics_Types.freshness);
                                         FStar_Tactics_Types.tac_verb_dbg =
                                           (uu___1214_72405.FStar_Tactics_Types.tac_verb_dbg);
                                         FStar_Tactics_Types.local_state =
                                           (uu___1214_72405.FStar_Tactics_Types.local_state)
                                       }  in
                                     let uu____72406 = set rp  in
                                     bind uu____72406
                                       (fun uu____72414  ->
                                          bind r
                                            (fun b  ->
                                               bind get
                                                 (fun rp'  ->
                                                    let p' =
                                                      let uu___1220_72430 =
                                                        rp'  in
                                                      {
                                                        FStar_Tactics_Types.main_context
                                                          =
                                                          (uu___1220_72430.FStar_Tactics_Types.main_context);
                                                        FStar_Tactics_Types.main_goal
                                                          =
                                                          (uu___1220_72430.FStar_Tactics_Types.main_goal);
                                                        FStar_Tactics_Types.all_implicits
                                                          =
                                                          (uu___1220_72430.FStar_Tactics_Types.all_implicits);
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
                                                          (uu___1220_72430.FStar_Tactics_Types.depth);
                                                        FStar_Tactics_Types.__dump
                                                          =
                                                          (uu___1220_72430.FStar_Tactics_Types.__dump);
                                                        FStar_Tactics_Types.psc
                                                          =
                                                          (uu___1220_72430.FStar_Tactics_Types.psc);
                                                        FStar_Tactics_Types.entry_range
                                                          =
                                                          (uu___1220_72430.FStar_Tactics_Types.entry_range);
                                                        FStar_Tactics_Types.guard_policy
                                                          =
                                                          (uu___1220_72430.FStar_Tactics_Types.guard_policy);
                                                        FStar_Tactics_Types.freshness
                                                          =
                                                          (uu___1220_72430.FStar_Tactics_Types.freshness);
                                                        FStar_Tactics_Types.tac_verb_dbg
                                                          =
                                                          (uu___1220_72430.FStar_Tactics_Types.tac_verb_dbg);
                                                        FStar_Tactics_Types.local_state
                                                          =
                                                          (uu___1220_72430.FStar_Tactics_Types.local_state)
                                                      }  in
                                                    let uu____72431 = set p'
                                                       in
                                                    bind uu____72431
                                                      (fun uu____72439  ->
                                                         bind
                                                           remove_solved_goals
                                                           (fun uu____72445 
                                                              -> ret (a, b)))))))))))
  
let focus : 'a . 'a tac -> 'a tac =
  fun f  ->
    let uu____72467 = divide FStar_BigInt.one f idtac  in
    bind uu____72467
      (fun uu____72480  -> match uu____72480 with | (a,()) -> ret a)
  
let rec map : 'a . 'a tac -> 'a Prims.list tac =
  fun tau  ->
    bind get
      (fun p  ->
         match p.FStar_Tactics_Types.goals with
         | [] -> ret []
         | uu____72518::uu____72519 ->
             let uu____72522 =
               let uu____72531 = map tau  in
               divide FStar_BigInt.one tau uu____72531  in
             bind uu____72522
               (fun uu____72549  ->
                  match uu____72549 with | (h,t) -> ret (h :: t)))
  
let (seq : unit tac -> unit tac -> unit tac) =
  fun t1  ->
    fun t2  ->
      let uu____72591 =
        bind t1
          (fun uu____72596  ->
             let uu____72597 = map t2  in
             bind uu____72597 (fun uu____72605  -> ret ()))
         in
      focus uu____72591
  
let (intro : unit -> FStar_Syntax_Syntax.binder tac) =
  fun uu____72615  ->
    let uu____72618 =
      let uu____72621 = cur_goal ()  in
      bind uu____72621
        (fun goal  ->
           let uu____72630 =
             let uu____72637 = FStar_Tactics_Types.goal_type goal  in
             FStar_Syntax_Util.arrow_one uu____72637  in
           match uu____72630 with
           | FStar_Pervasives_Native.Some (b,c) ->
               let uu____72646 =
                 let uu____72648 = FStar_Syntax_Util.is_total_comp c  in
                 Prims.op_Negation uu____72648  in
               if uu____72646
               then fail "Codomain is effectful"
               else
                 (let env' =
                    let uu____72657 = FStar_Tactics_Types.goal_env goal  in
                    FStar_TypeChecker_Env.push_binders uu____72657 [b]  in
                  let typ' = comp_to_typ c  in
                  let uu____72671 = new_uvar "intro" env' typ'  in
                  bind uu____72671
                    (fun uu____72688  ->
                       match uu____72688 with
                       | (body,ctx_uvar) ->
                           let sol =
                             FStar_Syntax_Util.abs [b] body
                               (FStar_Pervasives_Native.Some
                                  (FStar_Syntax_Util.residual_comp_of_comp c))
                              in
                           let uu____72712 = set_solution goal sol  in
                           bind uu____72712
                             (fun uu____72718  ->
                                let g =
                                  FStar_Tactics_Types.mk_goal env' ctx_uvar
                                    goal.FStar_Tactics_Types.opts
                                    goal.FStar_Tactics_Types.is_guard
                                    goal.FStar_Tactics_Types.label
                                   in
                                let uu____72720 =
                                  let uu____72723 = bnorm_goal g  in
                                  replace_cur uu____72723  in
                                bind uu____72720 (fun uu____72725  -> ret b))))
           | FStar_Pervasives_Native.None  ->
               let uu____72730 =
                 let uu____72732 = FStar_Tactics_Types.goal_env goal  in
                 let uu____72733 = FStar_Tactics_Types.goal_type goal  in
                 tts uu____72732 uu____72733  in
               fail1 "goal is not an arrow (%s)" uu____72730)
       in
    FStar_All.pipe_left (wrap_err "intro") uu____72618
  
let (intro_rec :
  unit -> (FStar_Syntax_Syntax.binder * FStar_Syntax_Syntax.binder) tac) =
  fun uu____72751  ->
    let uu____72758 = cur_goal ()  in
    bind uu____72758
      (fun goal  ->
         FStar_Util.print_string
           "WARNING (intro_rec): calling this is known to cause normalizer loops\n";
         FStar_Util.print_string
           "WARNING (intro_rec): proceed at your own risk...\n";
         (let uu____72777 =
            let uu____72784 = FStar_Tactics_Types.goal_type goal  in
            FStar_Syntax_Util.arrow_one uu____72784  in
          match uu____72777 with
          | FStar_Pervasives_Native.Some (b,c) ->
              let uu____72797 =
                let uu____72799 = FStar_Syntax_Util.is_total_comp c  in
                Prims.op_Negation uu____72799  in
              if uu____72797
              then fail "Codomain is effectful"
              else
                (let bv =
                   let uu____72816 = FStar_Tactics_Types.goal_type goal  in
                   FStar_Syntax_Syntax.gen_bv "__recf"
                     FStar_Pervasives_Native.None uu____72816
                    in
                 let bs =
                   let uu____72827 = FStar_Syntax_Syntax.mk_binder bv  in
                   [uu____72827; b]  in
                 let env' =
                   let uu____72853 = FStar_Tactics_Types.goal_env goal  in
                   FStar_TypeChecker_Env.push_binders uu____72853 bs  in
                 let uu____72854 =
                   let uu____72861 = comp_to_typ c  in
                   new_uvar "intro_rec" env' uu____72861  in
                 bind uu____72854
                   (fun uu____72881  ->
                      match uu____72881 with
                      | (u,ctx_uvar_u) ->
                          let lb =
                            let uu____72895 =
                              FStar_Tactics_Types.goal_type goal  in
                            let uu____72898 =
                              FStar_Syntax_Util.abs [b] u
                                FStar_Pervasives_Native.None
                               in
                            FStar_Syntax_Util.mk_letbinding
                              (FStar_Util.Inl bv) [] uu____72895
                              FStar_Parser_Const.effect_Tot_lid uu____72898
                              [] FStar_Range.dummyRange
                             in
                          let body = FStar_Syntax_Syntax.bv_to_name bv  in
                          let uu____72916 =
                            FStar_Syntax_Subst.close_let_rec [lb] body  in
                          (match uu____72916 with
                           | (lbs,body1) ->
                               let tm =
                                 let uu____72938 =
                                   let uu____72939 =
                                     FStar_Tactics_Types.goal_witness goal
                                      in
                                   uu____72939.FStar_Syntax_Syntax.pos  in
                                 FStar_Syntax_Syntax.mk
                                   (FStar_Syntax_Syntax.Tm_let
                                      ((true, lbs), body1))
                                   FStar_Pervasives_Native.None uu____72938
                                  in
                               let uu____72955 = set_solution goal tm  in
                               bind uu____72955
                                 (fun uu____72964  ->
                                    let uu____72965 =
                                      let uu____72968 =
                                        bnorm_goal
                                          (let uu___1291_72971 = goal  in
                                           {
                                             FStar_Tactics_Types.goal_main_env
                                               =
                                               (uu___1291_72971.FStar_Tactics_Types.goal_main_env);
                                             FStar_Tactics_Types.goal_ctx_uvar
                                               = ctx_uvar_u;
                                             FStar_Tactics_Types.opts =
                                               (uu___1291_72971.FStar_Tactics_Types.opts);
                                             FStar_Tactics_Types.is_guard =
                                               (uu___1291_72971.FStar_Tactics_Types.is_guard);
                                             FStar_Tactics_Types.label =
                                               (uu___1291_72971.FStar_Tactics_Types.label)
                                           })
                                         in
                                      replace_cur uu____72968  in
                                    bind uu____72965
                                      (fun uu____72978  ->
                                         let uu____72979 =
                                           let uu____72984 =
                                             FStar_Syntax_Syntax.mk_binder bv
                                              in
                                           (uu____72984, b)  in
                                         ret uu____72979)))))
          | FStar_Pervasives_Native.None  ->
              let uu____72993 =
                let uu____72995 = FStar_Tactics_Types.goal_env goal  in
                let uu____72996 = FStar_Tactics_Types.goal_type goal  in
                tts uu____72995 uu____72996  in
              fail1 "intro_rec: goal is not an arrow (%s)" uu____72993))
  
let (norm : FStar_Syntax_Embeddings.norm_step Prims.list -> unit tac) =
  fun s  ->
    let uu____73016 = cur_goal ()  in
    bind uu____73016
      (fun goal  ->
         mlog
           (fun uu____73023  ->
              let uu____73024 =
                let uu____73026 = FStar_Tactics_Types.goal_witness goal  in
                FStar_Syntax_Print.term_to_string uu____73026  in
              FStar_Util.print1 "norm: witness = %s\n" uu____73024)
           (fun uu____73032  ->
              let steps =
                let uu____73036 = FStar_TypeChecker_Normalize.tr_norm_steps s
                   in
                FStar_List.append
                  [FStar_TypeChecker_Env.Reify;
                  FStar_TypeChecker_Env.UnfoldTac] uu____73036
                 in
              let t =
                let uu____73040 = FStar_Tactics_Types.goal_env goal  in
                let uu____73041 = FStar_Tactics_Types.goal_type goal  in
                normalize steps uu____73040 uu____73041  in
              let uu____73042 = FStar_Tactics_Types.goal_with_type goal t  in
              replace_cur uu____73042))
  
let (norm_term_env :
  env ->
    FStar_Syntax_Embeddings.norm_step Prims.list ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term tac)
  =
  fun e  ->
    fun s  ->
      fun t  ->
        let uu____73067 =
          bind get
            (fun ps  ->
               let opts =
                 match ps.FStar_Tactics_Types.goals with
                 | g::uu____73075 -> g.FStar_Tactics_Types.opts
                 | uu____73078 -> FStar_Options.peek ()  in
               mlog
                 (fun uu____73083  ->
                    let uu____73084 = FStar_Syntax_Print.term_to_string t  in
                    FStar_Util.print1 "norm_term_env: t = %s\n" uu____73084)
                 (fun uu____73089  ->
                    let uu____73090 = __tc_lax e t  in
                    bind uu____73090
                      (fun uu____73111  ->
                         match uu____73111 with
                         | (t1,uu____73121,uu____73122) ->
                             let steps =
                               let uu____73126 =
                                 FStar_TypeChecker_Normalize.tr_norm_steps s
                                  in
                               FStar_List.append
                                 [FStar_TypeChecker_Env.Reify;
                                 FStar_TypeChecker_Env.UnfoldTac] uu____73126
                                in
                             let t2 =
                               normalize steps
                                 ps.FStar_Tactics_Types.main_context t1
                                in
                             mlog
                               (fun uu____73132  ->
                                  let uu____73133 =
                                    FStar_Syntax_Print.term_to_string t2  in
                                  FStar_Util.print1
                                    "norm_term_env: t' = %s\n" uu____73133)
                               (fun uu____73137  -> ret t2))))
           in
        FStar_All.pipe_left (wrap_err "norm_term") uu____73067
  
let (refine_intro : unit -> unit tac) =
  fun uu____73150  ->
    let uu____73153 =
      let uu____73156 = cur_goal ()  in
      bind uu____73156
        (fun g  ->
           let uu____73163 =
             let uu____73174 = FStar_Tactics_Types.goal_env g  in
             let uu____73175 = FStar_Tactics_Types.goal_type g  in
             FStar_TypeChecker_Rel.base_and_refinement uu____73174
               uu____73175
              in
           match uu____73163 with
           | (uu____73178,FStar_Pervasives_Native.None ) ->
               fail "not a refinement"
           | (t,FStar_Pervasives_Native.Some (bv,phi)) ->
               let g1 = FStar_Tactics_Types.goal_with_type g t  in
               let uu____73204 =
                 let uu____73209 =
                   let uu____73214 =
                     let uu____73215 = FStar_Syntax_Syntax.mk_binder bv  in
                     [uu____73215]  in
                   FStar_Syntax_Subst.open_term uu____73214 phi  in
                 match uu____73209 with
                 | (bvs,phi1) ->
                     let uu____73240 =
                       let uu____73241 = FStar_List.hd bvs  in
                       FStar_Pervasives_Native.fst uu____73241  in
                     (uu____73240, phi1)
                  in
               (match uu____73204 with
                | (bv1,phi1) ->
                    let uu____73260 =
                      let uu____73263 = FStar_Tactics_Types.goal_env g  in
                      let uu____73264 =
                        let uu____73265 =
                          let uu____73268 =
                            let uu____73269 =
                              let uu____73276 =
                                FStar_Tactics_Types.goal_witness g  in
                              (bv1, uu____73276)  in
                            FStar_Syntax_Syntax.NT uu____73269  in
                          [uu____73268]  in
                        FStar_Syntax_Subst.subst uu____73265 phi1  in
                      mk_irrelevant_goal "refine_intro refinement"
                        uu____73263 uu____73264 g.FStar_Tactics_Types.opts
                        g.FStar_Tactics_Types.label
                       in
                    bind uu____73260
                      (fun g2  ->
                         bind __dismiss
                           (fun uu____73285  -> add_goals [g1; g2]))))
       in
    FStar_All.pipe_left (wrap_err "refine_intro") uu____73153
  
let (__exact_now : Prims.bool -> FStar_Syntax_Syntax.term -> unit tac) =
  fun set_expected_typ1  ->
    fun t  ->
      let uu____73308 = cur_goal ()  in
      bind uu____73308
        (fun goal  ->
           let env =
             if set_expected_typ1
             then
               let uu____73317 = FStar_Tactics_Types.goal_env goal  in
               let uu____73318 = FStar_Tactics_Types.goal_type goal  in
               FStar_TypeChecker_Env.set_expected_typ uu____73317 uu____73318
             else FStar_Tactics_Types.goal_env goal  in
           let uu____73321 = __tc env t  in
           bind uu____73321
             (fun uu____73340  ->
                match uu____73340 with
                | (t1,typ,guard) ->
                    mlog
                      (fun uu____73355  ->
                         let uu____73356 =
                           FStar_Syntax_Print.term_to_string typ  in
                         let uu____73358 =
                           let uu____73360 =
                             FStar_Tactics_Types.goal_env goal  in
                           FStar_TypeChecker_Rel.guard_to_string uu____73360
                             guard
                            in
                         FStar_Util.print2
                           "__exact_now: got type %s\n__exact_now: and guard %s\n"
                           uu____73356 uu____73358)
                      (fun uu____73364  ->
                         let uu____73365 =
                           let uu____73368 =
                             FStar_Tactics_Types.goal_env goal  in
                           proc_guard "__exact typing" uu____73368 guard  in
                         bind uu____73365
                           (fun uu____73371  ->
                              mlog
                                (fun uu____73375  ->
                                   let uu____73376 =
                                     FStar_Syntax_Print.term_to_string typ
                                      in
                                   let uu____73378 =
                                     let uu____73380 =
                                       FStar_Tactics_Types.goal_type goal  in
                                     FStar_Syntax_Print.term_to_string
                                       uu____73380
                                      in
                                   FStar_Util.print2
                                     "__exact_now: unifying %s and %s\n"
                                     uu____73376 uu____73378)
                                (fun uu____73384  ->
                                   let uu____73385 =
                                     let uu____73389 =
                                       FStar_Tactics_Types.goal_env goal  in
                                     let uu____73390 =
                                       FStar_Tactics_Types.goal_type goal  in
                                     do_unify uu____73389 typ uu____73390  in
                                   bind uu____73385
                                     (fun b  ->
                                        if b
                                        then solve goal t1
                                        else
                                          (let uu____73400 =
                                             let uu____73402 =
                                               FStar_Tactics_Types.goal_env
                                                 goal
                                                in
                                             tts uu____73402 t1  in
                                           let uu____73403 =
                                             let uu____73405 =
                                               FStar_Tactics_Types.goal_env
                                                 goal
                                                in
                                             tts uu____73405 typ  in
                                           let uu____73406 =
                                             let uu____73408 =
                                               FStar_Tactics_Types.goal_env
                                                 goal
                                                in
                                             let uu____73409 =
                                               FStar_Tactics_Types.goal_type
                                                 goal
                                                in
                                             tts uu____73408 uu____73409  in
                                           let uu____73410 =
                                             let uu____73412 =
                                               FStar_Tactics_Types.goal_env
                                                 goal
                                                in
                                             let uu____73413 =
                                               FStar_Tactics_Types.goal_witness
                                                 goal
                                                in
                                             tts uu____73412 uu____73413  in
                                           fail4
                                             "%s : %s does not exactly solve the goal %s (witness = %s)"
                                             uu____73400 uu____73403
                                             uu____73406 uu____73410)))))))
  
let (t_exact :
  Prims.bool -> Prims.bool -> FStar_Syntax_Syntax.term -> unit tac) =
  fun try_refine  ->
    fun set_expected_typ1  ->
      fun tm  ->
        let uu____73439 =
          mlog
            (fun uu____73444  ->
               let uu____73445 = FStar_Syntax_Print.term_to_string tm  in
               FStar_Util.print1 "t_exact: tm = %s\n" uu____73445)
            (fun uu____73450  ->
               let uu____73451 =
                 let uu____73458 = __exact_now set_expected_typ1 tm  in
                 catch uu____73458  in
               bind uu____73451
                 (fun uu___611_73467  ->
                    match uu___611_73467 with
                    | FStar_Util.Inr r -> ret ()
                    | FStar_Util.Inl e when Prims.op_Negation try_refine ->
                        traise e
                    | FStar_Util.Inl e ->
                        mlog
                          (fun uu____73478  ->
                             FStar_Util.print_string
                               "__exact_now failed, trying refine...\n")
                          (fun uu____73482  ->
                             let uu____73483 =
                               let uu____73490 =
                                 let uu____73493 =
                                   norm [FStar_Syntax_Embeddings.Delta]  in
                                 bind uu____73493
                                   (fun uu____73498  ->
                                      let uu____73499 = refine_intro ()  in
                                      bind uu____73499
                                        (fun uu____73503  ->
                                           __exact_now set_expected_typ1 tm))
                                  in
                               catch uu____73490  in
                             bind uu____73483
                               (fun uu___610_73510  ->
                                  match uu___610_73510 with
                                  | FStar_Util.Inr r ->
                                      mlog
                                        (fun uu____73519  ->
                                           FStar_Util.print_string
                                             "__exact_now: failed after refining too\n")
                                        (fun uu____73522  -> ret ())
                                  | FStar_Util.Inl uu____73523 ->
                                      mlog
                                        (fun uu____73525  ->
                                           FStar_Util.print_string
                                             "__exact_now: was not a refinement\n")
                                        (fun uu____73528  -> traise e)))))
           in
        FStar_All.pipe_left (wrap_err "exact") uu____73439
  
let rec mapM : 'a 'b . ('a -> 'b tac) -> 'a Prims.list -> 'b Prims.list tac =
  fun f  ->
    fun l  ->
      match l with
      | [] -> ret []
      | x::xs ->
          let uu____73580 = f x  in
          bind uu____73580
            (fun y  ->
               let uu____73588 = mapM f xs  in
               bind uu____73588 (fun ys  -> ret (y :: ys)))
  
let rec (__try_match_by_application :
  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.aqual *
    FStar_Syntax_Syntax.ctx_uvar) Prims.list ->
    env ->
      FStar_Syntax_Syntax.term ->
        FStar_Syntax_Syntax.term ->
          (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.aqual *
            FStar_Syntax_Syntax.ctx_uvar) Prims.list tac)
  =
  fun acc  ->
    fun e  ->
      fun ty1  ->
        fun ty2  ->
          let uu____73660 = do_unify e ty1 ty2  in
          bind uu____73660
            (fun uu___612_73674  ->
               if uu___612_73674
               then ret acc
               else
                 (let uu____73694 = FStar_Syntax_Util.arrow_one ty1  in
                  match uu____73694 with
                  | FStar_Pervasives_Native.None  ->
                      let uu____73715 = FStar_Syntax_Print.term_to_string ty1
                         in
                      let uu____73717 = FStar_Syntax_Print.term_to_string ty2
                         in
                      fail2 "Could not instantiate, %s to %s" uu____73715
                        uu____73717
                  | FStar_Pervasives_Native.Some (b,c) ->
                      let uu____73734 =
                        let uu____73736 = FStar_Syntax_Util.is_total_comp c
                           in
                        Prims.op_Negation uu____73736  in
                      if uu____73734
                      then fail "Codomain is effectful"
                      else
                        (let uu____73760 =
                           new_uvar "apply arg" e
                             (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                            in
                         bind uu____73760
                           (fun uu____73787  ->
                              match uu____73787 with
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
        (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.aqual *
          FStar_Syntax_Syntax.ctx_uvar) Prims.list tac)
  = fun e  -> fun ty1  -> fun ty2  -> __try_match_by_application [] e ty1 ty2 
let (t_apply : Prims.bool -> FStar_Syntax_Syntax.term -> unit tac) =
  fun uopt  ->
    fun tm  ->
      let uu____73877 =
        mlog
          (fun uu____73882  ->
             let uu____73883 = FStar_Syntax_Print.term_to_string tm  in
             FStar_Util.print1 "t_apply: tm = %s\n" uu____73883)
          (fun uu____73888  ->
             let uu____73889 = cur_goal ()  in
             bind uu____73889
               (fun goal  ->
                  let e = FStar_Tactics_Types.goal_env goal  in
                  let uu____73897 = __tc e tm  in
                  bind uu____73897
                    (fun uu____73918  ->
                       match uu____73918 with
                       | (tm1,typ,guard) ->
                           let typ1 = bnorm e typ  in
                           let uu____73931 =
                             let uu____73942 =
                               FStar_Tactics_Types.goal_type goal  in
                             try_match_by_application e typ1 uu____73942  in
                           bind uu____73931
                             (fun uvs  ->
                                let fix_qual q =
                                  match q with
                                  | FStar_Pervasives_Native.Some
                                      (FStar_Syntax_Syntax.Meta uu____73980)
                                      ->
                                      FStar_Pervasives_Native.Some
                                        (FStar_Syntax_Syntax.Implicit false)
                                  | uu____73984 -> q  in
                                let w =
                                  FStar_List.fold_right
                                    (fun uu____74007  ->
                                       fun w  ->
                                         match uu____74007 with
                                         | (uvt,q,uu____74025) ->
                                             FStar_Syntax_Util.mk_app w
                                               [(uvt, (fix_qual q))]) uvs tm1
                                   in
                                let uvset =
                                  let uu____74057 =
                                    FStar_Syntax_Free.new_uv_set ()  in
                                  FStar_List.fold_right
                                    (fun uu____74074  ->
                                       fun s  ->
                                         match uu____74074 with
                                         | (uu____74086,uu____74087,uv) ->
                                             let uu____74089 =
                                               FStar_Syntax_Free.uvars
                                                 uv.FStar_Syntax_Syntax.ctx_uvar_typ
                                                in
                                             FStar_Util.set_union s
                                               uu____74089) uvs uu____74057
                                   in
                                let free_in_some_goal uv =
                                  FStar_Util.set_mem uv uvset  in
                                let uu____74099 = solve' goal w  in
                                bind uu____74099
                                  (fun uu____74104  ->
                                     let uu____74105 =
                                       mapM
                                         (fun uu____74122  ->
                                            match uu____74122 with
                                            | (uvt,q,uv) ->
                                                let uu____74134 =
                                                  FStar_Syntax_Unionfind.find
                                                    uv.FStar_Syntax_Syntax.ctx_uvar_head
                                                   in
                                                (match uu____74134 with
                                                 | FStar_Pervasives_Native.Some
                                                     uu____74139 -> ret ()
                                                 | FStar_Pervasives_Native.None
                                                      ->
                                                     let uu____74140 =
                                                       uopt &&
                                                         (free_in_some_goal
                                                            uv)
                                                        in
                                                     if uu____74140
                                                     then ret ()
                                                     else
                                                       (let uu____74147 =
                                                          let uu____74150 =
                                                            bnorm_goal
                                                              (let uu___1452_74153
                                                                 = goal  in
                                                               {
                                                                 FStar_Tactics_Types.goal_main_env
                                                                   =
                                                                   (uu___1452_74153.FStar_Tactics_Types.goal_main_env);
                                                                 FStar_Tactics_Types.goal_ctx_uvar
                                                                   = uv;
                                                                 FStar_Tactics_Types.opts
                                                                   =
                                                                   (uu___1452_74153.FStar_Tactics_Types.opts);
                                                                 FStar_Tactics_Types.is_guard
                                                                   = false;
                                                                 FStar_Tactics_Types.label
                                                                   =
                                                                   (uu___1452_74153.FStar_Tactics_Types.label)
                                                               })
                                                             in
                                                          [uu____74150]  in
                                                        add_goals uu____74147)))
                                         uvs
                                        in
                                     bind uu____74105
                                       (fun uu____74158  ->
                                          proc_guard "apply guard" e guard))))))
         in
      FStar_All.pipe_left (wrap_err "apply") uu____73877
  
let (lemma_or_sq :
  FStar_Syntax_Syntax.comp ->
    (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.option)
  =
  fun c  ->
    let ct = FStar_Syntax_Util.comp_to_comp_typ_nouniv c  in
    let uu____74186 =
      FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
        FStar_Parser_Const.effect_Lemma_lid
       in
    if uu____74186
    then
      let uu____74195 =
        match ct.FStar_Syntax_Syntax.effect_args with
        | pre::post::uu____74210 ->
            ((FStar_Pervasives_Native.fst pre),
              (FStar_Pervasives_Native.fst post))
        | uu____74263 -> failwith "apply_lemma: impossible: not a lemma"  in
      match uu____74195 with
      | (pre,post) ->
          let post1 =
            let uu____74296 =
              let uu____74307 =
                FStar_Syntax_Syntax.as_arg FStar_Syntax_Util.exp_unit  in
              [uu____74307]  in
            FStar_Syntax_Util.mk_app post uu____74296  in
          FStar_Pervasives_Native.Some (pre, post1)
    else
      (let uu____74338 =
         FStar_Syntax_Util.is_pure_effect ct.FStar_Syntax_Syntax.effect_name
          in
       if uu____74338
       then
         let uu____74347 =
           FStar_Syntax_Util.un_squash ct.FStar_Syntax_Syntax.result_typ  in
         FStar_Util.map_opt uu____74347
           (fun post  -> (FStar_Syntax_Util.t_true, post))
       else FStar_Pervasives_Native.None)
  
let rec fold_left :
  'a 'b . ('a -> 'b -> 'b tac) -> 'b -> 'a Prims.list -> 'b tac =
  fun f  ->
    fun e  ->
      fun xs  ->
        match xs with
        | [] -> ret e
        | x::xs1 ->
            let uu____74426 = f x e  in
            bind uu____74426 (fun e'  -> fold_left f e' xs1)
  
let (apply_lemma : FStar_Syntax_Syntax.term -> unit tac) =
  fun tm  ->
    let uu____74441 =
      let uu____74444 =
        bind get
          (fun ps  ->
             mlog
               (fun uu____74451  ->
                  let uu____74452 = FStar_Syntax_Print.term_to_string tm  in
                  FStar_Util.print1 "apply_lemma: tm = %s\n" uu____74452)
               (fun uu____74458  ->
                  let is_unit_t t =
                    let uu____74466 =
                      let uu____74467 = FStar_Syntax_Subst.compress t  in
                      uu____74467.FStar_Syntax_Syntax.n  in
                    match uu____74466 with
                    | FStar_Syntax_Syntax.Tm_fvar fv when
                        FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.unit_lid
                        -> true
                    | uu____74473 -> false  in
                  let uu____74475 = cur_goal ()  in
                  bind uu____74475
                    (fun goal  ->
                       let uu____74481 =
                         let uu____74490 = FStar_Tactics_Types.goal_env goal
                            in
                         __tc uu____74490 tm  in
                       bind uu____74481
                         (fun uu____74505  ->
                            match uu____74505 with
                            | (tm1,t,guard) ->
                                let uu____74517 =
                                  FStar_Syntax_Util.arrow_formals_comp t  in
                                (match uu____74517 with
                                 | (bs,comp) ->
                                     let uu____74550 = lemma_or_sq comp  in
                                     (match uu____74550 with
                                      | FStar_Pervasives_Native.None  ->
                                          fail
                                            "not a lemma or squashed function"
                                      | FStar_Pervasives_Native.Some
                                          (pre,post) ->
                                          let uu____74570 =
                                            fold_left
                                              (fun uu____74632  ->
                                                 fun uu____74633  ->
                                                   match (uu____74632,
                                                           uu____74633)
                                                   with
                                                   | ((b,aq),(uvs,imps,subst1))
                                                       ->
                                                       let b_t =
                                                         FStar_Syntax_Subst.subst
                                                           subst1
                                                           b.FStar_Syntax_Syntax.sort
                                                          in
                                                       let uu____74784 =
                                                         is_unit_t b_t  in
                                                       if uu____74784
                                                       then
                                                         FStar_All.pipe_left
                                                           ret
                                                           (((FStar_Syntax_Util.exp_unit,
                                                               aq) :: uvs),
                                                             imps,
                                                             ((FStar_Syntax_Syntax.NT
                                                                 (b,
                                                                   FStar_Syntax_Util.exp_unit))
                                                             :: subst1))
                                                       else
                                                         (let uu____74907 =
                                                            let uu____74914 =
                                                              FStar_Tactics_Types.goal_env
                                                                goal
                                                               in
                                                            new_uvar
                                                              "apply_lemma"
                                                              uu____74914 b_t
                                                             in
                                                          bind uu____74907
                                                            (fun uu____74945 
                                                               ->
                                                               match uu____74945
                                                               with
                                                               | (t1,u) ->
                                                                   FStar_All.pipe_left
                                                                    ret
                                                                    (((t1,
                                                                    aq) ::
                                                                    uvs),
                                                                    ((t1, u)
                                                                    :: imps),
                                                                    ((FStar_Syntax_Syntax.NT
                                                                    (b, t1))
                                                                    ::
                                                                    subst1)))))
                                              ([], [], []) bs
                                             in
                                          bind uu____74570
                                            (fun uu____75131  ->
                                               match uu____75131 with
                                               | (uvs,implicits,subst1) ->
                                                   let implicits1 =
                                                     FStar_List.rev implicits
                                                      in
                                                   let uvs1 =
                                                     FStar_List.rev uvs  in
                                                   let pre1 =
                                                     FStar_Syntax_Subst.subst
                                                       subst1 pre
                                                      in
                                                   let post1 =
                                                     FStar_Syntax_Subst.subst
                                                       subst1 post
                                                      in
                                                   let uu____75219 =
                                                     let uu____75223 =
                                                       FStar_Tactics_Types.goal_env
                                                         goal
                                                        in
                                                     let uu____75224 =
                                                       FStar_Syntax_Util.mk_squash
                                                         FStar_Syntax_Syntax.U_zero
                                                         post1
                                                        in
                                                     let uu____75225 =
                                                       FStar_Tactics_Types.goal_type
                                                         goal
                                                        in
                                                     do_unify uu____75223
                                                       uu____75224
                                                       uu____75225
                                                      in
                                                   bind uu____75219
                                                     (fun b  ->
                                                        if
                                                          Prims.op_Negation b
                                                        then
                                                          let uu____75236 =
                                                            let uu____75238 =
                                                              FStar_Tactics_Types.goal_env
                                                                goal
                                                               in
                                                            tts uu____75238
                                                              tm1
                                                             in
                                                          let uu____75239 =
                                                            let uu____75241 =
                                                              FStar_Tactics_Types.goal_env
                                                                goal
                                                               in
                                                            let uu____75242 =
                                                              FStar_Syntax_Util.mk_squash
                                                                FStar_Syntax_Syntax.U_zero
                                                                post1
                                                               in
                                                            tts uu____75241
                                                              uu____75242
                                                             in
                                                          let uu____75243 =
                                                            let uu____75245 =
                                                              FStar_Tactics_Types.goal_env
                                                                goal
                                                               in
                                                            let uu____75246 =
                                                              FStar_Tactics_Types.goal_type
                                                                goal
                                                               in
                                                            tts uu____75245
                                                              uu____75246
                                                             in
                                                          fail3
                                                            "Cannot instantiate lemma %s (with postcondition: %s) to match goal (%s)"
                                                            uu____75236
                                                            uu____75239
                                                            uu____75243
                                                        else
                                                          (let uu____75250 =
                                                             solve' goal
                                                               FStar_Syntax_Util.exp_unit
                                                              in
                                                           bind uu____75250
                                                             (fun uu____75258
                                                                 ->
                                                                let is_free_uvar
                                                                  uv t1 =
                                                                  let free_uvars
                                                                    =
                                                                    let uu____75284
                                                                    =
                                                                    let uu____75287
                                                                    =
                                                                    FStar_Syntax_Free.uvars
                                                                    t1  in
                                                                    FStar_Util.set_elements
                                                                    uu____75287
                                                                     in
                                                                    FStar_List.map
                                                                    (fun x 
                                                                    ->
                                                                    x.FStar_Syntax_Syntax.ctx_uvar_head)
                                                                    uu____75284
                                                                     in
                                                                  FStar_List.existsML
                                                                    (
                                                                    fun u  ->
                                                                    FStar_Syntax_Unionfind.equiv
                                                                    u uv)
                                                                    free_uvars
                                                                   in
                                                                let appears
                                                                  uv goals =
                                                                  FStar_List.existsML
                                                                    (
                                                                    fun g' 
                                                                    ->
                                                                    let uu____75323
                                                                    =
                                                                    FStar_Tactics_Types.goal_type
                                                                    g'  in
                                                                    is_free_uvar
                                                                    uv
                                                                    uu____75323)
                                                                    goals
                                                                   in
                                                                let checkone
                                                                  t1 goals =
                                                                  let uu____75340
                                                                    =
                                                                    FStar_Syntax_Util.head_and_args
                                                                    t1  in
                                                                  match uu____75340
                                                                  with
                                                                  | (hd1,uu____75359)
                                                                    ->
                                                                    (match 
                                                                    hd1.FStar_Syntax_Syntax.n
                                                                    with
                                                                    | 
                                                                    FStar_Syntax_Syntax.Tm_uvar
                                                                    (uv,uu____75386)
                                                                    ->
                                                                    appears
                                                                    uv.FStar_Syntax_Syntax.ctx_uvar_head
                                                                    goals
                                                                    | 
                                                                    uu____75403
                                                                    -> false)
                                                                   in
                                                                let uu____75405
                                                                  =
                                                                  FStar_All.pipe_right
                                                                    implicits1
                                                                    (
                                                                    mapM
                                                                    (fun imp 
                                                                    ->
                                                                    let t1 =
                                                                    FStar_Util.now
                                                                    ()  in
                                                                    let uu____75448
                                                                    = imp  in
                                                                    match uu____75448
                                                                    with
                                                                    | 
                                                                    (term,ctx_uvar)
                                                                    ->
                                                                    let uu____75459
                                                                    =
                                                                    FStar_Syntax_Util.head_and_args
                                                                    term  in
                                                                    (match uu____75459
                                                                    with
                                                                    | 
                                                                    (hd1,uu____75481)
                                                                    ->
                                                                    let uu____75506
                                                                    =
                                                                    let uu____75507
                                                                    =
                                                                    FStar_Syntax_Subst.compress
                                                                    hd1  in
                                                                    uu____75507.FStar_Syntax_Syntax.n
                                                                     in
                                                                    (match uu____75506
                                                                    with
                                                                    | 
                                                                    FStar_Syntax_Syntax.Tm_uvar
                                                                    (ctx_uvar1,uu____75515)
                                                                    ->
                                                                    let goal1
                                                                    =
                                                                    bnorm_goal
                                                                    (let uu___1562_75535
                                                                    = goal
                                                                     in
                                                                    {
                                                                    FStar_Tactics_Types.goal_main_env
                                                                    =
                                                                    (uu___1562_75535.FStar_Tactics_Types.goal_main_env);
                                                                    FStar_Tactics_Types.goal_ctx_uvar
                                                                    =
                                                                    ctx_uvar1;
                                                                    FStar_Tactics_Types.opts
                                                                    =
                                                                    (uu___1562_75535.FStar_Tactics_Types.opts);
                                                                    FStar_Tactics_Types.is_guard
                                                                    =
                                                                    (uu___1562_75535.FStar_Tactics_Types.is_guard);
                                                                    FStar_Tactics_Types.label
                                                                    =
                                                                    (uu___1562_75535.FStar_Tactics_Types.label)
                                                                    })  in
                                                                    ret
                                                                    [goal1]
                                                                    | 
                                                                    uu____75538
                                                                    ->
                                                                    mlog
                                                                    (fun
                                                                    uu____75544
                                                                     ->
                                                                    let uu____75545
                                                                    =
                                                                    FStar_Syntax_Print.uvar_to_string
                                                                    ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_head
                                                                     in
                                                                    let uu____75547
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    term  in
                                                                    FStar_Util.print2
                                                                    "apply_lemma: arg %s unified to (%s)\n"
                                                                    uu____75545
                                                                    uu____75547)
                                                                    (fun
                                                                    uu____75554
                                                                     ->
                                                                    let env =
                                                                    let uu___1567_75556
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    goal  in
                                                                    {
                                                                    FStar_TypeChecker_Env.solver
                                                                    =
                                                                    (uu___1567_75556.FStar_TypeChecker_Env.solver);
                                                                    FStar_TypeChecker_Env.range
                                                                    =
                                                                    (uu___1567_75556.FStar_TypeChecker_Env.range);
                                                                    FStar_TypeChecker_Env.curmodule
                                                                    =
                                                                    (uu___1567_75556.FStar_TypeChecker_Env.curmodule);
                                                                    FStar_TypeChecker_Env.gamma
                                                                    =
                                                                    (ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_gamma);
                                                                    FStar_TypeChecker_Env.gamma_sig
                                                                    =
                                                                    (uu___1567_75556.FStar_TypeChecker_Env.gamma_sig);
                                                                    FStar_TypeChecker_Env.gamma_cache
                                                                    =
                                                                    (uu___1567_75556.FStar_TypeChecker_Env.gamma_cache);
                                                                    FStar_TypeChecker_Env.modules
                                                                    =
                                                                    (uu___1567_75556.FStar_TypeChecker_Env.modules);
                                                                    FStar_TypeChecker_Env.expected_typ
                                                                    =
                                                                    (uu___1567_75556.FStar_TypeChecker_Env.expected_typ);
                                                                    FStar_TypeChecker_Env.sigtab
                                                                    =
                                                                    (uu___1567_75556.FStar_TypeChecker_Env.sigtab);
                                                                    FStar_TypeChecker_Env.attrtab
                                                                    =
                                                                    (uu___1567_75556.FStar_TypeChecker_Env.attrtab);
                                                                    FStar_TypeChecker_Env.is_pattern
                                                                    =
                                                                    (uu___1567_75556.FStar_TypeChecker_Env.is_pattern);
                                                                    FStar_TypeChecker_Env.instantiate_imp
                                                                    =
                                                                    (uu___1567_75556.FStar_TypeChecker_Env.instantiate_imp);
                                                                    FStar_TypeChecker_Env.effects
                                                                    =
                                                                    (uu___1567_75556.FStar_TypeChecker_Env.effects);
                                                                    FStar_TypeChecker_Env.generalize
                                                                    =
                                                                    (uu___1567_75556.FStar_TypeChecker_Env.generalize);
                                                                    FStar_TypeChecker_Env.letrecs
                                                                    =
                                                                    (uu___1567_75556.FStar_TypeChecker_Env.letrecs);
                                                                    FStar_TypeChecker_Env.top_level
                                                                    =
                                                                    (uu___1567_75556.FStar_TypeChecker_Env.top_level);
                                                                    FStar_TypeChecker_Env.check_uvars
                                                                    =
                                                                    (uu___1567_75556.FStar_TypeChecker_Env.check_uvars);
                                                                    FStar_TypeChecker_Env.use_eq
                                                                    =
                                                                    (uu___1567_75556.FStar_TypeChecker_Env.use_eq);
                                                                    FStar_TypeChecker_Env.is_iface
                                                                    =
                                                                    (uu___1567_75556.FStar_TypeChecker_Env.is_iface);
                                                                    FStar_TypeChecker_Env.admit
                                                                    =
                                                                    (uu___1567_75556.FStar_TypeChecker_Env.admit);
                                                                    FStar_TypeChecker_Env.lax
                                                                    =
                                                                    (uu___1567_75556.FStar_TypeChecker_Env.lax);
                                                                    FStar_TypeChecker_Env.lax_universes
                                                                    =
                                                                    (uu___1567_75556.FStar_TypeChecker_Env.lax_universes);
                                                                    FStar_TypeChecker_Env.phase1
                                                                    =
                                                                    (uu___1567_75556.FStar_TypeChecker_Env.phase1);
                                                                    FStar_TypeChecker_Env.failhard
                                                                    =
                                                                    (uu___1567_75556.FStar_TypeChecker_Env.failhard);
                                                                    FStar_TypeChecker_Env.nosynth
                                                                    =
                                                                    (uu___1567_75556.FStar_TypeChecker_Env.nosynth);
                                                                    FStar_TypeChecker_Env.uvar_subtyping
                                                                    =
                                                                    (uu___1567_75556.FStar_TypeChecker_Env.uvar_subtyping);
                                                                    FStar_TypeChecker_Env.tc_term
                                                                    =
                                                                    (uu___1567_75556.FStar_TypeChecker_Env.tc_term);
                                                                    FStar_TypeChecker_Env.type_of
                                                                    =
                                                                    (uu___1567_75556.FStar_TypeChecker_Env.type_of);
                                                                    FStar_TypeChecker_Env.universe_of
                                                                    =
                                                                    (uu___1567_75556.FStar_TypeChecker_Env.universe_of);
                                                                    FStar_TypeChecker_Env.check_type_of
                                                                    =
                                                                    (uu___1567_75556.FStar_TypeChecker_Env.check_type_of);
                                                                    FStar_TypeChecker_Env.use_bv_sorts
                                                                    =
                                                                    (uu___1567_75556.FStar_TypeChecker_Env.use_bv_sorts);
                                                                    FStar_TypeChecker_Env.qtbl_name_and_index
                                                                    =
                                                                    (uu___1567_75556.FStar_TypeChecker_Env.qtbl_name_and_index);
                                                                    FStar_TypeChecker_Env.normalized_eff_names
                                                                    =
                                                                    (uu___1567_75556.FStar_TypeChecker_Env.normalized_eff_names);
                                                                    FStar_TypeChecker_Env.fv_delta_depths
                                                                    =
                                                                    (uu___1567_75556.FStar_TypeChecker_Env.fv_delta_depths);
                                                                    FStar_TypeChecker_Env.proof_ns
                                                                    =
                                                                    (uu___1567_75556.FStar_TypeChecker_Env.proof_ns);
                                                                    FStar_TypeChecker_Env.synth_hook
                                                                    =
                                                                    (uu___1567_75556.FStar_TypeChecker_Env.synth_hook);
                                                                    FStar_TypeChecker_Env.splice
                                                                    =
                                                                    (uu___1567_75556.FStar_TypeChecker_Env.splice);
                                                                    FStar_TypeChecker_Env.postprocess
                                                                    =
                                                                    (uu___1567_75556.FStar_TypeChecker_Env.postprocess);
                                                                    FStar_TypeChecker_Env.is_native_tactic
                                                                    =
                                                                    (uu___1567_75556.FStar_TypeChecker_Env.is_native_tactic);
                                                                    FStar_TypeChecker_Env.identifier_info
                                                                    =
                                                                    (uu___1567_75556.FStar_TypeChecker_Env.identifier_info);
                                                                    FStar_TypeChecker_Env.tc_hooks
                                                                    =
                                                                    (uu___1567_75556.FStar_TypeChecker_Env.tc_hooks);
                                                                    FStar_TypeChecker_Env.dsenv
                                                                    =
                                                                    (uu___1567_75556.FStar_TypeChecker_Env.dsenv);
                                                                    FStar_TypeChecker_Env.nbe
                                                                    =
                                                                    (uu___1567_75556.FStar_TypeChecker_Env.nbe)
                                                                    }  in
                                                                    let g_typ
                                                                    =
                                                                    FStar_TypeChecker_TcTerm.check_type_of_well_typed_term'
                                                                    true env
                                                                    term
                                                                    ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_typ
                                                                     in
                                                                    let uu____75559
                                                                    =
                                                                    let uu____75562
                                                                    =
                                                                    if
                                                                    ps.FStar_Tactics_Types.tac_verb_dbg
                                                                    then
                                                                    let uu____75566
                                                                    =
                                                                    FStar_Syntax_Print.ctx_uvar_to_string
                                                                    ctx_uvar
                                                                     in
                                                                    let uu____75568
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    term  in
                                                                    FStar_Util.format2
                                                                    "apply_lemma solved arg %s to %s\n"
                                                                    uu____75566
                                                                    uu____75568
                                                                    else
                                                                    "apply_lemma solved arg"
                                                                     in
                                                                    let uu____75574
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    goal  in
                                                                    proc_guard
                                                                    uu____75562
                                                                    uu____75574
                                                                    g_typ  in
                                                                    bind
                                                                    uu____75559
                                                                    (fun
                                                                    uu____75578
                                                                     ->
                                                                    ret []))))))
                                                                   in
                                                                bind
                                                                  uu____75405
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
                                                                    let uu____75642
                                                                    = f x xs1
                                                                     in
                                                                    if
                                                                    uu____75642
                                                                    then
                                                                    let uu____75647
                                                                    =
                                                                    filter' f
                                                                    xs1  in x
                                                                    ::
                                                                    uu____75647
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
                                                                    let uu____75662
                                                                    =
                                                                    let uu____75664
                                                                    =
                                                                    FStar_Tactics_Types.goal_witness
                                                                    g  in
                                                                    checkone
                                                                    uu____75664
                                                                    goals  in
                                                                    Prims.op_Negation
                                                                    uu____75662)
                                                                    sub_goals1
                                                                     in
                                                                    let uu____75665
                                                                    =
                                                                    let uu____75668
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    goal  in
                                                                    proc_guard
                                                                    "apply_lemma guard"
                                                                    uu____75668
                                                                    guard  in
                                                                    bind
                                                                    uu____75665
                                                                    (fun
                                                                    uu____75672
                                                                     ->
                                                                    let uu____75673
                                                                    =
                                                                    let uu____75676
                                                                    =
                                                                    let uu____75678
                                                                    =
                                                                    let uu____75680
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    goal  in
                                                                    let uu____75681
                                                                    =
                                                                    FStar_Syntax_Util.mk_squash
                                                                    FStar_Syntax_Syntax.U_zero
                                                                    pre1  in
                                                                    istrivial
                                                                    uu____75680
                                                                    uu____75681
                                                                     in
                                                                    Prims.op_Negation
                                                                    uu____75678
                                                                     in
                                                                    if
                                                                    uu____75676
                                                                    then
                                                                    let uu____75685
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    goal  in
                                                                    add_irrelevant_goal
                                                                    "apply_lemma precondition"
                                                                    uu____75685
                                                                    pre1
                                                                    goal.FStar_Tactics_Types.opts
                                                                    goal.FStar_Tactics_Types.label
                                                                    else
                                                                    ret ()
                                                                     in
                                                                    bind
                                                                    uu____75673
                                                                    (fun
                                                                    uu____75690
                                                                     ->
                                                                    add_goals
                                                                    sub_goals2)))))))))))))
         in
      focus uu____74444  in
    FStar_All.pipe_left (wrap_err "apply_lemma") uu____74441
  
let (destruct_eq' :
  FStar_Reflection_Data.typ ->
    (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.option)
  =
  fun typ  ->
    let uu____75714 = FStar_Syntax_Util.destruct_typ_as_formula typ  in
    match uu____75714 with
    | FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn
        (l,uu____75724::(e1,uu____75726)::(e2,uu____75728)::[])) when
        (FStar_Ident.lid_equals l FStar_Parser_Const.eq2_lid) ||
          (FStar_Ident.lid_equals l FStar_Parser_Const.c_eq2_lid)
        -> FStar_Pervasives_Native.Some (e1, e2)
    | uu____75789 -> FStar_Pervasives_Native.None
  
let (destruct_eq :
  FStar_Reflection_Data.typ ->
    (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.option)
  =
  fun typ  ->
    let uu____75814 = destruct_eq' typ  in
    match uu____75814 with
    | FStar_Pervasives_Native.Some t -> FStar_Pervasives_Native.Some t
    | FStar_Pervasives_Native.None  ->
        let uu____75844 = FStar_Syntax_Util.un_squash typ  in
        (match uu____75844 with
         | FStar_Pervasives_Native.Some typ1 -> destruct_eq' typ1
         | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None)
  
let (split_env :
  FStar_Syntax_Syntax.bv ->
    env ->
      (env * FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.bv Prims.list)
        FStar_Pervasives_Native.option)
  =
  fun bvar  ->
    fun e  ->
      let rec aux e1 =
        let uu____75913 = FStar_TypeChecker_Env.pop_bv e1  in
        match uu____75913 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (bv',e') ->
            if FStar_Syntax_Syntax.bv_eq bvar bv'
            then FStar_Pervasives_Native.Some (e', bv', [])
            else
              (let uu____75971 = aux e'  in
               FStar_Util.map_opt uu____75971
                 (fun uu____76002  ->
                    match uu____76002 with
                    | (e'',bv,bvs) -> (e'', bv, (bv' :: bvs))))
         in
      let uu____76028 = aux e  in
      FStar_Util.map_opt uu____76028
        (fun uu____76059  ->
           match uu____76059 with
           | (e',bv,bvs) -> (e', bv, (FStar_List.rev bvs)))
  
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
          let uu____76133 =
            let uu____76144 = FStar_Tactics_Types.goal_env g  in
            split_env b1 uu____76144  in
          FStar_Util.map_opt uu____76133
            (fun uu____76162  ->
               match uu____76162 with
               | (e0,b11,bvs) ->
                   let s1 bv =
                     let uu___1640_76184 = bv  in
                     let uu____76185 =
                       FStar_Syntax_Subst.subst s bv.FStar_Syntax_Syntax.sort
                        in
                     {
                       FStar_Syntax_Syntax.ppname =
                         (uu___1640_76184.FStar_Syntax_Syntax.ppname);
                       FStar_Syntax_Syntax.index =
                         (uu___1640_76184.FStar_Syntax_Syntax.index);
                       FStar_Syntax_Syntax.sort = uu____76185
                     }  in
                   let bvs1 = FStar_List.map s1 bvs  in
                   let new_env = push_bvs e0 (b2 :: bvs1)  in
                   let new_goal =
                     let uu___1644_76193 =
                       g.FStar_Tactics_Types.goal_ctx_uvar  in
                     let uu____76194 =
                       FStar_TypeChecker_Env.all_binders new_env  in
                     let uu____76203 =
                       let uu____76206 = FStar_Tactics_Types.goal_type g  in
                       FStar_Syntax_Subst.subst s uu____76206  in
                     {
                       FStar_Syntax_Syntax.ctx_uvar_head =
                         (uu___1644_76193.FStar_Syntax_Syntax.ctx_uvar_head);
                       FStar_Syntax_Syntax.ctx_uvar_gamma =
                         (new_env.FStar_TypeChecker_Env.gamma);
                       FStar_Syntax_Syntax.ctx_uvar_binders = uu____76194;
                       FStar_Syntax_Syntax.ctx_uvar_typ = uu____76203;
                       FStar_Syntax_Syntax.ctx_uvar_reason =
                         (uu___1644_76193.FStar_Syntax_Syntax.ctx_uvar_reason);
                       FStar_Syntax_Syntax.ctx_uvar_should_check =
                         (uu___1644_76193.FStar_Syntax_Syntax.ctx_uvar_should_check);
                       FStar_Syntax_Syntax.ctx_uvar_range =
                         (uu___1644_76193.FStar_Syntax_Syntax.ctx_uvar_range);
                       FStar_Syntax_Syntax.ctx_uvar_meta =
                         (uu___1644_76193.FStar_Syntax_Syntax.ctx_uvar_meta)
                     }  in
                   let uu___1647_76207 = g  in
                   {
                     FStar_Tactics_Types.goal_main_env =
                       (uu___1647_76207.FStar_Tactics_Types.goal_main_env);
                     FStar_Tactics_Types.goal_ctx_uvar = new_goal;
                     FStar_Tactics_Types.opts =
                       (uu___1647_76207.FStar_Tactics_Types.opts);
                     FStar_Tactics_Types.is_guard =
                       (uu___1647_76207.FStar_Tactics_Types.is_guard);
                     FStar_Tactics_Types.label =
                       (uu___1647_76207.FStar_Tactics_Types.label)
                   })
  
let (rewrite : FStar_Syntax_Syntax.binder -> unit tac) =
  fun h  ->
    let uu____76218 =
      let uu____76221 = cur_goal ()  in
      bind uu____76221
        (fun goal  ->
           let uu____76229 = h  in
           match uu____76229 with
           | (bv,uu____76233) ->
               mlog
                 (fun uu____76241  ->
                    let uu____76242 = FStar_Syntax_Print.bv_to_string bv  in
                    let uu____76244 =
                      FStar_Syntax_Print.term_to_string
                        bv.FStar_Syntax_Syntax.sort
                       in
                    FStar_Util.print2 "+++Rewrite %s : %s\n" uu____76242
                      uu____76244)
                 (fun uu____76249  ->
                    let uu____76250 =
                      let uu____76261 = FStar_Tactics_Types.goal_env goal  in
                      split_env bv uu____76261  in
                    match uu____76250 with
                    | FStar_Pervasives_Native.None  ->
                        fail "binder not found in environment"
                    | FStar_Pervasives_Native.Some (e0,bv1,bvs) ->
                        let uu____76288 =
                          destruct_eq bv1.FStar_Syntax_Syntax.sort  in
                        (match uu____76288 with
                         | FStar_Pervasives_Native.Some (x,e) ->
                             let uu____76303 =
                               let uu____76304 =
                                 FStar_Syntax_Subst.compress x  in
                               uu____76304.FStar_Syntax_Syntax.n  in
                             (match uu____76303 with
                              | FStar_Syntax_Syntax.Tm_name x1 ->
                                  let s = [FStar_Syntax_Syntax.NT (x1, e)]
                                     in
                                  let s1 bv2 =
                                    let uu___1670_76321 = bv2  in
                                    let uu____76322 =
                                      FStar_Syntax_Subst.subst s
                                        bv2.FStar_Syntax_Syntax.sort
                                       in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___1670_76321.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___1670_76321.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = uu____76322
                                    }  in
                                  let bvs1 = FStar_List.map s1 bvs  in
                                  let new_env = push_bvs e0 (bv1 :: bvs1)  in
                                  let new_goal =
                                    let uu___1674_76330 =
                                      goal.FStar_Tactics_Types.goal_ctx_uvar
                                       in
                                    let uu____76331 =
                                      FStar_TypeChecker_Env.all_binders
                                        new_env
                                       in
                                    let uu____76340 =
                                      let uu____76343 =
                                        FStar_Tactics_Types.goal_type goal
                                         in
                                      FStar_Syntax_Subst.subst s uu____76343
                                       in
                                    {
                                      FStar_Syntax_Syntax.ctx_uvar_head =
                                        (uu___1674_76330.FStar_Syntax_Syntax.ctx_uvar_head);
                                      FStar_Syntax_Syntax.ctx_uvar_gamma =
                                        (new_env.FStar_TypeChecker_Env.gamma);
                                      FStar_Syntax_Syntax.ctx_uvar_binders =
                                        uu____76331;
                                      FStar_Syntax_Syntax.ctx_uvar_typ =
                                        uu____76340;
                                      FStar_Syntax_Syntax.ctx_uvar_reason =
                                        (uu___1674_76330.FStar_Syntax_Syntax.ctx_uvar_reason);
                                      FStar_Syntax_Syntax.ctx_uvar_should_check
                                        =
                                        (uu___1674_76330.FStar_Syntax_Syntax.ctx_uvar_should_check);
                                      FStar_Syntax_Syntax.ctx_uvar_range =
                                        (uu___1674_76330.FStar_Syntax_Syntax.ctx_uvar_range);
                                      FStar_Syntax_Syntax.ctx_uvar_meta =
                                        (uu___1674_76330.FStar_Syntax_Syntax.ctx_uvar_meta)
                                    }  in
                                  replace_cur
                                    (let uu___1677_76346 = goal  in
                                     {
                                       FStar_Tactics_Types.goal_main_env =
                                         (uu___1677_76346.FStar_Tactics_Types.goal_main_env);
                                       FStar_Tactics_Types.goal_ctx_uvar =
                                         new_goal;
                                       FStar_Tactics_Types.opts =
                                         (uu___1677_76346.FStar_Tactics_Types.opts);
                                       FStar_Tactics_Types.is_guard =
                                         (uu___1677_76346.FStar_Tactics_Types.is_guard);
                                       FStar_Tactics_Types.label =
                                         (uu___1677_76346.FStar_Tactics_Types.label)
                                     })
                              | uu____76347 ->
                                  fail
                                    "Not an equality hypothesis with a variable on the LHS")
                         | uu____76349 -> fail "Not an equality hypothesis")))
       in
    FStar_All.pipe_left (wrap_err "rewrite") uu____76218
  
let (rename_to : FStar_Syntax_Syntax.binder -> Prims.string -> unit tac) =
  fun b  ->
    fun s  ->
      let uu____76379 =
        let uu____76382 = cur_goal ()  in
        bind uu____76382
          (fun goal  ->
             let uu____76393 = b  in
             match uu____76393 with
             | (bv,uu____76397) ->
                 let bv' =
                   let uu____76403 =
                     let uu___1688_76404 = bv  in
                     let uu____76405 =
                       FStar_Ident.mk_ident
                         (s,
                           ((bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange))
                        in
                     {
                       FStar_Syntax_Syntax.ppname = uu____76405;
                       FStar_Syntax_Syntax.index =
                         (uu___1688_76404.FStar_Syntax_Syntax.index);
                       FStar_Syntax_Syntax.sort =
                         (uu___1688_76404.FStar_Syntax_Syntax.sort)
                     }  in
                   FStar_Syntax_Syntax.freshen_bv uu____76403  in
                 let s1 =
                   let uu____76410 =
                     let uu____76411 =
                       let uu____76418 = FStar_Syntax_Syntax.bv_to_name bv'
                          in
                       (bv, uu____76418)  in
                     FStar_Syntax_Syntax.NT uu____76411  in
                   [uu____76410]  in
                 let uu____76423 = subst_goal bv bv' s1 goal  in
                 (match uu____76423 with
                  | FStar_Pervasives_Native.None  ->
                      fail "binder not found in environment"
                  | FStar_Pervasives_Native.Some goal1 -> replace_cur goal1))
         in
      FStar_All.pipe_left (wrap_err "rename_to") uu____76379
  
let (binder_retype : FStar_Syntax_Syntax.binder -> unit tac) =
  fun b  ->
    let uu____76445 =
      let uu____76448 = cur_goal ()  in
      bind uu____76448
        (fun goal  ->
           let uu____76457 = b  in
           match uu____76457 with
           | (bv,uu____76461) ->
               let uu____76466 =
                 let uu____76477 = FStar_Tactics_Types.goal_env goal  in
                 split_env bv uu____76477  in
               (match uu____76466 with
                | FStar_Pervasives_Native.None  ->
                    fail "binder is not present in environment"
                | FStar_Pervasives_Native.Some (e0,bv1,bvs) ->
                    let uu____76504 = FStar_Syntax_Util.type_u ()  in
                    (match uu____76504 with
                     | (ty,u) ->
                         let uu____76513 = new_uvar "binder_retype" e0 ty  in
                         bind uu____76513
                           (fun uu____76532  ->
                              match uu____76532 with
                              | (t',u_t') ->
                                  let bv'' =
                                    let uu___1712_76542 = bv1  in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___1712_76542.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___1712_76542.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = t'
                                    }  in
                                  let s =
                                    let uu____76546 =
                                      let uu____76547 =
                                        let uu____76554 =
                                          FStar_Syntax_Syntax.bv_to_name bv''
                                           in
                                        (bv1, uu____76554)  in
                                      FStar_Syntax_Syntax.NT uu____76547  in
                                    [uu____76546]  in
                                  let bvs1 =
                                    FStar_List.map
                                      (fun b1  ->
                                         let uu___1717_76566 = b1  in
                                         let uu____76567 =
                                           FStar_Syntax_Subst.subst s
                                             b1.FStar_Syntax_Syntax.sort
                                            in
                                         {
                                           FStar_Syntax_Syntax.ppname =
                                             (uu___1717_76566.FStar_Syntax_Syntax.ppname);
                                           FStar_Syntax_Syntax.index =
                                             (uu___1717_76566.FStar_Syntax_Syntax.index);
                                           FStar_Syntax_Syntax.sort =
                                             uu____76567
                                         }) bvs
                                     in
                                  let env' = push_bvs e0 (bv'' :: bvs1)  in
                                  bind __dismiss
                                    (fun uu____76574  ->
                                       let new_goal =
                                         let uu____76576 =
                                           FStar_Tactics_Types.goal_with_env
                                             goal env'
                                            in
                                         let uu____76577 =
                                           let uu____76578 =
                                             FStar_Tactics_Types.goal_type
                                               goal
                                              in
                                           FStar_Syntax_Subst.subst s
                                             uu____76578
                                            in
                                         FStar_Tactics_Types.goal_with_type
                                           uu____76576 uu____76577
                                          in
                                       let uu____76579 = add_goals [new_goal]
                                          in
                                       bind uu____76579
                                         (fun uu____76584  ->
                                            let uu____76585 =
                                              FStar_Syntax_Util.mk_eq2
                                                (FStar_Syntax_Syntax.U_succ u)
                                                ty
                                                bv1.FStar_Syntax_Syntax.sort
                                                t'
                                               in
                                            add_irrelevant_goal
                                              "binder_retype equation" e0
                                              uu____76585
                                              goal.FStar_Tactics_Types.opts
                                              goal.FStar_Tactics_Types.label))))))
       in
    FStar_All.pipe_left (wrap_err "binder_retype") uu____76445
  
let (norm_binder_type :
  FStar_Syntax_Embeddings.norm_step Prims.list ->
    FStar_Syntax_Syntax.binder -> unit tac)
  =
  fun s  ->
    fun b  ->
      let uu____76611 =
        let uu____76614 = cur_goal ()  in
        bind uu____76614
          (fun goal  ->
             let uu____76623 = b  in
             match uu____76623 with
             | (bv,uu____76627) ->
                 let uu____76632 =
                   let uu____76643 = FStar_Tactics_Types.goal_env goal  in
                   split_env bv uu____76643  in
                 (match uu____76632 with
                  | FStar_Pervasives_Native.None  ->
                      fail "binder is not present in environment"
                  | FStar_Pervasives_Native.Some (e0,bv1,bvs) ->
                      let steps =
                        let uu____76673 =
                          FStar_TypeChecker_Normalize.tr_norm_steps s  in
                        FStar_List.append
                          [FStar_TypeChecker_Env.Reify;
                          FStar_TypeChecker_Env.UnfoldTac] uu____76673
                         in
                      let sort' =
                        normalize steps e0 bv1.FStar_Syntax_Syntax.sort  in
                      let bv' =
                        let uu___1738_76678 = bv1  in
                        {
                          FStar_Syntax_Syntax.ppname =
                            (uu___1738_76678.FStar_Syntax_Syntax.ppname);
                          FStar_Syntax_Syntax.index =
                            (uu___1738_76678.FStar_Syntax_Syntax.index);
                          FStar_Syntax_Syntax.sort = sort'
                        }  in
                      let env' = push_bvs e0 (bv' :: bvs)  in
                      let uu____76680 =
                        FStar_Tactics_Types.goal_with_env goal env'  in
                      replace_cur uu____76680))
         in
      FStar_All.pipe_left (wrap_err "norm_binder_type") uu____76611
  
let (revert : unit -> unit tac) =
  fun uu____76693  ->
    let uu____76696 = cur_goal ()  in
    bind uu____76696
      (fun goal  ->
         let uu____76702 =
           let uu____76709 = FStar_Tactics_Types.goal_env goal  in
           FStar_TypeChecker_Env.pop_bv uu____76709  in
         match uu____76702 with
         | FStar_Pervasives_Native.None  ->
             fail "Cannot revert; empty context"
         | FStar_Pervasives_Native.Some (x,env') ->
             let typ' =
               let uu____76726 =
                 let uu____76729 = FStar_Tactics_Types.goal_type goal  in
                 FStar_Syntax_Syntax.mk_Total uu____76729  in
               FStar_Syntax_Util.arrow [(x, FStar_Pervasives_Native.None)]
                 uu____76726
                in
             let uu____76744 = new_uvar "revert" env' typ'  in
             bind uu____76744
               (fun uu____76760  ->
                  match uu____76760 with
                  | (r,u_r) ->
                      let uu____76769 =
                        let uu____76772 =
                          let uu____76773 =
                            let uu____76774 =
                              FStar_Tactics_Types.goal_type goal  in
                            uu____76774.FStar_Syntax_Syntax.pos  in
                          let uu____76777 =
                            let uu____76782 =
                              let uu____76783 =
                                let uu____76792 =
                                  FStar_Syntax_Syntax.bv_to_name x  in
                                FStar_Syntax_Syntax.as_arg uu____76792  in
                              [uu____76783]  in
                            FStar_Syntax_Syntax.mk_Tm_app r uu____76782  in
                          uu____76777 FStar_Pervasives_Native.None
                            uu____76773
                           in
                        set_solution goal uu____76772  in
                      bind uu____76769
                        (fun uu____76813  ->
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
      let uu____76827 = FStar_Syntax_Free.names t  in
      FStar_Util.set_mem bv uu____76827
  
let rec (clear : FStar_Syntax_Syntax.binder -> unit tac) =
  fun b  ->
    let bv = FStar_Pervasives_Native.fst b  in
    let uu____76843 = cur_goal ()  in
    bind uu____76843
      (fun goal  ->
         mlog
           (fun uu____76851  ->
              let uu____76852 = FStar_Syntax_Print.binder_to_string b  in
              let uu____76854 =
                let uu____76856 =
                  let uu____76858 =
                    let uu____76867 = FStar_Tactics_Types.goal_env goal  in
                    FStar_TypeChecker_Env.all_binders uu____76867  in
                  FStar_All.pipe_right uu____76858 FStar_List.length  in
                FStar_All.pipe_right uu____76856 FStar_Util.string_of_int  in
              FStar_Util.print2 "Clear of (%s), env has %s binders\n"
                uu____76852 uu____76854)
           (fun uu____76888  ->
              let uu____76889 =
                let uu____76900 = FStar_Tactics_Types.goal_env goal  in
                split_env bv uu____76900  in
              match uu____76889 with
              | FStar_Pervasives_Native.None  ->
                  fail "Cannot clear; binder not in environment"
              | FStar_Pervasives_Native.Some (e',bv1,bvs) ->
                  let rec check1 bvs1 =
                    match bvs1 with
                    | [] -> ret ()
                    | bv'::bvs2 ->
                        let uu____76945 =
                          free_in bv1 bv'.FStar_Syntax_Syntax.sort  in
                        if uu____76945
                        then
                          let uu____76950 =
                            let uu____76952 =
                              FStar_Syntax_Print.bv_to_string bv'  in
                            FStar_Util.format1
                              "Cannot clear; binder present in the type of %s"
                              uu____76952
                             in
                          fail uu____76950
                        else check1 bvs2
                     in
                  let uu____76957 =
                    let uu____76959 = FStar_Tactics_Types.goal_type goal  in
                    free_in bv1 uu____76959  in
                  if uu____76957
                  then fail "Cannot clear; binder present in goal"
                  else
                    (let uu____76966 = check1 bvs  in
                     bind uu____76966
                       (fun uu____76972  ->
                          let env' = push_bvs e' bvs  in
                          let uu____76974 =
                            let uu____76981 =
                              FStar_Tactics_Types.goal_type goal  in
                            new_uvar "clear.witness" env' uu____76981  in
                          bind uu____76974
                            (fun uu____76991  ->
                               match uu____76991 with
                               | (ut,uvar_ut) ->
                                   let uu____77000 = set_solution goal ut  in
                                   bind uu____77000
                                     (fun uu____77005  ->
                                        let uu____77006 =
                                          FStar_Tactics_Types.mk_goal env'
                                            uvar_ut
                                            goal.FStar_Tactics_Types.opts
                                            goal.FStar_Tactics_Types.is_guard
                                            goal.FStar_Tactics_Types.label
                                           in
                                        replace_cur uu____77006))))))
  
let (clear_top : unit -> unit tac) =
  fun uu____77014  ->
    let uu____77017 = cur_goal ()  in
    bind uu____77017
      (fun goal  ->
         let uu____77023 =
           let uu____77030 = FStar_Tactics_Types.goal_env goal  in
           FStar_TypeChecker_Env.pop_bv uu____77030  in
         match uu____77023 with
         | FStar_Pervasives_Native.None  ->
             fail "Cannot clear; empty context"
         | FStar_Pervasives_Native.Some (x,uu____77039) ->
             let uu____77044 = FStar_Syntax_Syntax.mk_binder x  in
             clear uu____77044)
  
let (prune : Prims.string -> unit tac) =
  fun s  ->
    let uu____77057 = cur_goal ()  in
    bind uu____77057
      (fun g  ->
         let ctx = FStar_Tactics_Types.goal_env g  in
         let ctx' =
           let uu____77067 = FStar_Ident.path_of_text s  in
           FStar_TypeChecker_Env.rem_proof_ns ctx uu____77067  in
         let g' = FStar_Tactics_Types.goal_with_env g ctx'  in
         bind __dismiss (fun uu____77070  -> add_goals [g']))
  
let (addns : Prims.string -> unit tac) =
  fun s  ->
    let uu____77083 = cur_goal ()  in
    bind uu____77083
      (fun g  ->
         let ctx = FStar_Tactics_Types.goal_env g  in
         let ctx' =
           let uu____77093 = FStar_Ident.path_of_text s  in
           FStar_TypeChecker_Env.add_proof_ns ctx uu____77093  in
         let g' = FStar_Tactics_Types.goal_with_env g ctx'  in
         bind __dismiss (fun uu____77096  -> add_goals [g']))
  
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
            let uu____77137 = FStar_Syntax_Subst.compress t  in
            uu____77137.FStar_Syntax_Syntax.n  in
          let uu____77140 =
            if d = FStar_Tactics_Types.TopDown
            then
              f env
                (let uu___1922_77147 = t  in
                 {
                   FStar_Syntax_Syntax.n = tn;
                   FStar_Syntax_Syntax.pos =
                     (uu___1922_77147.FStar_Syntax_Syntax.pos);
                   FStar_Syntax_Syntax.vars =
                     (uu___1922_77147.FStar_Syntax_Syntax.vars)
                 })
            else ret t  in
          bind uu____77140
            (fun t1  ->
               let ff = tac_fold_env d f env  in
               let tn1 =
                 let uu____77164 =
                   let uu____77165 = FStar_Syntax_Subst.compress t1  in
                   uu____77165.FStar_Syntax_Syntax.n  in
                 match uu____77164 with
                 | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
                     let uu____77196 = ff hd1  in
                     bind uu____77196
                       (fun hd2  ->
                          let fa uu____77222 =
                            match uu____77222 with
                            | (a,q) ->
                                let uu____77243 = ff a  in
                                bind uu____77243 (fun a1  -> ret (a1, q))
                             in
                          let uu____77262 = mapM fa args  in
                          bind uu____77262
                            (fun args1  ->
                               ret (FStar_Syntax_Syntax.Tm_app (hd2, args1))))
                 | FStar_Syntax_Syntax.Tm_abs (bs,t2,k) ->
                     let uu____77344 = FStar_Syntax_Subst.open_term bs t2  in
                     (match uu____77344 with
                      | (bs1,t') ->
                          let uu____77353 =
                            let uu____77356 =
                              FStar_TypeChecker_Env.push_binders env bs1  in
                            tac_fold_env d f uu____77356 t'  in
                          bind uu____77353
                            (fun t''  ->
                               let uu____77360 =
                                 let uu____77361 =
                                   let uu____77380 =
                                     FStar_Syntax_Subst.close_binders bs1  in
                                   let uu____77389 =
                                     FStar_Syntax_Subst.close bs1 t''  in
                                   (uu____77380, uu____77389, k)  in
                                 FStar_Syntax_Syntax.Tm_abs uu____77361  in
                               ret uu____77360))
                 | FStar_Syntax_Syntax.Tm_arrow (bs,k) -> ret tn
                 | FStar_Syntax_Syntax.Tm_match (hd1,brs) ->
                     let uu____77464 = ff hd1  in
                     bind uu____77464
                       (fun hd2  ->
                          let ffb br =
                            let uu____77479 =
                              FStar_Syntax_Subst.open_branch br  in
                            match uu____77479 with
                            | (pat,w,e) ->
                                let bvs = FStar_Syntax_Syntax.pat_bvs pat  in
                                let ff1 =
                                  let uu____77511 =
                                    FStar_TypeChecker_Env.push_bvs env bvs
                                     in
                                  tac_fold_env d f uu____77511  in
                                let uu____77512 = ff1 e  in
                                bind uu____77512
                                  (fun e1  ->
                                     let br1 =
                                       FStar_Syntax_Subst.close_branch
                                         (pat, w, e1)
                                        in
                                     ret br1)
                             in
                          let uu____77527 = mapM ffb brs  in
                          bind uu____77527
                            (fun brs1  ->
                               ret (FStar_Syntax_Syntax.Tm_match (hd2, brs1))))
                 | FStar_Syntax_Syntax.Tm_let
                     ((false
                       ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inl bv;
                          FStar_Syntax_Syntax.lbunivs = uu____77571;
                          FStar_Syntax_Syntax.lbtyp = uu____77572;
                          FStar_Syntax_Syntax.lbeff = uu____77573;
                          FStar_Syntax_Syntax.lbdef = def;
                          FStar_Syntax_Syntax.lbattrs = uu____77575;
                          FStar_Syntax_Syntax.lbpos = uu____77576;_}::[]),e)
                     ->
                     let lb =
                       let uu____77604 =
                         let uu____77605 = FStar_Syntax_Subst.compress t1  in
                         uu____77605.FStar_Syntax_Syntax.n  in
                       match uu____77604 with
                       | FStar_Syntax_Syntax.Tm_let
                           ((false ,lb::[]),uu____77609) -> lb
                       | uu____77625 -> failwith "impossible"  in
                     let fflb lb1 =
                       let uu____77635 = ff lb1.FStar_Syntax_Syntax.lbdef  in
                       bind uu____77635
                         (fun def1  ->
                            ret
                              (let uu___1875_77641 = lb1  in
                               {
                                 FStar_Syntax_Syntax.lbname =
                                   (uu___1875_77641.FStar_Syntax_Syntax.lbname);
                                 FStar_Syntax_Syntax.lbunivs =
                                   (uu___1875_77641.FStar_Syntax_Syntax.lbunivs);
                                 FStar_Syntax_Syntax.lbtyp =
                                   (uu___1875_77641.FStar_Syntax_Syntax.lbtyp);
                                 FStar_Syntax_Syntax.lbeff =
                                   (uu___1875_77641.FStar_Syntax_Syntax.lbeff);
                                 FStar_Syntax_Syntax.lbdef = def1;
                                 FStar_Syntax_Syntax.lbattrs =
                                   (uu___1875_77641.FStar_Syntax_Syntax.lbattrs);
                                 FStar_Syntax_Syntax.lbpos =
                                   (uu___1875_77641.FStar_Syntax_Syntax.lbpos)
                               }))
                        in
                     let uu____77642 = fflb lb  in
                     bind uu____77642
                       (fun lb1  ->
                          let uu____77652 =
                            let uu____77657 =
                              let uu____77658 =
                                FStar_Syntax_Syntax.mk_binder bv  in
                              [uu____77658]  in
                            FStar_Syntax_Subst.open_term uu____77657 e  in
                          match uu____77652 with
                          | (bs,e1) ->
                              let ff1 =
                                let uu____77688 =
                                  FStar_TypeChecker_Env.push_binders env bs
                                   in
                                tac_fold_env d f uu____77688  in
                              let uu____77689 = ff1 e1  in
                              bind uu____77689
                                (fun e2  ->
                                   let e3 = FStar_Syntax_Subst.close bs e2
                                      in
                                   ret
                                     (FStar_Syntax_Syntax.Tm_let
                                        ((false, [lb1]), e3))))
                 | FStar_Syntax_Syntax.Tm_let ((true ,lbs),e) ->
                     let fflb lb =
                       let uu____77736 = ff lb.FStar_Syntax_Syntax.lbdef  in
                       bind uu____77736
                         (fun def  ->
                            ret
                              (let uu___1893_77742 = lb  in
                               {
                                 FStar_Syntax_Syntax.lbname =
                                   (uu___1893_77742.FStar_Syntax_Syntax.lbname);
                                 FStar_Syntax_Syntax.lbunivs =
                                   (uu___1893_77742.FStar_Syntax_Syntax.lbunivs);
                                 FStar_Syntax_Syntax.lbtyp =
                                   (uu___1893_77742.FStar_Syntax_Syntax.lbtyp);
                                 FStar_Syntax_Syntax.lbeff =
                                   (uu___1893_77742.FStar_Syntax_Syntax.lbeff);
                                 FStar_Syntax_Syntax.lbdef = def;
                                 FStar_Syntax_Syntax.lbattrs =
                                   (uu___1893_77742.FStar_Syntax_Syntax.lbattrs);
                                 FStar_Syntax_Syntax.lbpos =
                                   (uu___1893_77742.FStar_Syntax_Syntax.lbpos)
                               }))
                        in
                     let uu____77743 = FStar_Syntax_Subst.open_let_rec lbs e
                        in
                     (match uu____77743 with
                      | (lbs1,e1) ->
                          let uu____77758 = mapM fflb lbs1  in
                          bind uu____77758
                            (fun lbs2  ->
                               let uu____77770 = ff e1  in
                               bind uu____77770
                                 (fun e2  ->
                                    let uu____77778 =
                                      FStar_Syntax_Subst.close_let_rec lbs2
                                        e2
                                       in
                                    match uu____77778 with
                                    | (lbs3,e3) ->
                                        ret
                                          (FStar_Syntax_Syntax.Tm_let
                                             ((true, lbs3), e3)))))
                 | FStar_Syntax_Syntax.Tm_ascribed (t2,asc,eff) ->
                     let uu____77849 = ff t2  in
                     bind uu____77849
                       (fun t3  ->
                          ret
                            (FStar_Syntax_Syntax.Tm_ascribed (t3, asc, eff)))
                 | FStar_Syntax_Syntax.Tm_meta (t2,m) ->
                     let uu____77880 = ff t2  in
                     bind uu____77880
                       (fun t3  -> ret (FStar_Syntax_Syntax.Tm_meta (t3, m)))
                 | uu____77887 -> ret tn  in
               bind tn1
                 (fun tn2  ->
                    let t' =
                      let uu___1917_77894 = t1  in
                      {
                        FStar_Syntax_Syntax.n = tn2;
                        FStar_Syntax_Syntax.pos =
                          (uu___1917_77894.FStar_Syntax_Syntax.pos);
                        FStar_Syntax_Syntax.vars =
                          (uu___1917_77894.FStar_Syntax_Syntax.vars)
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
              let uu____77941 =
                FStar_TypeChecker_TcTerm.tc_term
                  (let uu___1930_77950 = env  in
                   {
                     FStar_TypeChecker_Env.solver =
                       (uu___1930_77950.FStar_TypeChecker_Env.solver);
                     FStar_TypeChecker_Env.range =
                       (uu___1930_77950.FStar_TypeChecker_Env.range);
                     FStar_TypeChecker_Env.curmodule =
                       (uu___1930_77950.FStar_TypeChecker_Env.curmodule);
                     FStar_TypeChecker_Env.gamma =
                       (uu___1930_77950.FStar_TypeChecker_Env.gamma);
                     FStar_TypeChecker_Env.gamma_sig =
                       (uu___1930_77950.FStar_TypeChecker_Env.gamma_sig);
                     FStar_TypeChecker_Env.gamma_cache =
                       (uu___1930_77950.FStar_TypeChecker_Env.gamma_cache);
                     FStar_TypeChecker_Env.modules =
                       (uu___1930_77950.FStar_TypeChecker_Env.modules);
                     FStar_TypeChecker_Env.expected_typ =
                       (uu___1930_77950.FStar_TypeChecker_Env.expected_typ);
                     FStar_TypeChecker_Env.sigtab =
                       (uu___1930_77950.FStar_TypeChecker_Env.sigtab);
                     FStar_TypeChecker_Env.attrtab =
                       (uu___1930_77950.FStar_TypeChecker_Env.attrtab);
                     FStar_TypeChecker_Env.is_pattern =
                       (uu___1930_77950.FStar_TypeChecker_Env.is_pattern);
                     FStar_TypeChecker_Env.instantiate_imp =
                       (uu___1930_77950.FStar_TypeChecker_Env.instantiate_imp);
                     FStar_TypeChecker_Env.effects =
                       (uu___1930_77950.FStar_TypeChecker_Env.effects);
                     FStar_TypeChecker_Env.generalize =
                       (uu___1930_77950.FStar_TypeChecker_Env.generalize);
                     FStar_TypeChecker_Env.letrecs =
                       (uu___1930_77950.FStar_TypeChecker_Env.letrecs);
                     FStar_TypeChecker_Env.top_level =
                       (uu___1930_77950.FStar_TypeChecker_Env.top_level);
                     FStar_TypeChecker_Env.check_uvars =
                       (uu___1930_77950.FStar_TypeChecker_Env.check_uvars);
                     FStar_TypeChecker_Env.use_eq =
                       (uu___1930_77950.FStar_TypeChecker_Env.use_eq);
                     FStar_TypeChecker_Env.is_iface =
                       (uu___1930_77950.FStar_TypeChecker_Env.is_iface);
                     FStar_TypeChecker_Env.admit =
                       (uu___1930_77950.FStar_TypeChecker_Env.admit);
                     FStar_TypeChecker_Env.lax = true;
                     FStar_TypeChecker_Env.lax_universes =
                       (uu___1930_77950.FStar_TypeChecker_Env.lax_universes);
                     FStar_TypeChecker_Env.phase1 =
                       (uu___1930_77950.FStar_TypeChecker_Env.phase1);
                     FStar_TypeChecker_Env.failhard =
                       (uu___1930_77950.FStar_TypeChecker_Env.failhard);
                     FStar_TypeChecker_Env.nosynth =
                       (uu___1930_77950.FStar_TypeChecker_Env.nosynth);
                     FStar_TypeChecker_Env.uvar_subtyping =
                       (uu___1930_77950.FStar_TypeChecker_Env.uvar_subtyping);
                     FStar_TypeChecker_Env.tc_term =
                       (uu___1930_77950.FStar_TypeChecker_Env.tc_term);
                     FStar_TypeChecker_Env.type_of =
                       (uu___1930_77950.FStar_TypeChecker_Env.type_of);
                     FStar_TypeChecker_Env.universe_of =
                       (uu___1930_77950.FStar_TypeChecker_Env.universe_of);
                     FStar_TypeChecker_Env.check_type_of =
                       (uu___1930_77950.FStar_TypeChecker_Env.check_type_of);
                     FStar_TypeChecker_Env.use_bv_sorts =
                       (uu___1930_77950.FStar_TypeChecker_Env.use_bv_sorts);
                     FStar_TypeChecker_Env.qtbl_name_and_index =
                       (uu___1930_77950.FStar_TypeChecker_Env.qtbl_name_and_index);
                     FStar_TypeChecker_Env.normalized_eff_names =
                       (uu___1930_77950.FStar_TypeChecker_Env.normalized_eff_names);
                     FStar_TypeChecker_Env.fv_delta_depths =
                       (uu___1930_77950.FStar_TypeChecker_Env.fv_delta_depths);
                     FStar_TypeChecker_Env.proof_ns =
                       (uu___1930_77950.FStar_TypeChecker_Env.proof_ns);
                     FStar_TypeChecker_Env.synth_hook =
                       (uu___1930_77950.FStar_TypeChecker_Env.synth_hook);
                     FStar_TypeChecker_Env.splice =
                       (uu___1930_77950.FStar_TypeChecker_Env.splice);
                     FStar_TypeChecker_Env.postprocess =
                       (uu___1930_77950.FStar_TypeChecker_Env.postprocess);
                     FStar_TypeChecker_Env.is_native_tactic =
                       (uu___1930_77950.FStar_TypeChecker_Env.is_native_tactic);
                     FStar_TypeChecker_Env.identifier_info =
                       (uu___1930_77950.FStar_TypeChecker_Env.identifier_info);
                     FStar_TypeChecker_Env.tc_hooks =
                       (uu___1930_77950.FStar_TypeChecker_Env.tc_hooks);
                     FStar_TypeChecker_Env.dsenv =
                       (uu___1930_77950.FStar_TypeChecker_Env.dsenv);
                     FStar_TypeChecker_Env.nbe =
                       (uu___1930_77950.FStar_TypeChecker_Env.nbe)
                   }) t
                 in
              match uu____77941 with
              | (t1,lcomp,g) ->
                  let uu____77957 =
                    (let uu____77961 =
                       FStar_Syntax_Util.is_pure_or_ghost_lcomp lcomp  in
                     Prims.op_Negation uu____77961) ||
                      (let uu____77964 = FStar_TypeChecker_Env.is_trivial g
                          in
                       Prims.op_Negation uu____77964)
                     in
                  if uu____77957
                  then ret t1
                  else
                    (let rewrite_eq =
                       let typ = lcomp.FStar_Syntax_Syntax.res_typ  in
                       let uu____77975 = new_uvar "pointwise_rec" env typ  in
                       bind uu____77975
                         (fun uu____77992  ->
                            match uu____77992 with
                            | (ut,uvar_ut) ->
                                (log ps
                                   (fun uu____78005  ->
                                      let uu____78006 =
                                        FStar_Syntax_Print.term_to_string t1
                                         in
                                      let uu____78008 =
                                        FStar_Syntax_Print.term_to_string ut
                                         in
                                      FStar_Util.print2
                                        "Pointwise_rec: making equality\n\t%s ==\n\t%s\n"
                                        uu____78006 uu____78008);
                                 (let uu____78011 =
                                    let uu____78014 =
                                      let uu____78015 =
                                        FStar_TypeChecker_TcTerm.universe_of
                                          env typ
                                         in
                                      FStar_Syntax_Util.mk_eq2 uu____78015
                                        typ t1 ut
                                       in
                                    add_irrelevant_goal
                                      "pointwise_rec equation" env
                                      uu____78014 opts label1
                                     in
                                  bind uu____78011
                                    (fun uu____78019  ->
                                       let uu____78020 =
                                         bind tau
                                           (fun uu____78026  ->
                                              let ut1 =
                                                FStar_TypeChecker_Normalize.reduce_uvar_solutions
                                                  env ut
                                                 in
                                              log ps
                                                (fun uu____78032  ->
                                                   let uu____78033 =
                                                     FStar_Syntax_Print.term_to_string
                                                       t1
                                                      in
                                                   let uu____78035 =
                                                     FStar_Syntax_Print.term_to_string
                                                       ut1
                                                      in
                                                   FStar_Util.print2
                                                     "Pointwise_rec: succeeded rewriting\n\t%s to\n\t%s\n"
                                                     uu____78033 uu____78035);
                                              ret ut1)
                                          in
                                       focus uu____78020))))
                        in
                     let uu____78038 = catch rewrite_eq  in
                     bind uu____78038
                       (fun x  ->
                          match x with
                          | FStar_Util.Inl (FStar_Tactics_Types.TacticFailure
                              "SKIP") -> ret t1
                          | FStar_Util.Inl e -> traise e
                          | FStar_Util.Inr x1 -> ret x1))
  
type ctrl = FStar_BigInt.t
let (keepGoing : ctrl) = FStar_BigInt.zero 
let (proceedToNextSubtree : FStar_BigInt.bigint) = FStar_BigInt.one 
let (globalStop : FStar_BigInt.bigint) =
  FStar_BigInt.succ_big_int FStar_BigInt.one 
type rewrite_result = Prims.bool
let (skipThisTerm : Prims.bool) = false 
let (rewroteThisTerm : Prims.bool) = true 
type 'a ctrl_tac = ('a * ctrl) tac
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
          let uu____78256 = FStar_Syntax_Subst.compress t  in
          maybe_continue ctrl uu____78256
            (fun t1  ->
               let uu____78264 =
                 f env
                   (let uu___2007_78273 = t1  in
                    {
                      FStar_Syntax_Syntax.n = (t1.FStar_Syntax_Syntax.n);
                      FStar_Syntax_Syntax.pos =
                        (uu___2007_78273.FStar_Syntax_Syntax.pos);
                      FStar_Syntax_Syntax.vars =
                        (uu___2007_78273.FStar_Syntax_Syntax.vars)
                    })
                  in
               bind uu____78264
                 (fun uu____78289  ->
                    match uu____78289 with
                    | (t2,ctrl1) ->
                        maybe_continue ctrl1 t2
                          (fun t3  ->
                             let uu____78312 =
                               let uu____78313 =
                                 FStar_Syntax_Subst.compress t3  in
                               uu____78313.FStar_Syntax_Syntax.n  in
                             match uu____78312 with
                             | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
                                 let uu____78350 =
                                   ctrl_tac_fold f env ctrl1 hd1  in
                                 bind uu____78350
                                   (fun uu____78375  ->
                                      match uu____78375 with
                                      | (hd2,ctrl2) ->
                                          let ctrl3 = keep_going ctrl2  in
                                          let uu____78391 =
                                            ctrl_tac_fold_args f env ctrl3
                                              args
                                             in
                                          bind uu____78391
                                            (fun uu____78418  ->
                                               match uu____78418 with
                                               | (args1,ctrl4) ->
                                                   ret
                                                     ((let uu___1987_78448 =
                                                         t3  in
                                                       {
                                                         FStar_Syntax_Syntax.n
                                                           =
                                                           (FStar_Syntax_Syntax.Tm_app
                                                              (hd2, args1));
                                                         FStar_Syntax_Syntax.pos
                                                           =
                                                           (uu___1987_78448.FStar_Syntax_Syntax.pos);
                                                         FStar_Syntax_Syntax.vars
                                                           =
                                                           (uu___1987_78448.FStar_Syntax_Syntax.vars)
                                                       }), ctrl4)))
                             | FStar_Syntax_Syntax.Tm_abs (bs,t4,k) ->
                                 let uu____78490 =
                                   FStar_Syntax_Subst.open_term bs t4  in
                                 (match uu____78490 with
                                  | (bs1,t') ->
                                      let uu____78505 =
                                        let uu____78512 =
                                          FStar_TypeChecker_Env.push_binders
                                            env bs1
                                           in
                                        ctrl_tac_fold f uu____78512 ctrl1 t'
                                         in
                                      bind uu____78505
                                        (fun uu____78530  ->
                                           match uu____78530 with
                                           | (t'',ctrl2) ->
                                               let uu____78545 =
                                                 let uu____78552 =
                                                   let uu___2000_78555 = t4
                                                      in
                                                   let uu____78558 =
                                                     let uu____78559 =
                                                       let uu____78578 =
                                                         FStar_Syntax_Subst.close_binders
                                                           bs1
                                                          in
                                                       let uu____78587 =
                                                         FStar_Syntax_Subst.close
                                                           bs1 t''
                                                          in
                                                       (uu____78578,
                                                         uu____78587, k)
                                                        in
                                                     FStar_Syntax_Syntax.Tm_abs
                                                       uu____78559
                                                      in
                                                   {
                                                     FStar_Syntax_Syntax.n =
                                                       uu____78558;
                                                     FStar_Syntax_Syntax.pos
                                                       =
                                                       (uu___2000_78555.FStar_Syntax_Syntax.pos);
                                                     FStar_Syntax_Syntax.vars
                                                       =
                                                       (uu___2000_78555.FStar_Syntax_Syntax.vars)
                                                   }  in
                                                 (uu____78552, ctrl2)  in
                                               ret uu____78545))
                             | FStar_Syntax_Syntax.Tm_arrow (bs,k) ->
                                 ret (t3, ctrl1)
                             | uu____78640 -> ret (t3, ctrl1))))

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
              let uu____78687 = ctrl_tac_fold f env ctrl t  in
              bind uu____78687
                (fun uu____78711  ->
                   match uu____78711 with
                   | (t1,ctrl1) ->
                       let uu____78726 = ctrl_tac_fold_args f env ctrl1 ts1
                          in
                       bind uu____78726
                         (fun uu____78753  ->
                            match uu____78753 with
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
                let uu____78847 =
                  let uu____78855 =
                    add_irrelevant_goal "dummy" env FStar_Syntax_Util.t_true
                      opts label1
                     in
                  bind uu____78855
                    (fun uu____78866  ->
                       let uu____78867 = ctrl t1  in
                       bind uu____78867
                         (fun res  ->
                            let uu____78894 = trivial ()  in
                            bind uu____78894 (fun uu____78903  -> ret res)))
                   in
                bind uu____78847
                  (fun uu____78921  ->
                     match uu____78921 with
                     | (should_rewrite,ctrl1) ->
                         if Prims.op_Negation should_rewrite
                         then ret (t1, ctrl1)
                         else
                           (let uu____78950 =
                              FStar_TypeChecker_TcTerm.tc_term
                                (let uu___2037_78959 = env  in
                                 {
                                   FStar_TypeChecker_Env.solver =
                                     (uu___2037_78959.FStar_TypeChecker_Env.solver);
                                   FStar_TypeChecker_Env.range =
                                     (uu___2037_78959.FStar_TypeChecker_Env.range);
                                   FStar_TypeChecker_Env.curmodule =
                                     (uu___2037_78959.FStar_TypeChecker_Env.curmodule);
                                   FStar_TypeChecker_Env.gamma =
                                     (uu___2037_78959.FStar_TypeChecker_Env.gamma);
                                   FStar_TypeChecker_Env.gamma_sig =
                                     (uu___2037_78959.FStar_TypeChecker_Env.gamma_sig);
                                   FStar_TypeChecker_Env.gamma_cache =
                                     (uu___2037_78959.FStar_TypeChecker_Env.gamma_cache);
                                   FStar_TypeChecker_Env.modules =
                                     (uu___2037_78959.FStar_TypeChecker_Env.modules);
                                   FStar_TypeChecker_Env.expected_typ =
                                     (uu___2037_78959.FStar_TypeChecker_Env.expected_typ);
                                   FStar_TypeChecker_Env.sigtab =
                                     (uu___2037_78959.FStar_TypeChecker_Env.sigtab);
                                   FStar_TypeChecker_Env.attrtab =
                                     (uu___2037_78959.FStar_TypeChecker_Env.attrtab);
                                   FStar_TypeChecker_Env.is_pattern =
                                     (uu___2037_78959.FStar_TypeChecker_Env.is_pattern);
                                   FStar_TypeChecker_Env.instantiate_imp =
                                     (uu___2037_78959.FStar_TypeChecker_Env.instantiate_imp);
                                   FStar_TypeChecker_Env.effects =
                                     (uu___2037_78959.FStar_TypeChecker_Env.effects);
                                   FStar_TypeChecker_Env.generalize =
                                     (uu___2037_78959.FStar_TypeChecker_Env.generalize);
                                   FStar_TypeChecker_Env.letrecs =
                                     (uu___2037_78959.FStar_TypeChecker_Env.letrecs);
                                   FStar_TypeChecker_Env.top_level =
                                     (uu___2037_78959.FStar_TypeChecker_Env.top_level);
                                   FStar_TypeChecker_Env.check_uvars =
                                     (uu___2037_78959.FStar_TypeChecker_Env.check_uvars);
                                   FStar_TypeChecker_Env.use_eq =
                                     (uu___2037_78959.FStar_TypeChecker_Env.use_eq);
                                   FStar_TypeChecker_Env.is_iface =
                                     (uu___2037_78959.FStar_TypeChecker_Env.is_iface);
                                   FStar_TypeChecker_Env.admit =
                                     (uu___2037_78959.FStar_TypeChecker_Env.admit);
                                   FStar_TypeChecker_Env.lax = true;
                                   FStar_TypeChecker_Env.lax_universes =
                                     (uu___2037_78959.FStar_TypeChecker_Env.lax_universes);
                                   FStar_TypeChecker_Env.phase1 =
                                     (uu___2037_78959.FStar_TypeChecker_Env.phase1);
                                   FStar_TypeChecker_Env.failhard =
                                     (uu___2037_78959.FStar_TypeChecker_Env.failhard);
                                   FStar_TypeChecker_Env.nosynth =
                                     (uu___2037_78959.FStar_TypeChecker_Env.nosynth);
                                   FStar_TypeChecker_Env.uvar_subtyping =
                                     (uu___2037_78959.FStar_TypeChecker_Env.uvar_subtyping);
                                   FStar_TypeChecker_Env.tc_term =
                                     (uu___2037_78959.FStar_TypeChecker_Env.tc_term);
                                   FStar_TypeChecker_Env.type_of =
                                     (uu___2037_78959.FStar_TypeChecker_Env.type_of);
                                   FStar_TypeChecker_Env.universe_of =
                                     (uu___2037_78959.FStar_TypeChecker_Env.universe_of);
                                   FStar_TypeChecker_Env.check_type_of =
                                     (uu___2037_78959.FStar_TypeChecker_Env.check_type_of);
                                   FStar_TypeChecker_Env.use_bv_sorts =
                                     (uu___2037_78959.FStar_TypeChecker_Env.use_bv_sorts);
                                   FStar_TypeChecker_Env.qtbl_name_and_index
                                     =
                                     (uu___2037_78959.FStar_TypeChecker_Env.qtbl_name_and_index);
                                   FStar_TypeChecker_Env.normalized_eff_names
                                     =
                                     (uu___2037_78959.FStar_TypeChecker_Env.normalized_eff_names);
                                   FStar_TypeChecker_Env.fv_delta_depths =
                                     (uu___2037_78959.FStar_TypeChecker_Env.fv_delta_depths);
                                   FStar_TypeChecker_Env.proof_ns =
                                     (uu___2037_78959.FStar_TypeChecker_Env.proof_ns);
                                   FStar_TypeChecker_Env.synth_hook =
                                     (uu___2037_78959.FStar_TypeChecker_Env.synth_hook);
                                   FStar_TypeChecker_Env.splice =
                                     (uu___2037_78959.FStar_TypeChecker_Env.splice);
                                   FStar_TypeChecker_Env.postprocess =
                                     (uu___2037_78959.FStar_TypeChecker_Env.postprocess);
                                   FStar_TypeChecker_Env.is_native_tactic =
                                     (uu___2037_78959.FStar_TypeChecker_Env.is_native_tactic);
                                   FStar_TypeChecker_Env.identifier_info =
                                     (uu___2037_78959.FStar_TypeChecker_Env.identifier_info);
                                   FStar_TypeChecker_Env.tc_hooks =
                                     (uu___2037_78959.FStar_TypeChecker_Env.tc_hooks);
                                   FStar_TypeChecker_Env.dsenv =
                                     (uu___2037_78959.FStar_TypeChecker_Env.dsenv);
                                   FStar_TypeChecker_Env.nbe =
                                     (uu___2037_78959.FStar_TypeChecker_Env.nbe)
                                 }) t1
                               in
                            match uu____78950 with
                            | (t2,lcomp,g) ->
                                let uu____78970 =
                                  (let uu____78974 =
                                     FStar_Syntax_Util.is_pure_or_ghost_lcomp
                                       lcomp
                                      in
                                   Prims.op_Negation uu____78974) ||
                                    (let uu____78977 =
                                       FStar_TypeChecker_Env.is_trivial g  in
                                     Prims.op_Negation uu____78977)
                                   in
                                if uu____78970
                                then ret (t2, globalStop)
                                else
                                  (let typ =
                                     lcomp.FStar_Syntax_Syntax.res_typ  in
                                   let uu____78993 =
                                     new_uvar "pointwise_rec" env typ  in
                                   bind uu____78993
                                     (fun uu____79014  ->
                                        match uu____79014 with
                                        | (ut,uvar_ut) ->
                                            (log ps
                                               (fun uu____79031  ->
                                                  let uu____79032 =
                                                    FStar_Syntax_Print.term_to_string
                                                      t2
                                                     in
                                                  let uu____79034 =
                                                    FStar_Syntax_Print.term_to_string
                                                      ut
                                                     in
                                                  FStar_Util.print2
                                                    "Pointwise_rec: making equality\n\t%s ==\n\t%s\n"
                                                    uu____79032 uu____79034);
                                             (let uu____79037 =
                                                let uu____79040 =
                                                  let uu____79041 =
                                                    FStar_TypeChecker_TcTerm.universe_of
                                                      env typ
                                                     in
                                                  FStar_Syntax_Util.mk_eq2
                                                    uu____79041 typ t2 ut
                                                   in
                                                add_irrelevant_goal
                                                  "rewrite_rec equation" env
                                                  uu____79040 opts label1
                                                 in
                                              bind uu____79037
                                                (fun uu____79049  ->
                                                   let uu____79050 =
                                                     bind rewriter
                                                       (fun uu____79064  ->
                                                          let ut1 =
                                                            FStar_TypeChecker_Normalize.reduce_uvar_solutions
                                                              env ut
                                                             in
                                                          log ps
                                                            (fun uu____79070 
                                                               ->
                                                               let uu____79071
                                                                 =
                                                                 FStar_Syntax_Print.term_to_string
                                                                   t2
                                                                  in
                                                               let uu____79073
                                                                 =
                                                                 FStar_Syntax_Print.term_to_string
                                                                   ut1
                                                                  in
                                                               FStar_Util.print2
                                                                 "rewrite_rec: succeeded rewriting\n\t%s to\n\t%s\n"
                                                                 uu____79071
                                                                 uu____79073);
                                                          ret (ut1, ctrl1))
                                                      in
                                                   focus uu____79050)))))))
  
let (topdown_rewrite :
  (FStar_Syntax_Syntax.term -> (Prims.bool * FStar_BigInt.t) tac) ->
    unit tac -> unit tac)
  =
  fun ctrl  ->
    fun rewriter  ->
      let uu____79119 =
        bind get
          (fun ps  ->
             let uu____79129 =
               match ps.FStar_Tactics_Types.goals with
               | g::gs -> (g, gs)
               | [] -> failwith "no goals"  in
             match uu____79129 with
             | (g,gs) ->
                 let gt1 = FStar_Tactics_Types.goal_type g  in
                 (log ps
                    (fun uu____79167  ->
                       let uu____79168 =
                         FStar_Syntax_Print.term_to_string gt1  in
                       FStar_Util.print1 "Topdown_rewrite starting with %s\n"
                         uu____79168);
                  bind dismiss_all
                    (fun uu____79173  ->
                       let uu____79174 =
                         let uu____79181 = FStar_Tactics_Types.goal_env g  in
                         ctrl_tac_fold
                           (rewrite_rec ps ctrl rewriter
                              g.FStar_Tactics_Types.opts
                              g.FStar_Tactics_Types.label) uu____79181
                           keepGoing gt1
                          in
                       bind uu____79174
                         (fun uu____79193  ->
                            match uu____79193 with
                            | (gt',uu____79201) ->
                                (log ps
                                   (fun uu____79205  ->
                                      let uu____79206 =
                                        FStar_Syntax_Print.term_to_string gt'
                                         in
                                      FStar_Util.print1
                                        "Topdown_rewrite seems to have succeded with %s\n"
                                        uu____79206);
                                 (let uu____79209 = push_goals gs  in
                                  bind uu____79209
                                    (fun uu____79214  ->
                                       let uu____79215 =
                                         let uu____79218 =
                                           FStar_Tactics_Types.goal_with_type
                                             g gt'
                                            in
                                         [uu____79218]  in
                                       add_goals uu____79215)))))))
         in
      FStar_All.pipe_left (wrap_err "topdown_rewrite") uu____79119
  
let (pointwise : FStar_Tactics_Types.direction -> unit tac -> unit tac) =
  fun d  ->
    fun tau  ->
      let uu____79243 =
        bind get
          (fun ps  ->
             let uu____79253 =
               match ps.FStar_Tactics_Types.goals with
               | g::gs -> (g, gs)
               | [] -> failwith "no goals"  in
             match uu____79253 with
             | (g,gs) ->
                 let gt1 = FStar_Tactics_Types.goal_type g  in
                 (log ps
                    (fun uu____79291  ->
                       let uu____79292 =
                         FStar_Syntax_Print.term_to_string gt1  in
                       FStar_Util.print1 "Pointwise starting with %s\n"
                         uu____79292);
                  bind dismiss_all
                    (fun uu____79297  ->
                       let uu____79298 =
                         let uu____79301 = FStar_Tactics_Types.goal_env g  in
                         tac_fold_env d
                           (pointwise_rec ps tau g.FStar_Tactics_Types.opts
                              g.FStar_Tactics_Types.label) uu____79301 gt1
                          in
                       bind uu____79298
                         (fun gt'  ->
                            log ps
                              (fun uu____79309  ->
                                 let uu____79310 =
                                   FStar_Syntax_Print.term_to_string gt'  in
                                 FStar_Util.print1
                                   "Pointwise seems to have succeded with %s\n"
                                   uu____79310);
                            (let uu____79313 = push_goals gs  in
                             bind uu____79313
                               (fun uu____79318  ->
                                  let uu____79319 =
                                    let uu____79322 =
                                      FStar_Tactics_Types.goal_with_type g
                                        gt'
                                       in
                                    [uu____79322]  in
                                  add_goals uu____79319))))))
         in
      FStar_All.pipe_left (wrap_err "pointwise") uu____79243
  
let (trefl : unit -> unit tac) =
  fun uu____79335  ->
    let uu____79338 =
      let uu____79341 = cur_goal ()  in
      bind uu____79341
        (fun g  ->
           let uu____79359 =
             let uu____79364 = FStar_Tactics_Types.goal_type g  in
             FStar_Syntax_Util.un_squash uu____79364  in
           match uu____79359 with
           | FStar_Pervasives_Native.Some t ->
               let uu____79372 = FStar_Syntax_Util.head_and_args' t  in
               (match uu____79372 with
                | (hd1,args) ->
                    let uu____79411 =
                      let uu____79424 =
                        let uu____79425 = FStar_Syntax_Util.un_uinst hd1  in
                        uu____79425.FStar_Syntax_Syntax.n  in
                      (uu____79424, args)  in
                    (match uu____79411 with
                     | (FStar_Syntax_Syntax.Tm_fvar
                        fv,uu____79439::(l,uu____79441)::(r,uu____79443)::[])
                         when
                         FStar_Syntax_Syntax.fv_eq_lid fv
                           FStar_Parser_Const.eq2_lid
                         ->
                         let uu____79490 =
                           let uu____79494 = FStar_Tactics_Types.goal_env g
                              in
                           do_unify uu____79494 l r  in
                         bind uu____79490
                           (fun b  ->
                              if b
                              then solve' g FStar_Syntax_Util.exp_unit
                              else
                                (let l1 =
                                   let uu____79505 =
                                     FStar_Tactics_Types.goal_env g  in
                                   FStar_TypeChecker_Normalize.normalize
                                     [FStar_TypeChecker_Env.UnfoldUntil
                                        FStar_Syntax_Syntax.delta_constant;
                                     FStar_TypeChecker_Env.Primops;
                                     FStar_TypeChecker_Env.UnfoldTac]
                                     uu____79505 l
                                    in
                                 let r1 =
                                   let uu____79507 =
                                     FStar_Tactics_Types.goal_env g  in
                                   FStar_TypeChecker_Normalize.normalize
                                     [FStar_TypeChecker_Env.UnfoldUntil
                                        FStar_Syntax_Syntax.delta_constant;
                                     FStar_TypeChecker_Env.Primops;
                                     FStar_TypeChecker_Env.UnfoldTac]
                                     uu____79507 r
                                    in
                                 let uu____79508 =
                                   let uu____79512 =
                                     FStar_Tactics_Types.goal_env g  in
                                   do_unify uu____79512 l1 r1  in
                                 bind uu____79508
                                   (fun b1  ->
                                      if b1
                                      then
                                        solve' g FStar_Syntax_Util.exp_unit
                                      else
                                        (let uu____79522 =
                                           let uu____79524 =
                                             FStar_Tactics_Types.goal_env g
                                              in
                                           tts uu____79524 l1  in
                                         let uu____79525 =
                                           let uu____79527 =
                                             FStar_Tactics_Types.goal_env g
                                              in
                                           tts uu____79527 r1  in
                                         fail2
                                           "not a trivial equality ((%s) vs (%s))"
                                           uu____79522 uu____79525))))
                     | (hd2,uu____79530) ->
                         let uu____79547 =
                           let uu____79549 = FStar_Tactics_Types.goal_env g
                              in
                           tts uu____79549 t  in
                         fail1 "trefl: not an equality (%s)" uu____79547))
           | FStar_Pervasives_Native.None  -> fail "not an irrelevant goal")
       in
    FStar_All.pipe_left (wrap_err "trefl") uu____79338
  
let (dup : unit -> unit tac) =
  fun uu____79566  ->
    let uu____79569 = cur_goal ()  in
    bind uu____79569
      (fun g  ->
         let uu____79575 =
           let uu____79582 = FStar_Tactics_Types.goal_env g  in
           let uu____79583 = FStar_Tactics_Types.goal_type g  in
           new_uvar "dup" uu____79582 uu____79583  in
         bind uu____79575
           (fun uu____79593  ->
              match uu____79593 with
              | (u,u_uvar) ->
                  let g' =
                    let uu___2129_79603 = g  in
                    {
                      FStar_Tactics_Types.goal_main_env =
                        (uu___2129_79603.FStar_Tactics_Types.goal_main_env);
                      FStar_Tactics_Types.goal_ctx_uvar = u_uvar;
                      FStar_Tactics_Types.opts =
                        (uu___2129_79603.FStar_Tactics_Types.opts);
                      FStar_Tactics_Types.is_guard =
                        (uu___2129_79603.FStar_Tactics_Types.is_guard);
                      FStar_Tactics_Types.label =
                        (uu___2129_79603.FStar_Tactics_Types.label)
                    }  in
                  bind __dismiss
                    (fun uu____79606  ->
                       let uu____79607 =
                         let uu____79610 = FStar_Tactics_Types.goal_env g  in
                         let uu____79611 =
                           let uu____79612 =
                             let uu____79613 = FStar_Tactics_Types.goal_env g
                                in
                             let uu____79614 =
                               FStar_Tactics_Types.goal_type g  in
                             FStar_TypeChecker_TcTerm.universe_of uu____79613
                               uu____79614
                              in
                           let uu____79615 = FStar_Tactics_Types.goal_type g
                              in
                           let uu____79616 =
                             FStar_Tactics_Types.goal_witness g  in
                           FStar_Syntax_Util.mk_eq2 uu____79612 uu____79615 u
                             uu____79616
                            in
                         add_irrelevant_goal "dup equation" uu____79610
                           uu____79611 g.FStar_Tactics_Types.opts
                           g.FStar_Tactics_Types.label
                          in
                       bind uu____79607
                         (fun uu____79620  ->
                            let uu____79621 = add_goals [g']  in
                            bind uu____79621 (fun uu____79625  -> ret ())))))
  
let rec longest_prefix :
  'a .
    ('a -> 'a -> Prims.bool) ->
      'a Prims.list ->
        'a Prims.list -> ('a Prims.list * 'a Prims.list * 'a Prims.list)
  =
  fun f  ->
    fun l1  ->
      fun l2  ->
        let rec aux acc l11 l21 =
          match (l11, l21) with
          | (x::xs,y::ys) ->
              let uu____79751 = f x y  in
              if uu____79751 then aux (x :: acc) xs ys else (acc, xs, ys)
          | uu____79774 -> (acc, l11, l21)  in
        let uu____79789 = aux [] l1 l2  in
        match uu____79789 with | (pr,t1,t2) -> ((FStar_List.rev pr), t1, t2)
  
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
      let uu____79895 = get_phi g1  in
      match uu____79895 with
      | FStar_Pervasives_Native.None  -> fail "goal 1 is not irrelevant"
      | FStar_Pervasives_Native.Some phi1 ->
          let uu____79902 = get_phi g2  in
          (match uu____79902 with
           | FStar_Pervasives_Native.None  -> fail "goal 2 is not irrelevant"
           | FStar_Pervasives_Native.Some phi2 ->
               let gamma1 =
                 (g1.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_gamma
                  in
               let gamma2 =
                 (g2.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_gamma
                  in
               let uu____79915 =
                 longest_prefix FStar_Syntax_Syntax.eq_binding
                   (FStar_List.rev gamma1) (FStar_List.rev gamma2)
                  in
               (match uu____79915 with
                | (gamma,r1,r2) ->
                    let t1 =
                      let uu____79946 =
                        FStar_TypeChecker_Env.binders_of_bindings
                          (FStar_List.rev r1)
                         in
                      close_forall_no_univs1 uu____79946 phi1  in
                    let t2 =
                      let uu____79956 =
                        FStar_TypeChecker_Env.binders_of_bindings
                          (FStar_List.rev r2)
                         in
                      close_forall_no_univs1 uu____79956 phi2  in
                    let uu____79965 =
                      set_solution g1 FStar_Syntax_Util.exp_unit  in
                    bind uu____79965
                      (fun uu____79970  ->
                         let uu____79971 =
                           set_solution g2 FStar_Syntax_Util.exp_unit  in
                         bind uu____79971
                           (fun uu____79978  ->
                              let ng = FStar_Syntax_Util.mk_conj t1 t2  in
                              let nenv =
                                let uu___2180_79983 =
                                  FStar_Tactics_Types.goal_env g1  in
                                let uu____79984 =
                                  FStar_Util.smap_create
                                    (Prims.parse_int "100")
                                   in
                                {
                                  FStar_TypeChecker_Env.solver =
                                    (uu___2180_79983.FStar_TypeChecker_Env.solver);
                                  FStar_TypeChecker_Env.range =
                                    (uu___2180_79983.FStar_TypeChecker_Env.range);
                                  FStar_TypeChecker_Env.curmodule =
                                    (uu___2180_79983.FStar_TypeChecker_Env.curmodule);
                                  FStar_TypeChecker_Env.gamma =
                                    (FStar_List.rev gamma);
                                  FStar_TypeChecker_Env.gamma_sig =
                                    (uu___2180_79983.FStar_TypeChecker_Env.gamma_sig);
                                  FStar_TypeChecker_Env.gamma_cache =
                                    uu____79984;
                                  FStar_TypeChecker_Env.modules =
                                    (uu___2180_79983.FStar_TypeChecker_Env.modules);
                                  FStar_TypeChecker_Env.expected_typ =
                                    (uu___2180_79983.FStar_TypeChecker_Env.expected_typ);
                                  FStar_TypeChecker_Env.sigtab =
                                    (uu___2180_79983.FStar_TypeChecker_Env.sigtab);
                                  FStar_TypeChecker_Env.attrtab =
                                    (uu___2180_79983.FStar_TypeChecker_Env.attrtab);
                                  FStar_TypeChecker_Env.is_pattern =
                                    (uu___2180_79983.FStar_TypeChecker_Env.is_pattern);
                                  FStar_TypeChecker_Env.instantiate_imp =
                                    (uu___2180_79983.FStar_TypeChecker_Env.instantiate_imp);
                                  FStar_TypeChecker_Env.effects =
                                    (uu___2180_79983.FStar_TypeChecker_Env.effects);
                                  FStar_TypeChecker_Env.generalize =
                                    (uu___2180_79983.FStar_TypeChecker_Env.generalize);
                                  FStar_TypeChecker_Env.letrecs =
                                    (uu___2180_79983.FStar_TypeChecker_Env.letrecs);
                                  FStar_TypeChecker_Env.top_level =
                                    (uu___2180_79983.FStar_TypeChecker_Env.top_level);
                                  FStar_TypeChecker_Env.check_uvars =
                                    (uu___2180_79983.FStar_TypeChecker_Env.check_uvars);
                                  FStar_TypeChecker_Env.use_eq =
                                    (uu___2180_79983.FStar_TypeChecker_Env.use_eq);
                                  FStar_TypeChecker_Env.is_iface =
                                    (uu___2180_79983.FStar_TypeChecker_Env.is_iface);
                                  FStar_TypeChecker_Env.admit =
                                    (uu___2180_79983.FStar_TypeChecker_Env.admit);
                                  FStar_TypeChecker_Env.lax =
                                    (uu___2180_79983.FStar_TypeChecker_Env.lax);
                                  FStar_TypeChecker_Env.lax_universes =
                                    (uu___2180_79983.FStar_TypeChecker_Env.lax_universes);
                                  FStar_TypeChecker_Env.phase1 =
                                    (uu___2180_79983.FStar_TypeChecker_Env.phase1);
                                  FStar_TypeChecker_Env.failhard =
                                    (uu___2180_79983.FStar_TypeChecker_Env.failhard);
                                  FStar_TypeChecker_Env.nosynth =
                                    (uu___2180_79983.FStar_TypeChecker_Env.nosynth);
                                  FStar_TypeChecker_Env.uvar_subtyping =
                                    (uu___2180_79983.FStar_TypeChecker_Env.uvar_subtyping);
                                  FStar_TypeChecker_Env.tc_term =
                                    (uu___2180_79983.FStar_TypeChecker_Env.tc_term);
                                  FStar_TypeChecker_Env.type_of =
                                    (uu___2180_79983.FStar_TypeChecker_Env.type_of);
                                  FStar_TypeChecker_Env.universe_of =
                                    (uu___2180_79983.FStar_TypeChecker_Env.universe_of);
                                  FStar_TypeChecker_Env.check_type_of =
                                    (uu___2180_79983.FStar_TypeChecker_Env.check_type_of);
                                  FStar_TypeChecker_Env.use_bv_sorts =
                                    (uu___2180_79983.FStar_TypeChecker_Env.use_bv_sorts);
                                  FStar_TypeChecker_Env.qtbl_name_and_index =
                                    (uu___2180_79983.FStar_TypeChecker_Env.qtbl_name_and_index);
                                  FStar_TypeChecker_Env.normalized_eff_names
                                    =
                                    (uu___2180_79983.FStar_TypeChecker_Env.normalized_eff_names);
                                  FStar_TypeChecker_Env.fv_delta_depths =
                                    (uu___2180_79983.FStar_TypeChecker_Env.fv_delta_depths);
                                  FStar_TypeChecker_Env.proof_ns =
                                    (uu___2180_79983.FStar_TypeChecker_Env.proof_ns);
                                  FStar_TypeChecker_Env.synth_hook =
                                    (uu___2180_79983.FStar_TypeChecker_Env.synth_hook);
                                  FStar_TypeChecker_Env.splice =
                                    (uu___2180_79983.FStar_TypeChecker_Env.splice);
                                  FStar_TypeChecker_Env.postprocess =
                                    (uu___2180_79983.FStar_TypeChecker_Env.postprocess);
                                  FStar_TypeChecker_Env.is_native_tactic =
                                    (uu___2180_79983.FStar_TypeChecker_Env.is_native_tactic);
                                  FStar_TypeChecker_Env.identifier_info =
                                    (uu___2180_79983.FStar_TypeChecker_Env.identifier_info);
                                  FStar_TypeChecker_Env.tc_hooks =
                                    (uu___2180_79983.FStar_TypeChecker_Env.tc_hooks);
                                  FStar_TypeChecker_Env.dsenv =
                                    (uu___2180_79983.FStar_TypeChecker_Env.dsenv);
                                  FStar_TypeChecker_Env.nbe =
                                    (uu___2180_79983.FStar_TypeChecker_Env.nbe)
                                }  in
                              let uu____79988 =
                                mk_irrelevant_goal "joined" nenv ng
                                  g1.FStar_Tactics_Types.opts
                                  g1.FStar_Tactics_Types.label
                                 in
                              bind uu____79988
                                (fun goal  ->
                                   mlog
                                     (fun uu____79998  ->
                                        let uu____79999 =
                                          goal_to_string_verbose g1  in
                                        let uu____80001 =
                                          goal_to_string_verbose g2  in
                                        let uu____80003 =
                                          goal_to_string_verbose goal  in
                                        FStar_Util.print3
                                          "join_goals of\n(%s)\nand\n(%s)\n= (%s)\n"
                                          uu____79999 uu____80001 uu____80003)
                                     (fun uu____80007  -> ret goal))))))
  
let (join : unit -> unit tac) =
  fun uu____80015  ->
    bind get
      (fun ps  ->
         match ps.FStar_Tactics_Types.goals with
         | g1::g2::gs ->
             let uu____80031 =
               set
                 (let uu___2195_80036 = ps  in
                  {
                    FStar_Tactics_Types.main_context =
                      (uu___2195_80036.FStar_Tactics_Types.main_context);
                    FStar_Tactics_Types.main_goal =
                      (uu___2195_80036.FStar_Tactics_Types.main_goal);
                    FStar_Tactics_Types.all_implicits =
                      (uu___2195_80036.FStar_Tactics_Types.all_implicits);
                    FStar_Tactics_Types.goals = gs;
                    FStar_Tactics_Types.smt_goals =
                      (uu___2195_80036.FStar_Tactics_Types.smt_goals);
                    FStar_Tactics_Types.depth =
                      (uu___2195_80036.FStar_Tactics_Types.depth);
                    FStar_Tactics_Types.__dump =
                      (uu___2195_80036.FStar_Tactics_Types.__dump);
                    FStar_Tactics_Types.psc =
                      (uu___2195_80036.FStar_Tactics_Types.psc);
                    FStar_Tactics_Types.entry_range =
                      (uu___2195_80036.FStar_Tactics_Types.entry_range);
                    FStar_Tactics_Types.guard_policy =
                      (uu___2195_80036.FStar_Tactics_Types.guard_policy);
                    FStar_Tactics_Types.freshness =
                      (uu___2195_80036.FStar_Tactics_Types.freshness);
                    FStar_Tactics_Types.tac_verb_dbg =
                      (uu___2195_80036.FStar_Tactics_Types.tac_verb_dbg);
                    FStar_Tactics_Types.local_state =
                      (uu___2195_80036.FStar_Tactics_Types.local_state)
                  })
                in
             bind uu____80031
               (fun uu____80039  ->
                  let uu____80040 = join_goals g1 g2  in
                  bind uu____80040 (fun g12  -> add_goals [g12]))
         | uu____80045 -> fail "join: less than 2 goals")
  
let (cases :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term) tac)
  =
  fun t  ->
    let uu____80067 =
      let uu____80074 = cur_goal ()  in
      bind uu____80074
        (fun g  ->
           let uu____80084 =
             let uu____80093 = FStar_Tactics_Types.goal_env g  in
             __tc uu____80093 t  in
           bind uu____80084
             (fun uu____80121  ->
                match uu____80121 with
                | (t1,typ,guard) ->
                    let uu____80137 = FStar_Syntax_Util.head_and_args typ  in
                    (match uu____80137 with
                     | (hd1,args) ->
                         let uu____80186 =
                           let uu____80201 =
                             let uu____80202 = FStar_Syntax_Util.un_uinst hd1
                                in
                             uu____80202.FStar_Syntax_Syntax.n  in
                           (uu____80201, args)  in
                         (match uu____80186 with
                          | (FStar_Syntax_Syntax.Tm_fvar
                             fv,(p,uu____80223)::(q,uu____80225)::[]) when
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
                                let uu____80279 =
                                  let uu____80280 =
                                    FStar_Tactics_Types.goal_env g  in
                                  FStar_TypeChecker_Env.push_bv uu____80280
                                    v_p
                                   in
                                FStar_Tactics_Types.goal_with_env g
                                  uu____80279
                                 in
                              let g2 =
                                let uu____80282 =
                                  let uu____80283 =
                                    FStar_Tactics_Types.goal_env g  in
                                  FStar_TypeChecker_Env.push_bv uu____80283
                                    v_q
                                   in
                                FStar_Tactics_Types.goal_with_env g
                                  uu____80282
                                 in
                              bind __dismiss
                                (fun uu____80290  ->
                                   let uu____80291 = add_goals [g1; g2]  in
                                   bind uu____80291
                                     (fun uu____80300  ->
                                        let uu____80301 =
                                          let uu____80306 =
                                            FStar_Syntax_Syntax.bv_to_name
                                              v_p
                                             in
                                          let uu____80307 =
                                            FStar_Syntax_Syntax.bv_to_name
                                              v_q
                                             in
                                          (uu____80306, uu____80307)  in
                                        ret uu____80301))
                          | uu____80312 ->
                              let uu____80327 =
                                let uu____80329 =
                                  FStar_Tactics_Types.goal_env g  in
                                tts uu____80329 typ  in
                              fail1 "Not a disjunction: %s" uu____80327))))
       in
    FStar_All.pipe_left (wrap_err "cases") uu____80067
  
let (set_options : Prims.string -> unit tac) =
  fun s  ->
    let uu____80364 =
      let uu____80367 = cur_goal ()  in
      bind uu____80367
        (fun g  ->
           FStar_Options.push ();
           (let uu____80380 = FStar_Util.smap_copy g.FStar_Tactics_Types.opts
               in
            FStar_Options.set uu____80380);
           (let res = FStar_Options.set_options FStar_Options.Set s  in
            let opts' = FStar_Options.peek ()  in
            FStar_Options.pop ();
            (match res with
             | FStar_Getopt.Success  ->
                 let g' =
                   let uu___2232_80387 = g  in
                   {
                     FStar_Tactics_Types.goal_main_env =
                       (uu___2232_80387.FStar_Tactics_Types.goal_main_env);
                     FStar_Tactics_Types.goal_ctx_uvar =
                       (uu___2232_80387.FStar_Tactics_Types.goal_ctx_uvar);
                     FStar_Tactics_Types.opts = opts';
                     FStar_Tactics_Types.is_guard =
                       (uu___2232_80387.FStar_Tactics_Types.is_guard);
                     FStar_Tactics_Types.label =
                       (uu___2232_80387.FStar_Tactics_Types.label)
                   }  in
                 replace_cur g'
             | FStar_Getopt.Error err ->
                 fail2 "Setting options `%s` failed: %s" s err
             | FStar_Getopt.Help  ->
                 fail1 "Setting options `%s` failed (got `Help`?)" s)))
       in
    FStar_All.pipe_left (wrap_err "set_options") uu____80364
  
let (top_env : unit -> env tac) =
  fun uu____80404  ->
    bind get
      (fun ps  -> FStar_All.pipe_left ret ps.FStar_Tactics_Types.main_context)
  
let (lax_on : unit -> Prims.bool tac) =
  fun uu____80419  ->
    let uu____80423 = cur_goal ()  in
    bind uu____80423
      (fun g  ->
         let uu____80430 =
           (FStar_Options.lax ()) ||
             (let uu____80433 = FStar_Tactics_Types.goal_env g  in
              uu____80433.FStar_TypeChecker_Env.lax)
            in
         ret uu____80430)
  
let (unquote :
  FStar_Reflection_Data.typ ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term tac)
  =
  fun ty  ->
    fun tm  ->
      let uu____80450 =
        mlog
          (fun uu____80455  ->
             let uu____80456 = FStar_Syntax_Print.term_to_string tm  in
             FStar_Util.print1 "unquote: tm = %s\n" uu____80456)
          (fun uu____80461  ->
             let uu____80462 = cur_goal ()  in
             bind uu____80462
               (fun goal  ->
                  let env =
                    let uu____80470 = FStar_Tactics_Types.goal_env goal  in
                    FStar_TypeChecker_Env.set_expected_typ uu____80470 ty  in
                  let uu____80471 = __tc_ghost env tm  in
                  bind uu____80471
                    (fun uu____80490  ->
                       match uu____80490 with
                       | (tm1,typ,guard) ->
                           mlog
                             (fun uu____80504  ->
                                let uu____80505 =
                                  FStar_Syntax_Print.term_to_string tm1  in
                                FStar_Util.print1 "unquote: tm' = %s\n"
                                  uu____80505)
                             (fun uu____80509  ->
                                mlog
                                  (fun uu____80512  ->
                                     let uu____80513 =
                                       FStar_Syntax_Print.term_to_string typ
                                        in
                                     FStar_Util.print1 "unquote: typ = %s\n"
                                       uu____80513)
                                  (fun uu____80518  ->
                                     let uu____80519 =
                                       proc_guard "unquote" env guard  in
                                     bind uu____80519
                                       (fun uu____80524  -> ret tm1))))))
         in
      FStar_All.pipe_left (wrap_err "unquote") uu____80450
  
let (uvar_env :
  env ->
    FStar_Reflection_Data.typ FStar_Pervasives_Native.option ->
      FStar_Syntax_Syntax.term tac)
  =
  fun env  ->
    fun ty  ->
      let uu____80549 =
        match ty with
        | FStar_Pervasives_Native.Some ty1 -> ret ty1
        | FStar_Pervasives_Native.None  ->
            let uu____80555 =
              let uu____80562 =
                let uu____80563 = FStar_Syntax_Util.type_u ()  in
                FStar_All.pipe_left FStar_Pervasives_Native.fst uu____80563
                 in
              new_uvar "uvar_env.2" env uu____80562  in
            bind uu____80555
              (fun uu____80580  ->
                 match uu____80580 with | (typ,uvar_typ) -> ret typ)
         in
      bind uu____80549
        (fun typ  ->
           let uu____80592 = new_uvar "uvar_env" env typ  in
           bind uu____80592
             (fun uu____80607  ->
                match uu____80607 with | (t,uvar_t) -> ret t))
  
let (unshelve : FStar_Syntax_Syntax.term -> unit tac) =
  fun t  ->
    let uu____80626 =
      bind get
        (fun ps  ->
           let env = ps.FStar_Tactics_Types.main_context  in
           let opts =
             match ps.FStar_Tactics_Types.goals with
             | g::uu____80645 -> g.FStar_Tactics_Types.opts
             | uu____80648 -> FStar_Options.peek ()  in
           let uu____80651 = FStar_Syntax_Util.head_and_args t  in
           match uu____80651 with
           | ({
                FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                  (ctx_uvar,uu____80671);
                FStar_Syntax_Syntax.pos = uu____80672;
                FStar_Syntax_Syntax.vars = uu____80673;_},uu____80674)
               ->
               let env1 =
                 let uu___2286_80716 = env  in
                 {
                   FStar_TypeChecker_Env.solver =
                     (uu___2286_80716.FStar_TypeChecker_Env.solver);
                   FStar_TypeChecker_Env.range =
                     (uu___2286_80716.FStar_TypeChecker_Env.range);
                   FStar_TypeChecker_Env.curmodule =
                     (uu___2286_80716.FStar_TypeChecker_Env.curmodule);
                   FStar_TypeChecker_Env.gamma =
                     (ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_gamma);
                   FStar_TypeChecker_Env.gamma_sig =
                     (uu___2286_80716.FStar_TypeChecker_Env.gamma_sig);
                   FStar_TypeChecker_Env.gamma_cache =
                     (uu___2286_80716.FStar_TypeChecker_Env.gamma_cache);
                   FStar_TypeChecker_Env.modules =
                     (uu___2286_80716.FStar_TypeChecker_Env.modules);
                   FStar_TypeChecker_Env.expected_typ =
                     (uu___2286_80716.FStar_TypeChecker_Env.expected_typ);
                   FStar_TypeChecker_Env.sigtab =
                     (uu___2286_80716.FStar_TypeChecker_Env.sigtab);
                   FStar_TypeChecker_Env.attrtab =
                     (uu___2286_80716.FStar_TypeChecker_Env.attrtab);
                   FStar_TypeChecker_Env.is_pattern =
                     (uu___2286_80716.FStar_TypeChecker_Env.is_pattern);
                   FStar_TypeChecker_Env.instantiate_imp =
                     (uu___2286_80716.FStar_TypeChecker_Env.instantiate_imp);
                   FStar_TypeChecker_Env.effects =
                     (uu___2286_80716.FStar_TypeChecker_Env.effects);
                   FStar_TypeChecker_Env.generalize =
                     (uu___2286_80716.FStar_TypeChecker_Env.generalize);
                   FStar_TypeChecker_Env.letrecs =
                     (uu___2286_80716.FStar_TypeChecker_Env.letrecs);
                   FStar_TypeChecker_Env.top_level =
                     (uu___2286_80716.FStar_TypeChecker_Env.top_level);
                   FStar_TypeChecker_Env.check_uvars =
                     (uu___2286_80716.FStar_TypeChecker_Env.check_uvars);
                   FStar_TypeChecker_Env.use_eq =
                     (uu___2286_80716.FStar_TypeChecker_Env.use_eq);
                   FStar_TypeChecker_Env.is_iface =
                     (uu___2286_80716.FStar_TypeChecker_Env.is_iface);
                   FStar_TypeChecker_Env.admit =
                     (uu___2286_80716.FStar_TypeChecker_Env.admit);
                   FStar_TypeChecker_Env.lax =
                     (uu___2286_80716.FStar_TypeChecker_Env.lax);
                   FStar_TypeChecker_Env.lax_universes =
                     (uu___2286_80716.FStar_TypeChecker_Env.lax_universes);
                   FStar_TypeChecker_Env.phase1 =
                     (uu___2286_80716.FStar_TypeChecker_Env.phase1);
                   FStar_TypeChecker_Env.failhard =
                     (uu___2286_80716.FStar_TypeChecker_Env.failhard);
                   FStar_TypeChecker_Env.nosynth =
                     (uu___2286_80716.FStar_TypeChecker_Env.nosynth);
                   FStar_TypeChecker_Env.uvar_subtyping =
                     (uu___2286_80716.FStar_TypeChecker_Env.uvar_subtyping);
                   FStar_TypeChecker_Env.tc_term =
                     (uu___2286_80716.FStar_TypeChecker_Env.tc_term);
                   FStar_TypeChecker_Env.type_of =
                     (uu___2286_80716.FStar_TypeChecker_Env.type_of);
                   FStar_TypeChecker_Env.universe_of =
                     (uu___2286_80716.FStar_TypeChecker_Env.universe_of);
                   FStar_TypeChecker_Env.check_type_of =
                     (uu___2286_80716.FStar_TypeChecker_Env.check_type_of);
                   FStar_TypeChecker_Env.use_bv_sorts =
                     (uu___2286_80716.FStar_TypeChecker_Env.use_bv_sorts);
                   FStar_TypeChecker_Env.qtbl_name_and_index =
                     (uu___2286_80716.FStar_TypeChecker_Env.qtbl_name_and_index);
                   FStar_TypeChecker_Env.normalized_eff_names =
                     (uu___2286_80716.FStar_TypeChecker_Env.normalized_eff_names);
                   FStar_TypeChecker_Env.fv_delta_depths =
                     (uu___2286_80716.FStar_TypeChecker_Env.fv_delta_depths);
                   FStar_TypeChecker_Env.proof_ns =
                     (uu___2286_80716.FStar_TypeChecker_Env.proof_ns);
                   FStar_TypeChecker_Env.synth_hook =
                     (uu___2286_80716.FStar_TypeChecker_Env.synth_hook);
                   FStar_TypeChecker_Env.splice =
                     (uu___2286_80716.FStar_TypeChecker_Env.splice);
                   FStar_TypeChecker_Env.postprocess =
                     (uu___2286_80716.FStar_TypeChecker_Env.postprocess);
                   FStar_TypeChecker_Env.is_native_tactic =
                     (uu___2286_80716.FStar_TypeChecker_Env.is_native_tactic);
                   FStar_TypeChecker_Env.identifier_info =
                     (uu___2286_80716.FStar_TypeChecker_Env.identifier_info);
                   FStar_TypeChecker_Env.tc_hooks =
                     (uu___2286_80716.FStar_TypeChecker_Env.tc_hooks);
                   FStar_TypeChecker_Env.dsenv =
                     (uu___2286_80716.FStar_TypeChecker_Env.dsenv);
                   FStar_TypeChecker_Env.nbe =
                     (uu___2286_80716.FStar_TypeChecker_Env.nbe)
                 }  in
               let g =
                 FStar_Tactics_Types.mk_goal env1 ctx_uvar opts false ""  in
               let uu____80720 =
                 let uu____80723 = bnorm_goal g  in [uu____80723]  in
               add_goals uu____80720
           | uu____80724 -> fail "not a uvar")
       in
    FStar_All.pipe_left (wrap_err "unshelve") uu____80626
  
let (tac_and : Prims.bool tac -> Prims.bool tac -> Prims.bool tac) =
  fun t1  ->
    fun t2  ->
      let comp =
        bind t1
          (fun b  ->
             let uu____80786 = if b then t2 else ret false  in
             bind uu____80786 (fun b'  -> if b' then ret b' else fail ""))
         in
      let uu____80812 = trytac comp  in
      bind uu____80812
        (fun uu___613_80824  ->
           match uu___613_80824 with
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
        let uu____80866 =
          bind get
            (fun ps  ->
               let uu____80874 = __tc e t1  in
               bind uu____80874
                 (fun uu____80895  ->
                    match uu____80895 with
                    | (t11,ty1,g1) ->
                        let uu____80908 = __tc e t2  in
                        bind uu____80908
                          (fun uu____80929  ->
                             match uu____80929 with
                             | (t21,ty2,g2) ->
                                 let uu____80942 =
                                   proc_guard "unify_env g1" e g1  in
                                 bind uu____80942
                                   (fun uu____80949  ->
                                      let uu____80950 =
                                        proc_guard "unify_env g2" e g2  in
                                      bind uu____80950
                                        (fun uu____80958  ->
                                           let uu____80959 =
                                             do_unify e ty1 ty2  in
                                           let uu____80963 =
                                             do_unify e t11 t21  in
                                           tac_and uu____80959 uu____80963)))))
           in
        FStar_All.pipe_left (wrap_err "unify_env") uu____80866
  
let (launch_process :
  Prims.string -> Prims.string Prims.list -> Prims.string -> Prims.string tac)
  =
  fun prog  ->
    fun args  ->
      fun input  ->
        bind idtac
          (fun uu____81011  ->
             let uu____81012 = FStar_Options.unsafe_tactic_exec ()  in
             if uu____81012
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
        (fun uu____81046  ->
           let uu____81047 =
             FStar_Syntax_Syntax.gen_bv nm FStar_Pervasives_Native.None t  in
           ret uu____81047)
  
let (change : FStar_Reflection_Data.typ -> unit tac) =
  fun ty  ->
    let uu____81058 =
      mlog
        (fun uu____81063  ->
           let uu____81064 = FStar_Syntax_Print.term_to_string ty  in
           FStar_Util.print1 "change: ty = %s\n" uu____81064)
        (fun uu____81069  ->
           let uu____81070 = cur_goal ()  in
           bind uu____81070
             (fun g  ->
                let uu____81076 =
                  let uu____81085 = FStar_Tactics_Types.goal_env g  in
                  __tc uu____81085 ty  in
                bind uu____81076
                  (fun uu____81097  ->
                     match uu____81097 with
                     | (ty1,uu____81107,guard) ->
                         let uu____81109 =
                           let uu____81112 = FStar_Tactics_Types.goal_env g
                              in
                           proc_guard "change" uu____81112 guard  in
                         bind uu____81109
                           (fun uu____81116  ->
                              let uu____81117 =
                                let uu____81121 =
                                  FStar_Tactics_Types.goal_env g  in
                                let uu____81122 =
                                  FStar_Tactics_Types.goal_type g  in
                                do_unify uu____81121 uu____81122 ty1  in
                              bind uu____81117
                                (fun bb  ->
                                   if bb
                                   then
                                     let uu____81131 =
                                       FStar_Tactics_Types.goal_with_type g
                                         ty1
                                        in
                                     replace_cur uu____81131
                                   else
                                     (let steps =
                                        [FStar_TypeChecker_Env.AllowUnboundUniverses;
                                        FStar_TypeChecker_Env.UnfoldUntil
                                          FStar_Syntax_Syntax.delta_constant;
                                        FStar_TypeChecker_Env.Primops]  in
                                      let ng =
                                        let uu____81138 =
                                          FStar_Tactics_Types.goal_env g  in
                                        let uu____81139 =
                                          FStar_Tactics_Types.goal_type g  in
                                        normalize steps uu____81138
                                          uu____81139
                                         in
                                      let nty =
                                        let uu____81141 =
                                          FStar_Tactics_Types.goal_env g  in
                                        normalize steps uu____81141 ty1  in
                                      let uu____81142 =
                                        let uu____81146 =
                                          FStar_Tactics_Types.goal_env g  in
                                        do_unify uu____81146 ng nty  in
                                      bind uu____81142
                                        (fun b  ->
                                           if b
                                           then
                                             let uu____81155 =
                                               FStar_Tactics_Types.goal_with_type
                                                 g ty1
                                                in
                                             replace_cur uu____81155
                                           else fail "not convertible")))))))
       in
    FStar_All.pipe_left (wrap_err "change") uu____81058
  
let failwhen : 'a . Prims.bool -> Prims.string -> (unit -> 'a tac) -> 'a tac
  = fun b  -> fun msg  -> fun k  -> if b then fail msg else k () 
let (t_destruct :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.fv * FStar_BigInt.t) Prims.list tac)
  =
  fun s_tm  ->
    let uu____81229 =
      let uu____81238 = cur_goal ()  in
      bind uu____81238
        (fun g  ->
           let uu____81250 =
             let uu____81259 = FStar_Tactics_Types.goal_env g  in
             __tc uu____81259 s_tm  in
           bind uu____81250
             (fun uu____81277  ->
                match uu____81277 with
                | (s_tm1,s_ty,guard) ->
                    let uu____81295 =
                      let uu____81298 = FStar_Tactics_Types.goal_env g  in
                      proc_guard "destruct" uu____81298 guard  in
                    bind uu____81295
                      (fun uu____81311  ->
                         let uu____81312 =
                           FStar_Syntax_Util.head_and_args' s_ty  in
                         match uu____81312 with
                         | (h,args) ->
                             let uu____81357 =
                               let uu____81364 =
                                 let uu____81365 =
                                   FStar_Syntax_Subst.compress h  in
                                 uu____81365.FStar_Syntax_Syntax.n  in
                               match uu____81364 with
                               | FStar_Syntax_Syntax.Tm_fvar fv ->
                                   ret (fv, [])
                               | FStar_Syntax_Syntax.Tm_uinst
                                   ({
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.Tm_fvar fv;
                                      FStar_Syntax_Syntax.pos = uu____81380;
                                      FStar_Syntax_Syntax.vars = uu____81381;_},us)
                                   -> ret (fv, us)
                               | uu____81391 -> fail "type is not an fv"  in
                             bind uu____81357
                               (fun uu____81412  ->
                                  match uu____81412 with
                                  | (fv,a_us) ->
                                      let t_lid =
                                        FStar_Syntax_Syntax.lid_of_fv fv  in
                                      let uu____81428 =
                                        let uu____81431 =
                                          FStar_Tactics_Types.goal_env g  in
                                        FStar_TypeChecker_Env.lookup_sigelt
                                          uu____81431 t_lid
                                         in
                                      (match uu____81428 with
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
                                                  (fun uu____81482  ->
                                                     let uu____81483 =
                                                       FStar_Syntax_Subst.open_term
                                                         t_ps t_ty
                                                        in
                                                     match uu____81483 with
                                                     | (t_ps1,t_ty1) ->
                                                         let uu____81498 =
                                                           mapM
                                                             (fun c_lid  ->
                                                                let uu____81526
                                                                  =
                                                                  let uu____81529
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    g  in
                                                                  FStar_TypeChecker_Env.lookup_sigelt
                                                                    uu____81529
                                                                    c_lid
                                                                   in
                                                                match uu____81526
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
                                                                    uu____81603
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
                                                                    let uu____81608
                                                                    =
                                                                    FStar_TypeChecker_Env.inst_tscheme
                                                                    (c_us,
                                                                    c_ty1)
                                                                     in
                                                                    match uu____81608
                                                                    with
                                                                    | 
                                                                    (c_us1,c_ty2)
                                                                    ->
                                                                    let uu____81631
                                                                    =
                                                                    FStar_Syntax_Util.arrow_formals_comp
                                                                    c_ty2  in
                                                                    (match uu____81631
                                                                    with
                                                                    | 
                                                                    (bs,comp)
                                                                    ->
                                                                    let uu____81674
                                                                    =
                                                                    FStar_List.splitAt
                                                                    nparam bs
                                                                     in
                                                                    (match uu____81674
                                                                    with
                                                                    | 
                                                                    (d_ps,bs1)
                                                                    ->
                                                                    let uu____81747
                                                                    =
                                                                    let uu____81749
                                                                    =
                                                                    FStar_Syntax_Util.is_total_comp
                                                                    comp  in
                                                                    Prims.op_Negation
                                                                    uu____81749
                                                                     in
                                                                    failwhen
                                                                    uu____81747
                                                                    "not total?"
                                                                    (fun
                                                                    uu____81768
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
                                                                    uu___614_81785
                                                                    =
                                                                    match uu___614_81785
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    (FStar_Syntax_Syntax.Implicit
                                                                    uu____81789)
                                                                    -> true
                                                                    | 
                                                                    uu____81792
                                                                    -> false
                                                                     in
                                                                    let uu____81796
                                                                    =
                                                                    FStar_List.splitAt
                                                                    nparam
                                                                    args  in
                                                                    match uu____81796
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
                                                                    uu____81930
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
                                                                    uu____81992
                                                                     ->
                                                                    match uu____81992
                                                                    with
                                                                    | 
                                                                    ((bv,uu____82012),
                                                                    (t,uu____82014))
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
                                                                    uu____82084
                                                                     ->
                                                                    match uu____82084
                                                                    with
                                                                    | 
                                                                    ((bv,uu____82111),
                                                                    (t,uu____82113))
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
                                                                    uu____82172
                                                                     ->
                                                                    match uu____82172
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
                                                                    let uu____82227
                                                                    =
                                                                    FStar_TypeChecker_TcTerm.tc_pat
                                                                    (let uu___2450_82244
                                                                    = env  in
                                                                    {
                                                                    FStar_TypeChecker_Env.solver
                                                                    =
                                                                    (uu___2450_82244.FStar_TypeChecker_Env.solver);
                                                                    FStar_TypeChecker_Env.range
                                                                    =
                                                                    (uu___2450_82244.FStar_TypeChecker_Env.range);
                                                                    FStar_TypeChecker_Env.curmodule
                                                                    =
                                                                    (uu___2450_82244.FStar_TypeChecker_Env.curmodule);
                                                                    FStar_TypeChecker_Env.gamma
                                                                    =
                                                                    (uu___2450_82244.FStar_TypeChecker_Env.gamma);
                                                                    FStar_TypeChecker_Env.gamma_sig
                                                                    =
                                                                    (uu___2450_82244.FStar_TypeChecker_Env.gamma_sig);
                                                                    FStar_TypeChecker_Env.gamma_cache
                                                                    =
                                                                    (uu___2450_82244.FStar_TypeChecker_Env.gamma_cache);
                                                                    FStar_TypeChecker_Env.modules
                                                                    =
                                                                    (uu___2450_82244.FStar_TypeChecker_Env.modules);
                                                                    FStar_TypeChecker_Env.expected_typ
                                                                    =
                                                                    (uu___2450_82244.FStar_TypeChecker_Env.expected_typ);
                                                                    FStar_TypeChecker_Env.sigtab
                                                                    =
                                                                    (uu___2450_82244.FStar_TypeChecker_Env.sigtab);
                                                                    FStar_TypeChecker_Env.attrtab
                                                                    =
                                                                    (uu___2450_82244.FStar_TypeChecker_Env.attrtab);
                                                                    FStar_TypeChecker_Env.is_pattern
                                                                    =
                                                                    (uu___2450_82244.FStar_TypeChecker_Env.is_pattern);
                                                                    FStar_TypeChecker_Env.instantiate_imp
                                                                    =
                                                                    (uu___2450_82244.FStar_TypeChecker_Env.instantiate_imp);
                                                                    FStar_TypeChecker_Env.effects
                                                                    =
                                                                    (uu___2450_82244.FStar_TypeChecker_Env.effects);
                                                                    FStar_TypeChecker_Env.generalize
                                                                    =
                                                                    (uu___2450_82244.FStar_TypeChecker_Env.generalize);
                                                                    FStar_TypeChecker_Env.letrecs
                                                                    =
                                                                    (uu___2450_82244.FStar_TypeChecker_Env.letrecs);
                                                                    FStar_TypeChecker_Env.top_level
                                                                    =
                                                                    (uu___2450_82244.FStar_TypeChecker_Env.top_level);
                                                                    FStar_TypeChecker_Env.check_uvars
                                                                    =
                                                                    (uu___2450_82244.FStar_TypeChecker_Env.check_uvars);
                                                                    FStar_TypeChecker_Env.use_eq
                                                                    =
                                                                    (uu___2450_82244.FStar_TypeChecker_Env.use_eq);
                                                                    FStar_TypeChecker_Env.is_iface
                                                                    =
                                                                    (uu___2450_82244.FStar_TypeChecker_Env.is_iface);
                                                                    FStar_TypeChecker_Env.admit
                                                                    =
                                                                    (uu___2450_82244.FStar_TypeChecker_Env.admit);
                                                                    FStar_TypeChecker_Env.lax
                                                                    = true;
                                                                    FStar_TypeChecker_Env.lax_universes
                                                                    =
                                                                    (uu___2450_82244.FStar_TypeChecker_Env.lax_universes);
                                                                    FStar_TypeChecker_Env.phase1
                                                                    =
                                                                    (uu___2450_82244.FStar_TypeChecker_Env.phase1);
                                                                    FStar_TypeChecker_Env.failhard
                                                                    =
                                                                    (uu___2450_82244.FStar_TypeChecker_Env.failhard);
                                                                    FStar_TypeChecker_Env.nosynth
                                                                    =
                                                                    (uu___2450_82244.FStar_TypeChecker_Env.nosynth);
                                                                    FStar_TypeChecker_Env.uvar_subtyping
                                                                    =
                                                                    (uu___2450_82244.FStar_TypeChecker_Env.uvar_subtyping);
                                                                    FStar_TypeChecker_Env.tc_term
                                                                    =
                                                                    (uu___2450_82244.FStar_TypeChecker_Env.tc_term);
                                                                    FStar_TypeChecker_Env.type_of
                                                                    =
                                                                    (uu___2450_82244.FStar_TypeChecker_Env.type_of);
                                                                    FStar_TypeChecker_Env.universe_of
                                                                    =
                                                                    (uu___2450_82244.FStar_TypeChecker_Env.universe_of);
                                                                    FStar_TypeChecker_Env.check_type_of
                                                                    =
                                                                    (uu___2450_82244.FStar_TypeChecker_Env.check_type_of);
                                                                    FStar_TypeChecker_Env.use_bv_sorts
                                                                    =
                                                                    (uu___2450_82244.FStar_TypeChecker_Env.use_bv_sorts);
                                                                    FStar_TypeChecker_Env.qtbl_name_and_index
                                                                    =
                                                                    (uu___2450_82244.FStar_TypeChecker_Env.qtbl_name_and_index);
                                                                    FStar_TypeChecker_Env.normalized_eff_names
                                                                    =
                                                                    (uu___2450_82244.FStar_TypeChecker_Env.normalized_eff_names);
                                                                    FStar_TypeChecker_Env.fv_delta_depths
                                                                    =
                                                                    (uu___2450_82244.FStar_TypeChecker_Env.fv_delta_depths);
                                                                    FStar_TypeChecker_Env.proof_ns
                                                                    =
                                                                    (uu___2450_82244.FStar_TypeChecker_Env.proof_ns);
                                                                    FStar_TypeChecker_Env.synth_hook
                                                                    =
                                                                    (uu___2450_82244.FStar_TypeChecker_Env.synth_hook);
                                                                    FStar_TypeChecker_Env.splice
                                                                    =
                                                                    (uu___2450_82244.FStar_TypeChecker_Env.splice);
                                                                    FStar_TypeChecker_Env.postprocess
                                                                    =
                                                                    (uu___2450_82244.FStar_TypeChecker_Env.postprocess);
                                                                    FStar_TypeChecker_Env.is_native_tactic
                                                                    =
                                                                    (uu___2450_82244.FStar_TypeChecker_Env.is_native_tactic);
                                                                    FStar_TypeChecker_Env.identifier_info
                                                                    =
                                                                    (uu___2450_82244.FStar_TypeChecker_Env.identifier_info);
                                                                    FStar_TypeChecker_Env.tc_hooks
                                                                    =
                                                                    (uu___2450_82244.FStar_TypeChecker_Env.tc_hooks);
                                                                    FStar_TypeChecker_Env.dsenv
                                                                    =
                                                                    (uu___2450_82244.FStar_TypeChecker_Env.dsenv);
                                                                    FStar_TypeChecker_Env.nbe
                                                                    =
                                                                    (uu___2450_82244.FStar_TypeChecker_Env.nbe)
                                                                    }) s_ty
                                                                    pat  in
                                                                    match uu____82227
                                                                    with
                                                                    | 
                                                                    (uu____82258,uu____82259,uu____82260,pat_t,uu____82262,_guard_pat)
                                                                    ->
                                                                    let eq_b
                                                                    =
                                                                    let uu____82269
                                                                    =
                                                                    let uu____82270
                                                                    =
                                                                    FStar_Syntax_Util.mk_eq2
                                                                    equ s_ty
                                                                    s_tm1
                                                                    pat_t  in
                                                                    FStar_Syntax_Util.mk_squash
                                                                    equ
                                                                    uu____82270
                                                                     in
                                                                    FStar_Syntax_Syntax.gen_bv
                                                                    "breq"
                                                                    FStar_Pervasives_Native.None
                                                                    uu____82269
                                                                     in
                                                                    let cod1
                                                                    =
                                                                    let uu____82275
                                                                    =
                                                                    let uu____82284
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_binder
                                                                    eq_b  in
                                                                    [uu____82284]
                                                                     in
                                                                    let uu____82303
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Total
                                                                    cod  in
                                                                    FStar_Syntax_Util.arrow
                                                                    uu____82275
                                                                    uu____82303
                                                                     in
                                                                    let nty =
                                                                    let uu____82309
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Total
                                                                    cod1  in
                                                                    FStar_Syntax_Util.arrow
                                                                    bs2
                                                                    uu____82309
                                                                     in
                                                                    let uu____82312
                                                                    =
                                                                    new_uvar
                                                                    "destruct branch"
                                                                    env nty
                                                                     in
                                                                    bind
                                                                    uu____82312
                                                                    (fun
                                                                    uu____82342
                                                                     ->
                                                                    match uu____82342
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
                                                                    let uu____82369
                                                                    =
                                                                    let uu____82380
                                                                    =
                                                                    FStar_Syntax_Syntax.as_arg
                                                                    FStar_Syntax_Util.exp_unit
                                                                     in
                                                                    [uu____82380]
                                                                     in
                                                                    FStar_Syntax_Util.mk_app
                                                                    brt
                                                                    uu____82369
                                                                     in
                                                                    let br =
                                                                    FStar_Syntax_Subst.close_branch
                                                                    (pat,
                                                                    FStar_Pervasives_Native.None,
                                                                    brt1)  in
                                                                    let uu____82416
                                                                    =
                                                                    let uu____82427
                                                                    =
                                                                    let uu____82432
                                                                    =
                                                                    FStar_BigInt.of_int_fs
                                                                    (FStar_List.length
                                                                    bs2)  in
                                                                    (fv1,
                                                                    uu____82432)
                                                                     in
                                                                    (g', br,
                                                                    uu____82427)
                                                                     in
                                                                    ret
                                                                    uu____82416))))))
                                                                    | 
                                                                    uu____82453
                                                                    ->
                                                                    fail
                                                                    "impossible: not a ctor"))
                                                             c_lids
                                                            in
                                                         bind uu____81498
                                                           (fun goal_brs  ->
                                                              let uu____82503
                                                                =
                                                                FStar_List.unzip3
                                                                  goal_brs
                                                                 in
                                                              match uu____82503
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
                                                                  let uu____82576
                                                                    =
                                                                    solve' g
                                                                    w  in
                                                                  bind
                                                                    uu____82576
                                                                    (
                                                                    fun
                                                                    uu____82587
                                                                     ->
                                                                    let uu____82588
                                                                    =
                                                                    add_goals
                                                                    goals  in
                                                                    bind
                                                                    uu____82588
                                                                    (fun
                                                                    uu____82598
                                                                     ->
                                                                    ret infos))))
                                            | uu____82605 ->
                                                fail "not an inductive type"))))))
       in
    FStar_All.pipe_left (wrap_err "destruct") uu____81229
  
let rec last : 'a . 'a Prims.list -> 'a =
  fun l  ->
    match l with
    | [] -> failwith "last: empty list"
    | x::[] -> x
    | uu____82654::xs -> last xs
  
let rec init : 'a . 'a Prims.list -> 'a Prims.list =
  fun l  ->
    match l with
    | [] -> failwith "init: empty list"
    | x::[] -> []
    | x::xs -> let uu____82684 = init xs  in x :: uu____82684
  
let rec (inspect :
  FStar_Syntax_Syntax.term -> FStar_Reflection_Data.term_view tac) =
  fun t  ->
    let uu____82697 =
      let t1 = FStar_Syntax_Util.unascribe t  in
      let t2 = FStar_Syntax_Util.un_uinst t1  in
      let t3 = FStar_Syntax_Util.unlazy_emb t2  in
      match t3.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_meta (t4,uu____82706) -> inspect t4
      | FStar_Syntax_Syntax.Tm_name bv ->
          FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_Var bv)
      | FStar_Syntax_Syntax.Tm_bvar bv ->
          FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_BVar bv)
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_FVar fv)
      | FStar_Syntax_Syntax.Tm_app (hd1,[]) ->
          failwith "empty arguments on Tm_app"
      | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
          let uu____82772 = last args  in
          (match uu____82772 with
           | (a,q) ->
               let q' = FStar_Reflection_Basic.inspect_aqual q  in
               let uu____82802 =
                 let uu____82803 =
                   let uu____82808 =
                     let uu____82809 =
                       let uu____82814 = init args  in
                       FStar_Syntax_Syntax.mk_Tm_app hd1 uu____82814  in
                     uu____82809 FStar_Pervasives_Native.None
                       t3.FStar_Syntax_Syntax.pos
                      in
                   (uu____82808, (a, q'))  in
                 FStar_Reflection_Data.Tv_App uu____82803  in
               FStar_All.pipe_left ret uu____82802)
      | FStar_Syntax_Syntax.Tm_abs ([],uu____82827,uu____82828) ->
          failwith "empty arguments on Tm_abs"
      | FStar_Syntax_Syntax.Tm_abs (bs,t4,k) ->
          let uu____82881 = FStar_Syntax_Subst.open_term bs t4  in
          (match uu____82881 with
           | (bs1,t5) ->
               (match bs1 with
                | [] -> failwith "impossible"
                | b::bs2 ->
                    let uu____82923 =
                      let uu____82924 =
                        let uu____82929 = FStar_Syntax_Util.abs bs2 t5 k  in
                        (b, uu____82929)  in
                      FStar_Reflection_Data.Tv_Abs uu____82924  in
                    FStar_All.pipe_left ret uu____82923))
      | FStar_Syntax_Syntax.Tm_type uu____82932 ->
          FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_Type ())
      | FStar_Syntax_Syntax.Tm_arrow ([],k) ->
          failwith "empty binders on arrow"
      | FStar_Syntax_Syntax.Tm_arrow uu____82957 ->
          let uu____82972 = FStar_Syntax_Util.arrow_one t3  in
          (match uu____82972 with
           | FStar_Pervasives_Native.Some (b,c) ->
               FStar_All.pipe_left ret
                 (FStar_Reflection_Data.Tv_Arrow (b, c))
           | FStar_Pervasives_Native.None  -> failwith "impossible")
      | FStar_Syntax_Syntax.Tm_refine (bv,t4) ->
          let b = FStar_Syntax_Syntax.mk_binder bv  in
          let uu____83003 = FStar_Syntax_Subst.open_term [b] t4  in
          (match uu____83003 with
           | (b',t5) ->
               let b1 =
                 match b' with
                 | b'1::[] -> b'1
                 | uu____83056 -> failwith "impossible"  in
               FStar_All.pipe_left ret
                 (FStar_Reflection_Data.Tv_Refine
                    ((FStar_Pervasives_Native.fst b1), t5)))
      | FStar_Syntax_Syntax.Tm_constant c ->
          let uu____83069 =
            let uu____83070 = FStar_Reflection_Basic.inspect_const c  in
            FStar_Reflection_Data.Tv_Const uu____83070  in
          FStar_All.pipe_left ret uu____83069
      | FStar_Syntax_Syntax.Tm_uvar (ctx_u,s) ->
          let uu____83091 =
            let uu____83092 =
              let uu____83097 =
                let uu____83098 =
                  FStar_Syntax_Unionfind.uvar_id
                    ctx_u.FStar_Syntax_Syntax.ctx_uvar_head
                   in
                FStar_BigInt.of_int_fs uu____83098  in
              (uu____83097, (ctx_u, s))  in
            FStar_Reflection_Data.Tv_Uvar uu____83092  in
          FStar_All.pipe_left ret uu____83091
      | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),t21) ->
          if lb.FStar_Syntax_Syntax.lbunivs <> []
          then FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown
          else
            (match lb.FStar_Syntax_Syntax.lbname with
             | FStar_Util.Inr uu____83138 ->
                 FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown
             | FStar_Util.Inl bv ->
                 let b = FStar_Syntax_Syntax.mk_binder bv  in
                 let uu____83143 = FStar_Syntax_Subst.open_term [b] t21  in
                 (match uu____83143 with
                  | (bs,t22) ->
                      let b1 =
                        match bs with
                        | b1::[] -> b1
                        | uu____83196 ->
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
             | FStar_Util.Inr uu____83238 ->
                 FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown
             | FStar_Util.Inl bv ->
                 let uu____83242 = FStar_Syntax_Subst.open_let_rec [lb] t21
                    in
                 (match uu____83242 with
                  | (lbs,t22) ->
                      (match lbs with
                       | lb1::[] ->
                           (match lb1.FStar_Syntax_Syntax.lbname with
                            | FStar_Util.Inr uu____83262 ->
                                ret FStar_Reflection_Data.Tv_Unknown
                            | FStar_Util.Inl bv1 ->
                                FStar_All.pipe_left ret
                                  (FStar_Reflection_Data.Tv_Let
                                     (true, bv1,
                                       (lb1.FStar_Syntax_Syntax.lbdef), t22)))
                       | uu____83268 ->
                           failwith
                             "impossible: open_term returned different amount of binders")))
      | FStar_Syntax_Syntax.Tm_match (t4,brs) ->
          let rec inspect_pat p =
            match p.FStar_Syntax_Syntax.v with
            | FStar_Syntax_Syntax.Pat_constant c ->
                let uu____83323 = FStar_Reflection_Basic.inspect_const c  in
                FStar_Reflection_Data.Pat_Constant uu____83323
            | FStar_Syntax_Syntax.Pat_cons (fv,ps) ->
                let uu____83344 =
                  let uu____83351 =
                    FStar_List.map
                      (fun uu____83364  ->
                         match uu____83364 with
                         | (p1,uu____83373) -> inspect_pat p1) ps
                     in
                  (fv, uu____83351)  in
                FStar_Reflection_Data.Pat_Cons uu____83344
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
              (fun uu___615_83469  ->
                 match uu___615_83469 with
                 | (pat,uu____83491,t5) ->
                     let uu____83509 = inspect_pat pat  in (uu____83509, t5))
              brs1
             in
          FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_Match (t4, brs2))
      | FStar_Syntax_Syntax.Tm_unknown  ->
          FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown
      | uu____83518 ->
          ((let uu____83520 =
              let uu____83526 =
                let uu____83528 = FStar_Syntax_Print.tag_of_term t3  in
                let uu____83530 = FStar_Syntax_Print.term_to_string t3  in
                FStar_Util.format2
                  "inspect: outside of expected syntax (%s, %s)\n"
                  uu____83528 uu____83530
                 in
              (FStar_Errors.Warning_CantInspect, uu____83526)  in
            FStar_Errors.log_issue t3.FStar_Syntax_Syntax.pos uu____83520);
           FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown)
       in
    wrap_err "inspect" uu____82697
  
let (pack : FStar_Reflection_Data.term_view -> FStar_Syntax_Syntax.term tac)
  =
  fun tv  ->
    match tv with
    | FStar_Reflection_Data.Tv_Var bv ->
        let uu____83548 = FStar_Syntax_Syntax.bv_to_name bv  in
        FStar_All.pipe_left ret uu____83548
    | FStar_Reflection_Data.Tv_BVar bv ->
        let uu____83552 = FStar_Syntax_Syntax.bv_to_tm bv  in
        FStar_All.pipe_left ret uu____83552
    | FStar_Reflection_Data.Tv_FVar fv ->
        let uu____83556 = FStar_Syntax_Syntax.fv_to_tm fv  in
        FStar_All.pipe_left ret uu____83556
    | FStar_Reflection_Data.Tv_App (l,(r,q)) ->
        let q' = FStar_Reflection_Basic.pack_aqual q  in
        let uu____83563 = FStar_Syntax_Util.mk_app l [(r, q')]  in
        FStar_All.pipe_left ret uu____83563
    | FStar_Reflection_Data.Tv_Abs (b,t) ->
        let uu____83588 =
          FStar_Syntax_Util.abs [b] t FStar_Pervasives_Native.None  in
        FStar_All.pipe_left ret uu____83588
    | FStar_Reflection_Data.Tv_Arrow (b,c) ->
        let uu____83605 = FStar_Syntax_Util.arrow [b] c  in
        FStar_All.pipe_left ret uu____83605
    | FStar_Reflection_Data.Tv_Type () ->
        FStar_All.pipe_left ret FStar_Syntax_Util.ktype
    | FStar_Reflection_Data.Tv_Refine (bv,t) ->
        let uu____83624 = FStar_Syntax_Util.refine bv t  in
        FStar_All.pipe_left ret uu____83624
    | FStar_Reflection_Data.Tv_Const c ->
        let uu____83628 =
          let uu____83629 =
            let uu____83636 =
              let uu____83637 = FStar_Reflection_Basic.pack_const c  in
              FStar_Syntax_Syntax.Tm_constant uu____83637  in
            FStar_Syntax_Syntax.mk uu____83636  in
          uu____83629 FStar_Pervasives_Native.None FStar_Range.dummyRange  in
        FStar_All.pipe_left ret uu____83628
    | FStar_Reflection_Data.Tv_Uvar (_u,ctx_u_s) ->
        let uu____83645 =
          FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_uvar ctx_u_s)
            FStar_Pervasives_Native.None FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____83645
    | FStar_Reflection_Data.Tv_Let (false ,bv,t1,t2) ->
        let lb =
          FStar_Syntax_Util.mk_letbinding (FStar_Util.Inl bv) []
            bv.FStar_Syntax_Syntax.sort FStar_Parser_Const.effect_Tot_lid t1
            [] FStar_Range.dummyRange
           in
        let uu____83656 =
          let uu____83657 =
            let uu____83664 =
              let uu____83665 =
                let uu____83679 =
                  let uu____83682 =
                    let uu____83683 = FStar_Syntax_Syntax.mk_binder bv  in
                    [uu____83683]  in
                  FStar_Syntax_Subst.close uu____83682 t2  in
                ((false, [lb]), uu____83679)  in
              FStar_Syntax_Syntax.Tm_let uu____83665  in
            FStar_Syntax_Syntax.mk uu____83664  in
          uu____83657 FStar_Pervasives_Native.None FStar_Range.dummyRange  in
        FStar_All.pipe_left ret uu____83656
    | FStar_Reflection_Data.Tv_Let (true ,bv,t1,t2) ->
        let lb =
          FStar_Syntax_Util.mk_letbinding (FStar_Util.Inl bv) []
            bv.FStar_Syntax_Syntax.sort FStar_Parser_Const.effect_Tot_lid t1
            [] FStar_Range.dummyRange
           in
        let uu____83728 = FStar_Syntax_Subst.close_let_rec [lb] t2  in
        (match uu____83728 with
         | (lbs,body) ->
             let uu____83743 =
               FStar_Syntax_Syntax.mk
                 (FStar_Syntax_Syntax.Tm_let ((true, lbs), body))
                 FStar_Pervasives_Native.None FStar_Range.dummyRange
                in
             FStar_All.pipe_left ret uu____83743)
    | FStar_Reflection_Data.Tv_Match (t,brs) ->
        let wrap v1 =
          {
            FStar_Syntax_Syntax.v = v1;
            FStar_Syntax_Syntax.p = FStar_Range.dummyRange
          }  in
        let rec pack_pat p =
          match p with
          | FStar_Reflection_Data.Pat_Constant c ->
              let uu____83780 =
                let uu____83781 = FStar_Reflection_Basic.pack_const c  in
                FStar_Syntax_Syntax.Pat_constant uu____83781  in
              FStar_All.pipe_left wrap uu____83780
          | FStar_Reflection_Data.Pat_Cons (fv,ps) ->
              let uu____83788 =
                let uu____83789 =
                  let uu____83803 =
                    FStar_List.map
                      (fun p1  ->
                         let uu____83821 = pack_pat p1  in
                         (uu____83821, false)) ps
                     in
                  (fv, uu____83803)  in
                FStar_Syntax_Syntax.Pat_cons uu____83789  in
              FStar_All.pipe_left wrap uu____83788
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
            (fun uu___616_83870  ->
               match uu___616_83870 with
               | (pat,t1) ->
                   let uu____83887 = pack_pat pat  in
                   (uu____83887, FStar_Pervasives_Native.None, t1)) brs
           in
        let brs2 = FStar_List.map FStar_Syntax_Subst.close_branch brs1  in
        let uu____83935 =
          FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_match (t, brs2))
            FStar_Pervasives_Native.None FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____83935
    | FStar_Reflection_Data.Tv_AscribedT (e,t,tacopt) ->
        let uu____83963 =
          FStar_Syntax_Syntax.mk
            (FStar_Syntax_Syntax.Tm_ascribed
               (e, ((FStar_Util.Inl t), tacopt),
                 FStar_Pervasives_Native.None)) FStar_Pervasives_Native.None
            FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____83963
    | FStar_Reflection_Data.Tv_AscribedC (e,c,tacopt) ->
        let uu____84009 =
          FStar_Syntax_Syntax.mk
            (FStar_Syntax_Syntax.Tm_ascribed
               (e, ((FStar_Util.Inr c), tacopt),
                 FStar_Pervasives_Native.None)) FStar_Pervasives_Native.None
            FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____84009
    | FStar_Reflection_Data.Tv_Unknown  ->
        let uu____84048 =
          FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown
            FStar_Pervasives_Native.None FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____84048
  
let (lget :
  FStar_Reflection_Data.typ -> Prims.string -> FStar_Syntax_Syntax.term tac)
  =
  fun ty  ->
    fun k  ->
      let uu____84068 =
        bind get
          (fun ps  ->
             let uu____84074 =
               FStar_Util.psmap_try_find ps.FStar_Tactics_Types.local_state k
                in
             match uu____84074 with
             | FStar_Pervasives_Native.None  -> fail "not found"
             | FStar_Pervasives_Native.Some t -> unquote ty t)
         in
      FStar_All.pipe_left (wrap_err "lget") uu____84068
  
let (lset :
  FStar_Reflection_Data.typ ->
    Prims.string -> FStar_Syntax_Syntax.term -> unit tac)
  =
  fun _ty  ->
    fun k  ->
      fun t  ->
        let uu____84108 =
          bind get
            (fun ps  ->
               let ps1 =
                 let uu___2748_84115 = ps  in
                 let uu____84116 =
                   FStar_Util.psmap_add ps.FStar_Tactics_Types.local_state k
                     t
                    in
                 {
                   FStar_Tactics_Types.main_context =
                     (uu___2748_84115.FStar_Tactics_Types.main_context);
                   FStar_Tactics_Types.main_goal =
                     (uu___2748_84115.FStar_Tactics_Types.main_goal);
                   FStar_Tactics_Types.all_implicits =
                     (uu___2748_84115.FStar_Tactics_Types.all_implicits);
                   FStar_Tactics_Types.goals =
                     (uu___2748_84115.FStar_Tactics_Types.goals);
                   FStar_Tactics_Types.smt_goals =
                     (uu___2748_84115.FStar_Tactics_Types.smt_goals);
                   FStar_Tactics_Types.depth =
                     (uu___2748_84115.FStar_Tactics_Types.depth);
                   FStar_Tactics_Types.__dump =
                     (uu___2748_84115.FStar_Tactics_Types.__dump);
                   FStar_Tactics_Types.psc =
                     (uu___2748_84115.FStar_Tactics_Types.psc);
                   FStar_Tactics_Types.entry_range =
                     (uu___2748_84115.FStar_Tactics_Types.entry_range);
                   FStar_Tactics_Types.guard_policy =
                     (uu___2748_84115.FStar_Tactics_Types.guard_policy);
                   FStar_Tactics_Types.freshness =
                     (uu___2748_84115.FStar_Tactics_Types.freshness);
                   FStar_Tactics_Types.tac_verb_dbg =
                     (uu___2748_84115.FStar_Tactics_Types.tac_verb_dbg);
                   FStar_Tactics_Types.local_state = uu____84116
                 }  in
               set ps1)
           in
        FStar_All.pipe_left (wrap_err "lset") uu____84108
  
let (goal_of_goal_ty :
  env ->
    FStar_Reflection_Data.typ ->
      (FStar_Tactics_Types.goal * FStar_TypeChecker_Env.guard_t))
  =
  fun env  ->
    fun typ  ->
      let uu____84143 =
        FStar_TypeChecker_Util.new_implicit_var "proofstate_of_goal_ty"
          typ.FStar_Syntax_Syntax.pos env typ
         in
      match uu____84143 with
      | (u,ctx_uvars,g_u) ->
          let uu____84176 = FStar_List.hd ctx_uvars  in
          (match uu____84176 with
           | (ctx_uvar,uu____84190) ->
               let g =
                 let uu____84192 = FStar_Options.peek ()  in
                 FStar_Tactics_Types.mk_goal env ctx_uvar uu____84192 false
                   ""
                  in
               (g, g_u))
  
let (proofstate_of_goal_ty :
  FStar_Range.range ->
    env ->
      FStar_Reflection_Data.typ ->
        (FStar_Tactics_Types.proofstate * FStar_Syntax_Syntax.term))
  =
  fun rng  ->
    fun env  ->
      fun typ  ->
        let uu____84215 = goal_of_goal_ty env typ  in
        match uu____84215 with
        | (g,g_u) ->
            let ps =
              let uu____84227 =
                FStar_TypeChecker_Env.debug env
                  (FStar_Options.Other "TacVerbose")
                 in
              let uu____84230 = FStar_Util.psmap_empty ()  in
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
                FStar_Tactics_Types.tac_verb_dbg = uu____84227;
                FStar_Tactics_Types.local_state = uu____84230
              }  in
            let uu____84240 = FStar_Tactics_Types.goal_witness g  in
            (ps, uu____84240)
  